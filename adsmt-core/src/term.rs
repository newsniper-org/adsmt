use std::fmt;
use std::ops::Deref;
use std::sync::Arc;

use indexmap::IndexMap;

use crate::error::{KernelError, KernelResult};
use crate::ty::{TyVar, Type};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Var {
    pub name: String,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Const {
    pub name: String,
    pub ty: Type,
}

/// Internal data layout for [`Term`].
///
/// Pattern-match through [`Term::kind`] (or through the
/// [`Deref`] impl which gives `&TermInner`).  The PascalCase
/// associated constructors on [`Term`] mirror these variants so
/// most call sites that say `Term::Var(arc_var)` /
/// `Term::App(f, x)` keep working unchanged.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TermInner {
    Var(Arc<Var>),
    Const(Arc<Const>),
    /// `f x` — `f` is itself a Term (`Arc<TermInner>` under the
    /// hood), so the App variant adds no further indirection.
    App(Term, Term),
    Lam(Arc<Var>, Term),
}

/// A term in HOL+HKT.
///
/// Cloning a `Term` is one `Arc::clone` (a single refcount bump);
/// the term tree itself is structurally shared between clones.
/// Structural `PartialEq` / `Eq` / `Hash` are derived through the
/// underlying [`TermInner`]; α-equivalence is a separate method
/// ([`Term::alpha_eq`]) used by the kernel where appropriate.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Term(pub(crate) Arc<TermInner>);

impl Term {
    /// Return the underlying [`TermInner`] for pattern matching.
    /// Equivalent to dereferencing via [`Deref`] — pick whichever
    /// reads better at the call site.
    #[inline]
    pub fn kind(&self) -> &TermInner {
        &self.0
    }
}

impl Deref for Term {
    type Target = TermInner;
    #[inline]
    fn deref(&self) -> &TermInner {
        &self.0
    }
}

// === Variant-shaped associated constructors ===
//
// These mirror the historical enum-variant shape (`Term::Var(...)`
// etc.) so most construction sites that pre-date the
// `Term(Arc<TermInner>)` refactor keep working without edits.

#[allow(non_snake_case)]
impl Term {
    pub fn Var(v: Arc<Var>) -> Term {
        Term(Arc::new(TermInner::Var(v)))
    }
    pub fn Const(c: Arc<Const>) -> Term {
        Term(Arc::new(TermInner::Const(c)))
    }
    pub fn App(f: Term, x: Term) -> Term {
        Term(Arc::new(TermInner::App(f, x)))
    }
    pub fn Lam(v: Arc<Var>, body: Term) -> Term {
        Term(Arc::new(TermInner::Lam(v, body)))
    }
}

impl Term {
    pub fn var(name: &str, ty: Type) -> Term {
        Term::Var(Arc::new(Var { name: name.into(), ty }))
    }

    pub fn const_(name: &str, ty: Type) -> Term {
        Term::Const(Arc::new(Const { name: name.into(), ty }))
    }

    pub fn app(f: Term, x: Term) -> KernelResult<Term> {
        let ft = f.type_of();
        let xt = x.type_of();
        match ft.dest_fun() {
            Some((dom, _)) if dom == xt => Ok(Term::App(f, x)),
            Some((dom, _)) => Err(KernelError::TypeMismatch {
                expected: dom.to_string(),
                found: xt.to_string(),
            }),
            None => Err(KernelError::NotFunctionType(ft.to_string())),
        }
    }

    pub fn lam(v: Var, body: Term) -> Term {
        Term::Lam(Arc::new(v), body)
    }

    pub fn type_of(&self) -> Type {
        match self.kind() {
            TermInner::Var(v) => v.ty.clone(),
            TermInner::Const(c) => c.ty.clone(),
            TermInner::App(f, _) => f
                .type_of()
                .dest_fun()
                .expect("ill-typed App slipped past Term::app()")
                .1,
            TermInner::Lam(v, body) => Type::fun(v.ty.clone(), body.type_of())
                .expect("kinds match by construction"),
        }
    }

    /// Free term variables in left-to-right order.
    pub fn free_vars(&self) -> Vec<Arc<Var>> {
        let mut bound = Vec::new();
        let mut free = Vec::new();
        self.collect_free(&mut bound, &mut free);
        free
    }

    fn collect_free(&self, bound: &mut Vec<Arc<Var>>, free: &mut Vec<Arc<Var>>) {
        match self.kind() {
            TermInner::Var(v) => {
                if !bound.iter().any(|b| **b == **v) && !free.iter().any(|f| **f == **v) {
                    free.push(v.clone());
                }
            }
            TermInner::Const(_) => {}
            TermInner::App(f, x) => {
                f.collect_free(bound, free);
                x.collect_free(bound, free);
            }
            TermInner::Lam(v, body) => {
                bound.push(v.clone());
                body.collect_free(bound, free);
                bound.pop();
            }
        }
    }

    /// Free *type* variables appearing anywhere in this term.
    pub fn free_type_vars(&self) -> Vec<Arc<TyVar>> {
        let mut out = Vec::new();
        self.collect_free_tyvars(&mut out);
        out
    }

    fn collect_free_tyvars(&self, out: &mut Vec<Arc<TyVar>>) {
        match self.kind() {
            TermInner::Var(v) => extend_tyvars(out, &v.ty.free_vars()),
            TermInner::Const(c) => extend_tyvars(out, &c.ty.free_vars()),
            TermInner::App(f, x) => {
                f.collect_free_tyvars(out);
                x.collect_free_tyvars(out);
            }
            TermInner::Lam(v, body) => {
                extend_tyvars(out, &v.ty.free_vars());
                body.collect_free_tyvars(out);
            }
        }
    }

    /// α-equivalence: structural equality up to renaming of bound variables.
    pub fn alpha_eq(&self, other: &Term) -> bool {
        alpha_eq_rec(self, other, &mut Vec::new(), &mut Vec::new())
    }

    /// Capture-avoiding term substitution.
    pub fn subst(&self, sigma: &IndexMap<Arc<Var>, Term>) -> KernelResult<Term> {
        if sigma.is_empty() {
            return Ok(self.clone());
        }
        // Type-check the substitution
        for (v, t) in sigma {
            if t.type_of() != v.ty {
                return Err(KernelError::TypeMismatch {
                    expected: v.ty.to_string(),
                    found: t.type_of().to_string(),
                });
            }
        }
        // Avoid set: free vars of every substitution image, plus the
        // domain of sigma itself (so that re-binding stays safe).
        let mut avoid: Vec<Arc<Var>> = Vec::new();
        for img in sigma.values() {
            for fv in img.free_vars() {
                if !avoid.iter().any(|a| **a == *fv) {
                    avoid.push(fv);
                }
            }
        }
        self.subst_rec(sigma, &avoid)
    }

    fn subst_rec(
        &self,
        sigma: &IndexMap<Arc<Var>, Term>,
        avoid: &[Arc<Var>],
    ) -> KernelResult<Term> {
        match self.kind() {
            TermInner::Var(v) => Ok(sigma.get(v).cloned().unwrap_or_else(|| self.clone())),
            TermInner::Const(_) => Ok(self.clone()),
            TermInner::App(f, x) => {
                let f2 = f.subst_rec(sigma, avoid)?;
                let x2 = x.subst_rec(sigma, avoid)?;
                Ok(Term::App(f2, x2))
            }
            TermInner::Lam(v, body) => {
                // Shadow: drop v from sigma inside the binder.
                let restricted: IndexMap<Arc<Var>, Term> = sigma
                    .iter()
                    .filter(|(k, _)| **k != *v)
                    .map(|(k, t)| (k.clone(), t.clone()))
                    .collect();

                if restricted.is_empty() {
                    return Ok(self.clone());
                }

                // Capture would occur if any free var of restricted's
                // range equals (name + type) the bound `v`.
                let must_rename = restricted
                    .values()
                    .any(|t| t.free_vars().iter().any(|fv| **fv == **v));

                if must_rename {
                    let body_free = body.free_vars();
                    let fresh = Arc::new(Var {
                        name: fresh_name(&v.name, avoid, &body_free),
                        ty: v.ty.clone(),
                    });
                    let mut rename = IndexMap::new();
                    rename.insert(v.clone(), Term::Var(fresh.clone()));
                    let body_renamed = body.subst_rec(&rename, &[])?;
                    let body_done = body_renamed.subst_rec(&restricted, avoid)?;
                    return Ok(Term::Lam(fresh, body_done));
                }

                let body_done = body.subst_rec(&restricted, avoid)?;
                Ok(Term::Lam(v.clone(), body_done))
            }
        }
    }

    /// Apply a type substitution everywhere in the term.
    pub fn type_subst(&self, sigma: &IndexMap<Arc<TyVar>, Type>) -> Term {
        if sigma.is_empty() {
            return self.clone();
        }
        match self.kind() {
            TermInner::Var(v) => Term::Var(Arc::new(Var {
                name: v.name.clone(),
                ty: v.ty.subst(sigma),
            })),
            TermInner::Const(c) => Term::Const(Arc::new(Const {
                name: c.name.clone(),
                ty: c.ty.subst(sigma),
            })),
            TermInner::App(f, x) => Term::App(f.type_subst(sigma), x.type_subst(sigma)),
            TermInner::Lam(v, body) => {
                let new_v = Arc::new(Var {
                    name: v.name.clone(),
                    ty: v.ty.subst(sigma),
                });
                Term::Lam(new_v, body.type_subst(sigma))
            }
        }
    }

    /// β-reduce a redex `(λx. body) arg` to `body[x ↦ arg]`.
    pub fn beta_reduce(&self) -> KernelResult<Term> {
        if let TermInner::App(f, arg) = self.kind()
            && let TermInner::Lam(v, body) = f.kind()
        {
            let mut sigma = IndexMap::new();
            sigma.insert(v.clone(), arg.clone());
            return body.subst(&sigma);
        }
        Err(KernelError::NotBetaRedex(self.to_string()))
    }

    /// Built-in equality `=` instantiated at `ty`: `ty -> ty -> Bool`.
    pub fn eq_const(ty: Type) -> KernelResult<Term> {
        let cod = Type::fun(ty.clone(), Type::bool_())?;
        let eq_ty = Type::fun(ty, cod)?;
        Ok(Term::const_("=", eq_ty))
    }

    /// Build the equation `lhs = rhs`.
    pub fn mk_eq(lhs: Term, rhs: Term) -> KernelResult<Term> {
        let lty = lhs.type_of();
        let rty = rhs.type_of();
        if lty != rty {
            return Err(KernelError::TypeMismatch {
                expected: lty.to_string(),
                found: rty.to_string(),
            });
        }
        let eq = Self::eq_const(lty)?;
        Term::app(Term::app(eq, lhs)?, rhs)
    }

    /// Destruct an equation `lhs = rhs`.
    pub fn dest_eq(&self) -> Option<(Term, Term)> {
        if let TermInner::App(outer, rhs) = self.kind()
            && let TermInner::App(eq, lhs) = outer.kind()
            && let TermInner::Const(c) = eq.kind()
            && c.name == "="
        {
            return Some((lhs.clone(), rhs.clone()));
        }
        None
    }

    /// Build `p ↔ q`, i.e. an equation between booleans.
    pub fn mk_iff(p: Term, q: Term) -> KernelResult<Term> {
        if p.type_of() != Type::bool_() {
            return Err(KernelError::TypeMismatch {
                expected: "Bool".into(),
                found: p.type_of().to_string(),
            });
        }
        Term::mk_eq(p, q)
    }

    /// Destruct `p ↔ q` (equation at type Bool).
    pub fn dest_iff(&self) -> Option<(Term, Term)> {
        let (l, r) = self.dest_eq()?;
        if l.type_of() == Type::bool_() {
            Some((l, r))
        } else {
            None
        }
    }

    // === Boolean built-ins (v0.3) ===
    //
    // These are kernel-recognized symbols whose semantics is honoured
    // by the engine. They aren't yet *defined* in the kernel sense
    // (no axioms relating `not p` to falsehood, etc.) — definitional
    // theorems land when the engine grows a proof-producing path.

    /// Built-in `true : Bool`.
    pub fn true_const() -> Term {
        Term::const_("true", Type::bool_())
    }

    /// Built-in `false : Bool`.
    pub fn false_const() -> Term {
        Term::const_("false", Type::bool_())
    }

    /// Built-in `not : Bool -> Bool`.
    pub fn not_const() -> Term {
        Term::const_(
            "not",
            Type::fun(Type::bool_(), Type::bool_()).expect("Bool kinds"),
        )
    }

    fn bool_binop(name: &str) -> Term {
        let bb = Type::fun(Type::bool_(), Type::bool_()).expect("Bool kinds");
        let ty = Type::fun(Type::bool_(), bb).expect("Bool kinds");
        Term::const_(name, ty)
    }

    /// Built-in `and : Bool -> Bool -> Bool`.
    pub fn and_const() -> Term { Self::bool_binop("and") }

    /// Built-in `or : Bool -> Bool -> Bool`.
    pub fn or_const() -> Term { Self::bool_binop("or") }

    /// Built-in `=> : Bool -> Bool -> Bool` (implication).
    pub fn imp_const() -> Term { Self::bool_binop("=>") }

    fn require_bool(t: &Term) -> KernelResult<()> {
        if t.type_of() != Type::bool_() {
            return Err(KernelError::TypeMismatch {
                expected: "Bool".into(),
                found: t.type_of().to_string(),
            });
        }
        Ok(())
    }

    pub fn mk_not(p: Term) -> KernelResult<Term> {
        Self::require_bool(&p)?;
        Term::app(Term::not_const(), p)
    }

    pub fn mk_and(p: Term, q: Term) -> KernelResult<Term> {
        Self::require_bool(&p)?;
        Self::require_bool(&q)?;
        Term::app(Term::app(Term::and_const(), p)?, q)
    }

    pub fn mk_or(p: Term, q: Term) -> KernelResult<Term> {
        Self::require_bool(&p)?;
        Self::require_bool(&q)?;
        Term::app(Term::app(Term::or_const(), p)?, q)
    }

    pub fn mk_imp(p: Term, q: Term) -> KernelResult<Term> {
        Self::require_bool(&p)?;
        Self::require_bool(&q)?;
        Term::app(Term::app(Term::imp_const(), p)?, q)
    }

    /// Decompose `not P` returning `P`.
    pub fn dest_not(&self) -> Option<Term> {
        if let TermInner::App(f, p) = self.kind()
            && let TermInner::Const(c) = f.kind()
            && c.name == "not"
        {
            return Some(p.clone());
        }
        None
    }

    fn dest_bool_binop(name: &str, t: &Term) -> Option<(Term, Term)> {
        if let TermInner::App(outer, q) = t.kind()
            && let TermInner::App(head, p) = outer.kind()
            && let TermInner::Const(c) = head.kind()
            && c.name == name
        {
            return Some((p.clone(), q.clone()));
        }
        None
    }

    pub fn dest_and(&self) -> Option<(Term, Term)> { Self::dest_bool_binop("and", self) }
    pub fn dest_or(&self) -> Option<(Term, Term)> { Self::dest_bool_binop("or", self) }
    pub fn dest_imp(&self) -> Option<(Term, Term)> { Self::dest_bool_binop("=>", self) }

    pub fn is_true_const(&self) -> bool {
        matches!(self.kind(), TermInner::Const(c) if c.name == "true")
    }

    pub fn is_false_const(&self) -> bool {
        matches!(self.kind(), TermInner::Const(c) if c.name == "false")
    }

    // === Quantifier built-ins (v0.3 quantifier handling) ===

    /// Built-in `forall : (α -> Bool) -> Bool`, monomorphized at `arg_ty`.
    pub fn forall_const(arg_ty: Type) -> KernelResult<Term> {
        let pred_ty = Type::fun(arg_ty, Type::bool_())?;
        let forall_ty = Type::fun(pred_ty, Type::bool_())?;
        Ok(Term::const_("forall", forall_ty))
    }

    /// Built-in `exists : (α -> Bool) -> Bool`, monomorphized at `arg_ty`.
    pub fn exists_const(arg_ty: Type) -> KernelResult<Term> {
        let pred_ty = Type::fun(arg_ty, Type::bool_())?;
        let exists_ty = Type::fun(pred_ty, Type::bool_())?;
        Ok(Term::const_("exists", exists_ty))
    }

    /// Build `∀v. body` from a bound variable and a Bool body.
    pub fn mk_forall(v: Var, body: Term) -> KernelResult<Term> {
        Self::require_bool(&body)?;
        let arg_ty = v.ty.clone();
        let lam = Term::lam(v, body);
        Term::app(Term::forall_const(arg_ty)?, lam)
    }

    /// Build `∃v. body` from a bound variable and a Bool body.
    pub fn mk_exists(v: Var, body: Term) -> KernelResult<Term> {
        Self::require_bool(&body)?;
        let arg_ty = v.ty.clone();
        let lam = Term::lam(v, body);
        Term::app(Term::exists_const(arg_ty)?, lam)
    }

    // === Bit-vector built-ins (v0.5) ===
    //
    // BV sorts are encoded as `BV<width>` type constants. Literal
    // values are encoded as Const terms named `bv:value:width`,
    // which is parseable both ways. v0.5 keeps this representation
    // string-based; v0.7 may switch to a structured payload.

    /// `(_ BitVec width)` sort name → `Type::const_("BV<width>", Type)`.
    pub fn bv_sort(width: u32) -> Type {
        Type::const_(&format!("BV<{width}>"), crate::kind::Kind::Type)
    }

    /// Build the literal Const term `bv:value:width` at sort `BV<width>`.
    pub fn bv_lit(value: u128, width: u32) -> Term {
        Term::const_(&format!("bv:{value}:{width}"), Self::bv_sort(width))
    }

    /// If `t` is a BV literal, return `(value, width)`.
    pub fn dest_bv_lit(&self) -> Option<(u128, u32)> {
        if let TermInner::Const(c) = self.kind()
            && let Some(rest) = c.name.strip_prefix("bv:")
        {
            let mut parts = rest.splitn(2, ':');
            let v = parts.next()?.parse::<u128>().ok()?;
            let w = parts.next()?.parse::<u32>().ok()?;
            return Some((v, w));
        }
        None
    }

    /// Build a BV binary-op constant (`bvand`/`bvor`/`bvxor`/`bvadd`/
    /// `bvsub`/`bvmul`/`bvshl`/`bvshr`) at `width`.
    fn bv_binop_const(name: &str, width: u32) -> Term {
        let bv = Self::bv_sort(width);
        let ty = Type::fun(bv.clone(), Type::fun(bv.clone(), bv).unwrap()).unwrap();
        Term::const_(&format!("{name}_{width}"), ty)
    }

    pub fn mk_bvand(lhs: Term, rhs: Term, width: u32) -> KernelResult<Term> {
        Term::app(Term::app(Self::bv_binop_const("bvand", width), lhs)?, rhs)
    }
    pub fn mk_bvor(lhs: Term, rhs: Term, width: u32) -> KernelResult<Term> {
        Term::app(Term::app(Self::bv_binop_const("bvor", width), lhs)?, rhs)
    }
    pub fn mk_bvxor(lhs: Term, rhs: Term, width: u32) -> KernelResult<Term> {
        Term::app(Term::app(Self::bv_binop_const("bvxor", width), lhs)?, rhs)
    }
    pub fn mk_bvadd(lhs: Term, rhs: Term, width: u32) -> KernelResult<Term> {
        Term::app(Term::app(Self::bv_binop_const("bvadd", width), lhs)?, rhs)
    }
    /// v0.21 C.1 — symmetric to `mk_bvadd`. `Bv::reduce_binop`
    /// already evaluates the all-literal case, and the
    /// `bv_blast` ripple-carry-subtractor handles the mixed case.
    pub fn mk_bvsub(lhs: Term, rhs: Term, width: u32) -> KernelResult<Term> {
        Term::app(Term::app(Self::bv_binop_const("bvsub", width), lhs)?, rhs)
    }
    /// v0.21 C.1 — currently no bit-blaster (shift-and-add waits
    /// for v0.23); `Bv::reduce_binop` handles the all-literal
    /// case eagerly.
    pub fn mk_bvmul(lhs: Term, rhs: Term, width: u32) -> KernelResult<Term> {
        Term::app(Term::app(Self::bv_binop_const("bvmul", width), lhs)?, rhs)
    }

    /// v0.23 C.1 — unary BV NOT (bitwise complement). Returns
    /// `(bvnot_<width> arg)`. Eager constant folding lives in
    /// `Bv::reduce_unop`; bit-blast wiring in
    /// `adsmt-engine::bv_blast::blast_term`.
    pub fn mk_bvnot(arg: Term, width: u32) -> KernelResult<Term> {
        let bv = Self::bv_sort(width);
        let ty = Type::fun(bv.clone(), bv).unwrap();
        let head = Term::const_(&format!("bvnot_{width}"), ty);
        Term::app(head, arg)
    }

    /// v0.23 C.1 — unary BV negation (two's complement).
    /// `(bvneg x) ≡ (bvadd (bvnot x) 0x1)`. Returns
    /// `(bvneg_<width> arg)`; bit-blast lowering reuses the
    /// existing ripple-carry adder under the bvnot/bvneg
    /// composition.
    pub fn mk_bvneg(arg: Term, width: u32) -> KernelResult<Term> {
        let bv = Self::bv_sort(width);
        let ty = Type::fun(bv.clone(), bv).unwrap();
        let head = Term::const_(&format!("bvneg_{width}"), ty);
        Term::app(head, arg)
    }

    /// Destructure a BV unary op `(<op>_w arg)` returning
    /// `(op, width, arg)`. Recognises `bvnot` and `bvneg`.
    pub fn dest_bv_unop(&self) -> Option<(String, u32, Term)> {
        if let TermInner::App(head, arg) = self.kind()
            && let TermInner::Const(c) = head.kind()
        {
            let nm = &c.name;
            for op in ["bvnot", "bvneg"] {
                if let Some(rest) = nm.strip_prefix(&format!("{op}_"))
                    && let Ok(w) = rest.parse::<u32>()
                {
                    return Some((op.into(), w, arg.clone()));
                }
            }
        }
        None
    }

    /// Destructure a BV binop `(<op>_w lhs rhs)` returning `(op, width, lhs, rhs)`.
    pub fn dest_bv_binop(&self) -> Option<(String, u32, Term, Term)> {
        if let TermInner::App(outer, rhs) = self.kind()
            && let TermInner::App(head, lhs) = outer.kind()
            && let TermInner::Const(c) = head.kind()
        {
            let nm = &c.name;
            for op in ["bvand", "bvor", "bvxor", "bvadd", "bvsub", "bvmul"] {
                if let Some(rest) = nm.strip_prefix(&format!("{op}_"))
                    && let Ok(w) = rest.parse::<u32>()
                {
                    return Some((op.into(), w, lhs.clone(), rhs.clone()));
                }
            }
        }
        None
    }

    /// Extract the bit-vector width from a `BV<n>` sort, if applicable.
    pub fn bv_sort_width(ty: &Type) -> Option<u32> {
        if let Type::Const(c) = ty
            && let Some(rest) = c.name.strip_prefix("BV<")
            && let Some(num) = rest.strip_suffix('>')
        {
            return num.parse::<u32>().ok();
        }
        None
    }

    /// Destructure `∀v. body`, returning the binder and body.
    pub fn dest_forall(&self) -> Option<(Var, Term)> {
        if let TermInner::App(f, lam) = self.kind()
            && let TermInner::Const(c) = f.kind()
            && c.name == "forall"
            && let TermInner::Lam(v, body) = lam.kind()
        {
            return Some(((**v).clone(), body.clone()));
        }
        None
    }

    /// Destructure `∃v. body`, returning the binder and body.
    pub fn dest_exists(&self) -> Option<(Var, Term)> {
        if let TermInner::App(f, lam) = self.kind()
            && let TermInner::Const(c) = f.kind()
            && c.name == "exists"
            && let TermInner::Lam(v, body) = lam.kind()
        {
            return Some(((**v).clone(), body.clone()));
        }
        None
    }
}

fn extend_tyvars(dst: &mut Vec<Arc<TyVar>>, src: &[Arc<TyVar>]) {
    for v in src {
        if !dst.iter().any(|d| **d == **v) {
            dst.push(v.clone());
        }
    }
}

fn alpha_eq_rec(
    a: &Term,
    b: &Term,
    a_bound: &mut Vec<Arc<Var>>,
    b_bound: &mut Vec<Arc<Var>>,
) -> bool {
    match (a.kind(), b.kind()) {
        (TermInner::Var(va), TermInner::Var(vb)) => {
            let pos_a = a_bound.iter().rposition(|v| **v == **va);
            let pos_b = b_bound.iter().rposition(|v| **v == **vb);
            match (pos_a, pos_b) {
                (Some(i), Some(j)) => {
                    let depth_a = a_bound.len() - 1 - i;
                    let depth_b = b_bound.len() - 1 - j;
                    depth_a == depth_b && va.ty == vb.ty
                }
                (None, None) => **va == **vb,
                _ => false,
            }
        }
        (TermInner::Const(ca), TermInner::Const(cb)) => **ca == **cb,
        (TermInner::App(fa, xa), TermInner::App(fb, xb)) => {
            alpha_eq_rec(fa, fb, a_bound, b_bound)
                && alpha_eq_rec(xa, xb, a_bound, b_bound)
        }
        (TermInner::Lam(va, ba), TermInner::Lam(vb, bb)) => {
            if va.ty != vb.ty {
                return false;
            }
            a_bound.push(va.clone());
            b_bound.push(vb.clone());
            let r = alpha_eq_rec(ba, bb, a_bound, b_bound);
            a_bound.pop();
            b_bound.pop();
            r
        }
        _ => false,
    }
}

fn fresh_name(base: &str, avoid1: &[Arc<Var>], avoid2: &[Arc<Var>]) -> String {
    let mut n = 0usize;
    loop {
        let candidate = format!("{base}'{n}");
        let clash = avoid1.iter().any(|v| v.name == candidate)
            || avoid2.iter().any(|v| v.name == candidate);
        if !clash {
            return candidate;
        }
        n += 1;
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((lhs, rhs)) = self.dest_eq() {
            return write!(f, "({lhs} = {rhs})");
        }
        match self.kind() {
            TermInner::Var(v) => write!(f, "{}", v.name),
            TermInner::Const(c) => write!(f, "{}", c.name),
            TermInner::App(g, x) => {
                if matches!(g.kind(), TermInner::Lam(..)) {
                    write!(f, "({g})")?;
                } else {
                    write!(f, "{g}")?;
                }
                write!(f, " ")?;
                if matches!(x.kind(), TermInner::App(..) | TermInner::Lam(..)) {
                    write!(f, "({x})")
                } else {
                    write!(f, "{x}")
                }
            }
            TermInner::Lam(v, body) => write!(f, "λ{}:{}. {body}", v.name, v.ty),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kind::Kind;

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    #[test]
    fn variable_type() {
        let x = Term::var("x", int_());
        assert_eq!(x.type_of(), int_());
    }

    #[test]
    fn constant_type() {
        let one = Term::const_("1", int_());
        assert_eq!(one.type_of(), int_());
    }

    #[test]
    fn ill_typed_app_rejected() {
        let f = Term::var("f", Type::fun(int_(), int_()).unwrap());
        let b = Term::var("b", Type::bool_());
        let r = Term::app(f, b);
        assert!(r.is_err());
    }

    #[test]
    fn well_typed_app_succeeds() {
        let f = Term::var("f", Type::fun(int_(), int_()).unwrap());
        let x = Term::var("x", int_());
        let fx = Term::app(f, x).unwrap();
        assert_eq!(fx.type_of(), int_());
    }

    #[test]
    fn lambda_type_is_arrow() {
        let x = Var { name: "x".into(), ty: int_() };
        let body = Term::var("body", int_());
        let lam = Term::lam(x, body);
        assert_eq!(lam.type_of(), Type::fun(int_(), int_()).unwrap());
    }

    #[test]
    fn alpha_eq_lambdas_renames_bound() {
        let x = Var { name: "x".into(), ty: int_() };
        let y = Var { name: "y".into(), ty: int_() };
        let body_x = Term::Var(Arc::new(x.clone()));
        let body_y = Term::Var(Arc::new(y.clone()));
        let lam_x = Term::lam(x, body_x);
        let lam_y = Term::lam(y, body_y);
        assert!(lam_x.alpha_eq(&lam_y));
    }

    #[test]
    fn alpha_eq_distinct_constants_no_match() {
        let x = Var { name: "x".into(), ty: int_() };
        let y = Var { name: "y".into(), ty: int_() };
        let body_x = Term::var("z", int_());
        let body_y = Term::var("w", int_());
        let lam_x = Term::lam(x, body_x);
        let lam_y = Term::lam(y, body_y);
        assert!(!lam_x.alpha_eq(&lam_y));
    }

    #[test]
    fn subst_substitutes_variable() {
        let x = Arc::new(Var { name: "x".into(), ty: int_() });
        let y = Term::var("y", int_());
        let mut sigma = IndexMap::new();
        sigma.insert(x.clone(), y.clone());
        let result = Term::Var(x).subst(&sigma).unwrap();
        assert_eq!(result, y);
    }

    #[test]
    fn subst_into_lambda_capture_avoiding() {
        // λy. x  with  σ = {x ↦ y}  must rename the binder.
        let y = Arc::new(Var { name: "y".into(), ty: int_() });
        let x = Arc::new(Var { name: "x".into(), ty: int_() });
        let body = Term::Var(x.clone());
        let lam = Term::Lam(y.clone(), body);
        let mut sigma = IndexMap::new();
        sigma.insert(x.clone(), Term::Var(y.clone()));
        let result = lam.subst(&sigma).unwrap();
        // The bound name should NOT be `y` any more.
        if let TermInner::Lam(v, _) = result.kind() {
            assert_ne!(v.name, "y", "binder was not renamed");
        } else {
            panic!("expected Lam result");
        }
    }

    #[test]
    fn beta_reduces_redex() {
        let x = Arc::new(Var { name: "x".into(), ty: int_() });
        let body = Term::Var(x.clone());
        let lam = Term::Lam(x.clone(), body);
        let arg = Term::var("a", int_());
        let redex = Term::app(lam, arg.clone()).unwrap();
        let r = redex.beta_reduce().unwrap();
        assert_eq!(r, arg);
    }

    #[test]
    fn eq_term_well_typed() {
        let x = Term::var("x", int_());
        let y = Term::var("y", int_());
        let eq = Term::mk_eq(x, y).unwrap();
        assert_eq!(eq.type_of(), Type::bool_());
    }

    #[test]
    fn eq_term_round_trips() {
        let x = Term::var("x", int_());
        let y = Term::var("y", int_());
        let eq = Term::mk_eq(x.clone(), y.clone()).unwrap();
        let (l, r) = eq.dest_eq().unwrap();
        assert!(l.alpha_eq(&x));
        assert!(r.alpha_eq(&y));
    }

    #[test]
    fn boolean_builtins_well_typed_and_roundtrip() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let n = Term::mk_not(p.clone()).unwrap();
        assert_eq!(n.type_of(), Type::bool_());
        assert_eq!(n.dest_not().unwrap(), p);

        let conj = Term::mk_and(p.clone(), q.clone()).unwrap();
        let (l, r) = conj.dest_and().unwrap();
        assert_eq!(l, p);
        assert_eq!(r, q);

        let disj = Term::mk_or(p.clone(), q.clone()).unwrap();
        assert!(disj.dest_and().is_none());
        assert!(disj.dest_or().is_some());

        let imp = Term::mk_imp(p.clone(), q.clone()).unwrap();
        let (l, r) = imp.dest_imp().unwrap();
        assert_eq!(l, p);
        assert_eq!(r, q);
    }

    #[test]
    fn boolean_builtins_reject_non_bool() {
        let x = Term::var("x", int_());
        let p = Term::var("p", Type::bool_());
        assert!(Term::mk_not(x.clone()).is_err());
        assert!(Term::mk_and(x.clone(), p.clone()).is_err());
        assert!(Term::mk_and(p.clone(), x).is_err());
    }
}
