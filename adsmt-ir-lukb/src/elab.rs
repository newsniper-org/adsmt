//! Elaborate a parsed lu-kb-successor [`Module`] into a **kernel-checked**
//! [`Env`] + the obligation/hypothesis term lists. Every elaborated term is
//! re-checked by the adsmt-ir kernel (each `axiom`/`assume`/`goal` body must be
//! a closed `Prop`), so a face bug can only ever yield a [`FaceError`], never a
//! trusted ill-typed term — the same firewall as the SMT-LIB / ASP faces.

use adsmt_ir::theory;
use adsmt_ir::{
    Ctx, Env, Term as K, Univ, declare_inductive, define, infer, is_def_eq, postulate, subst_top,
};

use crate::ast::{BinOp, Binder, Item, Module, Term as S, Type};
use crate::error::{FaceError, unsupported};
use crate::parser::parse;

/// The result of elaborating a lu-kb-successor module: the checked environment,
/// the hypotheses `H` (from `axiom` + `assume`), and the obligations (from
/// `goal`). Each term is a closed, kernel-checked `Prop`. The entailment to
/// discharge is `H ⊨ goal` for each goal.
pub struct Elaborated {
    pub env: Env,
    /// `axiom` + `assume` bodies (the assumption set `H`).
    pub hypotheses: Vec<K>,
    /// `goal` bodies (the obligations, each to be checked under `H`).
    pub goals: Vec<K>,
}

/// Parse + elaborate lu-kb-successor source.
pub fn elaborate(src: &str) -> Result<Elaborated, FaceError> {
    let module: Module = parse(src)?;
    let mut e = Elab::new()?;
    for item in &module.items {
        e.item(item)?;
    }
    Ok(Elaborated { env: e.env, hypotheses: e.hyps, goals: e.goals })
}

struct Elab {
    env: Env,
    hyps: Vec<K>,
    goals: Vec<K>,
}

impl Elab {
    fn new() -> Result<Self, FaceError> {
        let mut env = Env::new();
        // the logical prelude (Bool = Prop; connectives; polymorphic Eq /
        // Exists / ite), all `open` — mirrors the SMT-LIB face.
        let prop = K::prop();
        let pp = || K::arrow(K::prop(), K::prop());
        postulate(&mut env, "true", prop.clone())?;
        postulate(&mut env, "false", prop.clone())?;
        postulate(&mut env, "not", pp())?;
        postulate(&mut env, "and", K::arrow(K::prop(), pp()))?;
        postulate(&mut env, "or", K::arrow(K::prop(), pp()))?;
        let eq_ty =
            K::pi(K::type_(0), K::arrow(K::bound(0), K::arrow(K::bound(0), K::prop())));
        postulate(&mut env, "=", eq_ty)?;
        let ex_ty =
            K::pi(K::type_(0), K::arrow(K::arrow(K::bound(0), K::prop()), K::prop()));
        postulate(&mut env, "exists", ex_ty)?;
        // the FULL arithmetic prelude (Int/Real/Nat/WNat + ops + injections +
        // pow/odd/prime) — the lu-kb surface uses Nat/WNat/pow/… as built-ins.
        theory::install_arith(&mut env)?;
        Ok(Elab { env, hyps: Vec::new(), goals: Vec::new() })
    }

    fn item(&mut self, item: &Item) -> Result<(), FaceError> {
        match item {
            Item::Sort(s) => {
                postulate(&mut self.env, s, K::type_(0))?;
            }
            Item::Const(x, ty) => {
                // a refinement-typed constant `const c: {v: T | φ}` postulates
                // `c : T` PLUS the trusted fact `φ[v := c]` as a top-level
                // hypothesis. Dropping it would be unsound: an arbitrary `T`
                // value could violate `φ`, admitting a spurious model (the same
                // reason the Nat/WNat collapse re-asserts free-const positivity).
                if let Type::Refine { var, base, pred } = ty {
                    let kbase = self.elab_type(base)?;
                    postulate(&mut self.env, x, kbase.clone())?;
                    let phi = self.refine_pred_at(var, &kbase, pred, &K::cnst(x.clone()))?;
                    self.hyps.push(phi);
                } else {
                    let kty = self.elab_type(ty)?;
                    postulate(&mut self.env, x, kty)?;
                }
            }
            Item::Fn { name, params, ret, body } => {
                // build the curried function type `T1 -> … -> ret` + the flat
                // (param-name, type) list in order.
                let mut ptypes: Vec<K> = Vec::new();
                let mut pnames: Vec<String> = Vec::new();
                for (names, t) in params {
                    let kt = self.elab_type(t)?;
                    for n in names {
                        ptypes.push(kt.clone());
                        pnames.push(n.clone());
                    }
                }
                let mut ty = self.elab_type(ret)?;
                for pt in ptypes.iter().rev() {
                    ty = K::arrow(pt.clone(), ty);
                }
                match body {
                    // a signature: an opaque (`open`) function constant.
                    None => {
                        postulate(&mut self.env, name, ty)?;
                    }
                    // a definition `f := λ(params). body`. Elaborate the body
                    // under the param binders, λ-abstract, and `define` it (a
                    // `Modality::Def`, δ-unfolded at the solver lowering). The
                    // body must NOT mention `f` — a recursive body needs the
                    // kernel `fix` (a later slice; here it elaborates to an
                    // "unknown symbol `f`" error, which is sound).
                    Some(b) => {
                        let mut ctx: Vec<(String, K)> =
                            pnames.into_iter().zip(ptypes.iter().cloned()).collect();
                        let kbody = self.elab_term(&mut ctx, b)?;
                        let mut lam = kbody;
                        for pt in ptypes.into_iter().rev() {
                            lam = K::lam(pt, lam);
                        }
                        define(&mut self.env, name, ty, lam)?;
                    }
                }
            }
            Item::Data { name, ctors } => {
                // a non-parametric inductive datatype → `declare_inductive`. A
                // field type may reference THIS datatype (recursive) — it is not
                // in `env` yet, so the self-reference resolves to `cnst(name)`.
                // Selector names are surface-only (the solver lowering
                // synthesizes positional selectors).
                let mut kctors: Vec<(String, Vec<K>)> = Vec::with_capacity(ctors.len());
                for (cname, fields) in ctors {
                    let mut ftypes = Vec::with_capacity(fields.len());
                    for (_selname, fty) in fields {
                        ftypes.push(self.elab_field_type(fty, name)?);
                    }
                    kctors.push((cname.clone(), ftypes));
                }
                declare_inductive(&mut self.env, name, Vec::new(), Univ::Type(0), kctors)?;
            }
            Item::Axiom(_, t) | Item::Assume(_, t) => {
                let kt = self.elab_prop(t)?;
                self.hyps.push(kt);
            }
            Item::Goal(_, t) => {
                let kt = self.elab_prop(t)?;
                self.goals.push(kt);
            }
        }
        Ok(())
    }

    /// Elaborate a term and **check it is a closed `Prop`** (the kernel gate).
    fn elab_prop(&mut self, t: &S) -> Result<K, FaceError> {
        let mut ctx: Vec<(String, K)> = Vec::new();
        let kt = self.elab_term(&mut ctx, t)?;
        let ty = infer(&self.env, &Ctx::new(), &kt)?;
        if !is_def_eq(&self.env, &ty, &K::prop()) {
            return Err(unsupported(format!("item body has sort `{ty}`, expected Bool/Prop")));
        }
        Ok(kt)
    }

    /// A datatype constructor's **field type**, as [`Self::elab_type`] but with
    /// the inductive being declared (`data_name`) allowed as a (recursive)
    /// self-reference even though it is not yet in `env`.
    fn elab_field_type(&self, ty: &Type, data_name: &str) -> Result<K, FaceError> {
        match ty {
            Type::Name(n) if n == data_name => Ok(K::cnst(n.clone())),
            _ => self.elab_type(ty),
        }
    }

    fn elab_type(&self, ty: &Type) -> Result<K, FaceError> {
        match ty {
            Type::Name(n) if n == "Bool" => Ok(K::prop()),
            Type::Name(n) => match self.env.lookup(n) {
                Some(d) if is_type0(&d.ty) => Ok(K::cnst(n.clone())),
                Some(_) => Err(unsupported(format!("`{n}` is not a sort"))),
                None => Err(unsupported(format!("unknown sort `{n}`"))),
            },
            Type::App(n, _) => {
                Err(unsupported(format!("parametric sort `{n}(…)` is a later slice")))
            }
            // a refinement `{v: T | φ}`'s *sort* is just its base `T` (the proof
            // of `φ` is `Prop`-irrelevant + lowering-erased). The predicate `φ`
            // becomes a separate contract obligation at the use site (const
            // positivity hypothesis / fn pre-/post-condition), handled by the
            // callers that own the binding name — never here.
            Type::Refine { base, .. } => self.elab_type(base),
        }
    }

    /// Elaborate a refinement predicate `φ` (over its bound value `var`) as the
    /// kernel proposition `φ[var := head]`: elaborate `φ` once under the binder
    /// (`var` → de Bruijn `#0`), then β-substitute `head` for `#0`
    /// ([`subst_top`]). Used to attach a refinement's contract to a concrete
    /// term (`head = cnst(x)` for a const / a bound param). Errors if `φ` is not
    /// a `Prop` (e.g. an unbound generic `'p` resolves to "unknown symbol").
    fn refine_pred_at(
        &mut self,
        var: &str,
        kbase: &K,
        pred: &S,
        head: &K,
    ) -> Result<K, FaceError> {
        let mut ctx: Vec<(String, K)> = vec![(var.to_string(), kbase.clone())];
        let kpred = self.elab_term(&mut ctx, pred)?;
        let phi = subst_top(&kpred, head);
        let ty = infer(&self.env, &Ctx::new(), &phi)?;
        if !is_def_eq(&self.env, &ty, &K::prop()) {
            return Err(unsupported(format!(
                "refinement predicate has sort `{ty}`, expected Bool/Prop"
            )));
        }
        Ok(phi)
    }

    fn elab_term(&mut self, ctx: &mut Vec<(String, K)>, t: &S) -> Result<K, FaceError> {
        match t {
            S::Var(name) => {
                if let Some(pos) = ctx.iter().rposition(|(n, _)| n == name) {
                    Ok(K::bound(ctx.len() - 1 - pos))
                } else if self.env.lookup(name).is_some() {
                    Ok(K::cnst(name.clone()))
                } else {
                    Err(unsupported(format!("unknown symbol `{name}`")))
                }
            }
            S::IntLit(s) => Ok(theory::int_literal(&mut self.env, s)?),
            S::RealLit(s) => Ok(theory::real_literal(&mut self.env, s)?),
            S::Bool(true) => Ok(K::cnst("true")),
            S::Bool(false) => Ok(K::cnst("false")),
            S::Not(a) => {
                let ka = self.elab_term(ctx, a)?;
                Ok(K::app(K::cnst("not"), ka))
            }
            S::Neg(a) => {
                let ka = self.elab_term(ctx, a)?;
                let s = infer(&self.env, &kernel_ctx(ctx), &ka)?;
                let op = if is_int(&self.env, &s) {
                    theory::INT_NEG
                } else if is_real(&self.env, &s) {
                    theory::REAL_NEG
                } else {
                    return Err(unsupported(format!("unary `-` on non-numeric sort `{s}`")));
                };
                Ok(K::app(K::cnst(op), ka))
            }
            S::Bin(op, l, r) => self.elab_bin(ctx, *op, l, r),
            S::Call(name, args) => self.elab_call(ctx, name, args),
            // triggers are MBQI matching control; the kernel `Π` cannot carry
            // them, so they are dropped here (to be threaded out-of-band as
            // solver metadata once the CIC→HOL solver path lands). Dropping is
            // sound: triggers only *guide* instantiation, never change meaning.
            S::Forall(bs, body, _trigs) | S::Exists(bs, body, _trigs) => {
                let forall = matches!(t, S::Forall(..));
                self.elab_quant(ctx, bs, body, forall)
            }
            S::Let(x, e, body) => {
                let ke = self.elab_term(ctx, e)?;
                let ty = infer(&self.env, &kernel_ctx(ctx), &ke)?;
                ctx.push((x.clone(), ty.clone()));
                let kb = self.elab_term(ctx, body);
                ctx.pop();
                Ok(K::let_(ty, ke, kb?))
            }
        }
    }

    fn elab_quant(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        binders: &[Binder],
        body: &S,
        forall: bool,
    ) -> Result<K, FaceError> {
        let depth0 = ctx.len();
        let mut sorts = Vec::new();
        // a binder's inline refinement constraint `(names: T) op rhs` desugars to
        // one guard `name op rhs` per name — a *domain* restriction, conjoined
        // into the antecedent (∀) / conjunct (∃), kept distinct from any body
        // antecedent the author writes.
        let mut guards: Vec<S> = Vec::new();
        for b in binders {
            let ty = self.elab_type(&b.ty)?;
            for name in &b.names {
                sorts.push(ty.clone());
                ctx.push((name.clone(), ty.clone()));
            }
            if let Some((op, rhs)) = &b.constraint {
                for name in &b.names {
                    guards.push(S::Bin(*op, Box::new(S::Var(name.clone())), rhs.clone()));
                }
            }
            // a bounded range `x in lo..hi` adds the half-open domain guard
            // `lo <= x and x < hi`.
            if let Some((lo, hi)) = &b.range {
                let x = S::Var(b.names[0].clone());
                guards.push(S::Bin(BinOp::Le, lo.clone(), Box::new(x.clone())));
                guards.push(S::Bin(BinOp::Lt, Box::new(x), hi.clone()));
            }
            // a refinement-type binder `{names : T | φ}` adds the arbitrary
            // predicate `φ` (in scope of the just-bound names) as one domain
            // guard — the general form of the comparison constraint.
            if let Some(pred) = &b.refinement {
                guards.push((**pred).clone());
            }
        }
        // elaborate the guards + body in the binder context; restore the context
        // regardless of success so an error doesn't leave it dirty.
        let r = self.elab_guards_and_body(ctx, &guards, body);
        ctx.truncate(depth0);
        let (kguards, kbody) = r?;
        // guard the body with the domain constraints.
        let inner = if kguards.is_empty() {
            kbody
        } else {
            let conj = and_chain_k(kguards);
            if forall {
                K::arrow(conj, kbody) // (∧ guards) ==> body
            } else {
                K::apps(K::cnst("and"), [conj, kbody]) // (∧ guards) ∧ body
            }
        };
        if forall {
            Ok(adsmt_ir::build_pi(&sorts, inner))
        } else {
            // ∃ nests right-to-left: Exists T0 (λT0. Exists T1 (λT1. … inner)).
            let mut acc = inner;
            for ty in sorts.into_iter().rev() {
                let lam = K::lam(ty.clone(), acc);
                acc = K::apps(K::cnst("exists"), [ty, lam]);
            }
            Ok(acc)
        }
    }

    /// Elaborate the binder guards and the quantifier body in the (already
    /// extended) context. Split out so [`elab_quant`] can restore the context on
    /// either outcome.
    fn elab_guards_and_body(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        guards: &[S],
        body: &S,
    ) -> Result<(Vec<K>, K), FaceError> {
        let mut kguards = Vec::with_capacity(guards.len());
        for g in guards {
            kguards.push(self.elab_term(ctx, g)?);
        }
        let kbody = self.elab_term(ctx, body)?;
        Ok((kguards, kbody))
    }

    fn elab_call(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        name: &str,
        args: &[S],
    ) -> Result<K, FaceError> {
        let kargs: Vec<K> =
            args.iter().map(|a| self.elab_term(ctx, a)).collect::<Result<_, _>>()?;
        // built-in function names map to the arithmetic prelude constants;
        // anything else must be a declared symbol.
        let head = match name {
            "pow" => theory::POW,
            "odd" => theory::ODD,
            "prime" => theory::PRIME,
            "abs" => theory::INT_ABS,
            "div" => theory::INT_DIV,
            "mod" => theory::INT_MOD,
            "to_real" => theory::INT2REAL,
            _ => {
                if self.env.lookup(name).is_none() && !ctx.iter().any(|(n, _)| n == name) {
                    return Err(unsupported(format!("unknown function symbol `{name}`")));
                }
                // a declared function / bound functional — resolve as a Var head.
                let f = self.elab_term(ctx, &S::Var(name.to_string()))?;
                return Ok(K::apps(f, kargs));
            }
        };
        Ok(K::apps(K::cnst(head), kargs))
    }

    fn elab_bin(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        op: BinOp,
        l: &S,
        r: &S,
    ) -> Result<K, FaceError> {
        // logical connectives elaborate their operands directly.
        match op {
            BinOp::And => {
                let (a, b) = self.elab_pair(ctx, l, r)?;
                return Ok(K::apps(K::cnst("and"), [a, b]));
            }
            BinOp::Or => {
                let (a, b) = self.elab_pair(ctx, l, r)?;
                return Ok(K::apps(K::cnst("or"), [a, b]));
            }
            BinOp::Implies => {
                let (a, b) = self.elab_pair(ctx, l, r)?;
                return Ok(K::arrow(a, b));
            }
            BinOp::Iff => {
                let (a, b) = self.elab_pair(ctx, l, r)?;
                // a <==> b  ≡  (a ==> b) ∧ (b ==> a)
                return Ok(K::apps(
                    K::cnst("and"),
                    [K::arrow(a.clone(), b.clone()), K::arrow(b, a)],
                ));
            }
            _ => {}
        }
        // (dis)equality + comparison + arithmetic: sort-directed, with the
        // numeric injections inserted where a narrower operand meets a wider
        // one (`Nat ⊂ WNat ⊂ Int ⊂ Real`).
        let ka = self.elab_term(ctx, l)?;
        let kb = self.elab_term(ctx, r)?;
        let sa = infer(&self.env, &kernel_ctx(ctx), &ka)?;
        let sb = infer(&self.env, &kernel_ctx(ctx), &kb)?;
        let (ka, kb, s) = self.unify_sorts(ka, kb, sa, sb)?;
        match op {
            BinOp::Eq => Ok(K::apps(K::cnst("="), [s, ka, kb])),
            BinOp::Ne => {
                Ok(K::app(K::cnst("not"), K::apps(K::cnst("="), [s, ka, kb])))
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let rel = arith_rel(&self.env, op, &s)
                    .ok_or_else(|| unsupported(format!("comparison on non-numeric sort `{s}`")))?;
                Ok(K::apps(K::cnst(rel), [ka, kb]))
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                let arith = arith_binop(&self.env, op, &s).ok_or_else(|| {
                    unsupported(format!("`{op:?}` not available on sort `{s}`"))
                })?;
                Ok(K::apps(K::cnst(arith), [ka, kb]))
            }
            BinOp::And | BinOp::Or | BinOp::Implies | BinOp::Iff => unreachable!(),
        }
    }

    fn elab_pair(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        l: &S,
        r: &S,
    ) -> Result<(K, K), FaceError> {
        Ok((self.elab_term(ctx, l)?, self.elab_term(ctx, r)?))
    }

    /// Reconcile two operand sorts via the numeric injection lattice
    /// (`Nat ⊂ WNat ⊂ Int ⊂ Real`): equal sorts pass through; a narrower numeric
    /// operand is injected up to the wider sort (the design's
    /// elaborator-inserts-injections rule); otherwise the operands are rejected.
    /// Returns the (possibly coerced) operand terms and their common sort.
    fn unify_sorts(&self, ka: K, kb: K, sa: K, sb: K) -> Result<(K, K, K), FaceError> {
        if is_def_eq(&self.env, &sa, &sb) {
            return Ok((ka, kb, sa));
        }
        match (numeric_rank(&self.env, &sa), numeric_rank(&self.env, &sb)) {
            (Some(ra), Some(rb)) if ra < rb => Ok((inject(ka, ra, rb), kb, sb)),
            (Some(ra), Some(rb)) if ra > rb => Ok((ka, inject(kb, rb, ra), sa)),
            _ => Err(unsupported(format!("operands of differing sorts `{sa}` and `{sb}`"))),
        }
    }
}

// ── helpers ───────────────────────────────────────────────────────────────

fn kernel_ctx(ctx: &[(String, K)]) -> Ctx {
    ctx.iter().map(|(_, t)| t.clone()).collect()
}

/// Left-fold non-empty kernel `Prop`s with `and` (a single term unchanged).
fn and_chain_k(mut ts: Vec<K>) -> K {
    let mut acc = ts.remove(0);
    for t in ts {
        acc = K::apps(K::cnst("and"), [acc, t]);
    }
    acc
}

fn is_type0(ty: &K) -> bool {
    matches!(ty.kind(), adsmt_ir::TermKind::Sort(adsmt_ir::Univ::Type(0)))
}

/// The position of a numeric sort in the injection lattice
/// `Nat(0) ⊂ WNat(1) ⊂ Int(2) ⊂ Real(3)`, or `None` for a non-numeric sort.
fn numeric_rank(env: &Env, s: &K) -> Option<u8> {
    for (name, r) in [(theory::NAT, 0u8), (theory::WNAT, 1), (theory::INT, 2), (theory::REAL, 3)] {
        if is_def_eq(env, s, &K::cnst(name)) {
            return Some(r);
        }
    }
    None
}

/// Inject a term of numeric rank `from` up to rank `to` (`from < to`) via the
/// single prelude injection constant for that pair.
fn inject(t: K, from: u8, to: u8) -> K {
    let inj = match (from, to) {
        (0, 1) => theory::NAT2WNAT,
        (0, 2) => theory::NAT2INT,
        (0, 3) => theory::NAT2REAL,
        (1, 2) => theory::WNAT2INT,
        (1, 3) => theory::WNAT2REAL,
        (2, 3) => theory::INT2REAL,
        _ => unreachable!("inject: from < to over {{0,1,2,3}}"),
    };
    K::app(K::cnst(inj), t)
}

fn is_int(env: &Env, s: &K) -> bool {
    is_def_eq(env, s, &K::cnst(theory::INT))
}
fn is_real(env: &Env, s: &K) -> bool {
    is_def_eq(env, s, &K::cnst(theory::REAL))
}

/// The comparison constant for `op` at sort `s` (`Int.lt`/`Real.ge`/…).
fn arith_rel(env: &Env, op: BinOp, s: &K) -> Option<&'static str> {
    let int = is_int(env, s);
    if !int && !is_real(env, s) {
        return None;
    }
    Some(match op {
        BinOp::Lt => if int { theory::INT_LT } else { theory::REAL_LT },
        BinOp::Le => if int { theory::INT_LE } else { theory::REAL_LE },
        BinOp::Gt => if int { theory::INT_GT } else { theory::REAL_GT },
        BinOp::Ge => if int { theory::INT_GE } else { theory::REAL_GE },
        _ => return None,
    })
}

/// The arithmetic constant for `op` at sort `s`. `/` is Real-only (`div`/`mod`
/// are written as calls, §built-ins).
fn arith_binop(env: &Env, op: BinOp, s: &K) -> Option<&'static str> {
    let int = is_int(env, s);
    if !int && !is_real(env, s) {
        return None;
    }
    Some(match op {
        BinOp::Add => if int { theory::INT_ADD } else { theory::REAL_ADD },
        BinOp::Sub => if int { theory::INT_SUB } else { theory::REAL_SUB },
        BinOp::Mul => if int { theory::INT_MUL } else { theory::REAL_MUL },
        BinOp::Div => {
            if int {
                return None; // Int division is the `div`/`mod` calls, not `/`
            }
            theory::REAL_DIV
        }
        _ => return None,
    })
}
