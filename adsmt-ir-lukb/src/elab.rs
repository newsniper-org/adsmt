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
                self.elab_fn(name, params, ret, body)?;
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

    /// Elaborate a `fn` item — possibly **predicate-polymorphic** in generic
    /// refinement parameters `'p`. The kernel encoding (proofs `Prop`-irrelevant
    /// + lowering-erased):
    ///
    /// ```text
    ///   fn g(x: {v:T | 'p v}): {w:U | 'p w} [= body]
    ///     g : Π('p: T→Prop). Π(x: T). U          -- value sorts erase refinements
    ///     contract:  ∀'p. ∀x. 'p(x) ⟹ 'p(g('p, x))
    /// ```
    ///
    /// The generic `'p` are collected from every param/return refinement and
    /// bound implicitly at the head as `Π('p: base→Prop)` (predicate
    /// polymorphism — the body type-checks ONCE with `'p` abstract; the
    /// "checked-once" guarantee). Each param refinement becomes a **precondition**
    /// (deduped conjunction — idempotence `r∧…∧r ⟺ r`), the return refinement a
    /// **postcondition**: a definition emits the contract as a **goal** (the
    /// construct-site obligation `prove φ(result)`); a signature postulates it as
    /// a **trusted axiom** (the user asserts the contract). At a use site the
    /// caller instantiates `'p := q` and discharges the now-monomorphic
    /// precondition — the dictionary-passing of the pre-verified §5.2.
    fn elab_fn(
        &mut self,
        name: &str,
        params: &[(Vec<String>, Type)],
        ret: &Type,
        body: &Option<S>,
    ) -> Result<(), FaceError> {
        // 1. collect the generic predicate parameters `'p` (in first-seen order)
        //    from every refinement predicate, each over its refinement's base.
        let mut pred_names: Vec<String> = Vec::new();
        let mut pred_bases: Vec<Type> = Vec::new();
        let see_refinement = |ty: &Type, pn: &mut Vec<String>, pb: &mut Vec<Type>| {
            if let Type::Refine { base, pred, .. } = ty {
                let mut ticks = Vec::new();
                collect_ticks(pred, &mut ticks);
                for t in ticks {
                    if let Some(i) = pn.iter().position(|x| *x == t) {
                        // a `'p` reused across refinements must keep one domain.
                        if pb[i] != **base {
                            return Err(unsupported(format!(
                                "generic predicate `{t}` used over two different domains"
                            )));
                        }
                    } else {
                        pn.push(t);
                        pb.push((**base).clone());
                    }
                }
            }
            Ok(())
        };
        for (_, ty) in params {
            see_refinement(ty, &mut pred_names, &mut pred_bases)?;
        }
        see_refinement(ret, &mut pred_names, &mut pred_bases)?;

        // 2. kernel sorts for the `'p` binders: `'p : base → Prop`.
        let mut pred_sorts: Vec<K> = Vec::with_capacity(pred_names.len());
        for base in &pred_bases {
            let kbase = self.elab_type(base)?;
            pred_sorts.push(K::arrow(kbase, K::prop()));
        }

        // 3. flatten value params: (name, base type, optional (refvar, refpred)).
        let mut vnames: Vec<String> = Vec::new();
        let mut vbase_tys: Vec<Type> = Vec::new();
        let mut vrefine: Vec<Option<(String, S)>> = Vec::new();
        for (names, ty) in params {
            let (base_ty, refine) = match ty {
                Type::Refine { var, base, pred } => {
                    ((**base).clone(), Some((var.clone(), (**pred).clone())))
                }
                other => (other.clone(), None),
            };
            for n in names {
                vnames.push(n.clone());
                vbase_tys.push(base_ty.clone());
                vrefine.push(refine.clone());
            }
        }
        let vsorts: Vec<K> =
            vbase_tys.iter().map(|t| self.elab_type(t)).collect::<Result<_, _>>()?;

        // 4. the fn kernel type: Π('p…). Π(x…). ret_base  (refinements erased).
        let ret_base = match ret {
            Type::Refine { base, .. } => (**base).clone(),
            other => other.clone(),
        };
        let kret = self.elab_type(&ret_base)?;
        let mut value_chain = kret;
        for s in vsorts.iter().rev() {
            value_chain = K::arrow(s.clone(), value_chain);
        }
        let ty = adsmt_ir::build_pi(&pred_sorts, value_chain);

        // 5. define (with a body) or postulate (a signature).
        match body {
            None => {
                postulate(&mut self.env, name, ty.clone())?;
            }
            Some(b) => {
                let mut ctx: Vec<(String, K)> = Vec::new();
                for (pn, ps) in pred_names.iter().zip(&pred_sorts) {
                    ctx.push((pn.clone(), ps.clone()));
                }
                for (vn, vs) in vnames.iter().zip(&vsorts) {
                    ctx.push((vn.clone(), vs.clone()));
                }
                let kbody = self.elab_term(&mut ctx, b)?;
                let mut lam = kbody;
                for s in vsorts.iter().rev() {
                    lam = K::lam(s.clone(), lam);
                }
                for s in pred_sorts.iter().rev() {
                    lam = K::lam(s.clone(), lam);
                }
                define(&mut self.env, name, ty.clone(), lam)?;
            }
        }

        // 6. the contract obligation — only when the RETURN is refined.
        if let Type::Refine { var: rv, pred: rp, .. } = ret {
            // result = g('p…, x…); for a def it δ-unfolds to the body.
            let mut result_args: Vec<S> = pred_names.iter().map(|n| S::Var(n.clone())).collect();
            result_args.extend(vnames.iter().map(|n| S::Var(n.clone())));
            let result = S::Call(name.to_string(), result_args);
            let post = subst_surface(rp, rv, &result);
            // precondition: the deduped conjunction of every param refinement,
            // each instantiated at its parameter name (idempotence dedup).
            let mut pre: Vec<S> = Vec::new();
            for (vn, refine) in vnames.iter().zip(&vrefine) {
                if let Some((rvar, rpred)) = refine {
                    pre.push(subst_surface(rpred, rvar, &S::Var(vn.clone())));
                }
            }
            let inner = match surface_conj_dedup(pre) {
                Some(conj) => S::Bin(BinOp::Implies, Box::new(conj), Box::new(post)),
                None => post,
            };
            // ∀ over the value params (plain typed binders).
            let vc_body = if vnames.is_empty() {
                inner
            } else {
                let binders = vnames
                    .iter()
                    .zip(&vbase_tys)
                    .map(|(n, t)| Binder {
                        names: vec![n.clone()],
                        ty: t.clone(),
                        constraint: None,
                        range: None,
                        refinement: None,
                    })
                    .collect();
                S::Forall(binders, Box::new(inner), Vec::new())
            };
            // elaborate under the `'p` binders, then wrap them as `Π('p…)`.
            let mut ctx: Vec<(String, K)> = pred_names
                .iter()
                .cloned()
                .zip(pred_sorts.iter().cloned())
                .collect();
            let kvc_inner = self.elab_term(&mut ctx, &vc_body)?;
            let kvc = adsmt_ir::build_pi(&pred_sorts, kvc_inner);
            // a closed `Prop`, re-checked by the kernel.
            let kty = infer(&self.env, &Ctx::new(), &kvc)?;
            if !is_def_eq(&self.env, &kty, &K::prop()) {
                return Err(unsupported(format!("fn contract is not a Prop: {kty}")));
            }
            match body {
                Some(_) => self.goals.push(kvc),  // construct-site obligation
                None => self.hyps.push(kvc),      // trusted contract axiom
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
            // a function type `T -> U` → the kernel arrow. A refined arrow's
            // value sort is the plain arrow over the base sorts (the `'p`/`'q`
            // refinements are erased here; their pre-/postcondition role is
            // realised when the arrow-typed value is used — see
            // `docs/design/SOLVE_BY_PROOF_TERMS.md`).
            Type::Arrow(dom, cod) => Ok(K::arrow(self.elab_type(dom)?, self.elab_type(cod)?)),
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

/// Left-fold non-empty kernel `Prop`s with `and`, first dropping
/// structurally-identical conjuncts (the idempotence `r ∧ … ∧ r ⟺ r`; cheap
/// since kernel terms are hash-consed, so `==` is `Arc::ptr_eq`). A single term
/// is returned unchanged.
fn and_chain_k(ts: Vec<K>) -> K {
    let mut uniq: Vec<K> = Vec::with_capacity(ts.len());
    for t in ts {
        if !uniq.contains(&t) {
            uniq.push(t);
        }
    }
    let mut it = uniq.into_iter();
    let mut acc = it.next().expect("and_chain_k: non-empty");
    for t in it {
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

// ── refinement / generic-predicate (`'p`) helpers ───────────────────────────

/// Capture-avoiding substitution of the free surface variable `from` by the
/// term `to` (used to instantiate a refinement's bound value `v` at a concrete
/// argument/result, and to rename `v` to a parameter name). Respects binder
/// shadowing in `let`/quantifiers; a binder's `range`/`constraint` sub-terms are
/// in the *enclosing* scope (substituted regardless), its `refinement` predicate
/// and body are in the binder's scope (substituted only when not shadowed).
fn subst_surface(t: &S, from: &str, to: &S) -> S {
    let go = |x: &S| subst_surface(x, from, to);
    match t {
        S::Var(n) => if n == from { to.clone() } else { t.clone() },
        S::IntLit(_) | S::RealLit(_) | S::Bool(_) => t.clone(),
        S::Not(a) => S::Not(Box::new(go(a))),
        S::Neg(a) => S::Neg(Box::new(go(a))),
        S::Bin(op, a, b) => S::Bin(*op, Box::new(go(a)), Box::new(go(b))),
        S::Call(f, args) => S::Call(f.clone(), args.iter().map(&go).collect()),
        S::Let(x, e, body) => {
            let e2 = go(e);
            let body2 = if x == from { (**body).clone() } else { go(body) };
            S::Let(x.clone(), Box::new(e2), Box::new(body2))
        }
        S::Forall(bs, body, trigs) => {
            let (bs2, shadow) = subst_binders(bs, from, to);
            let body2 = if shadow { (**body).clone() } else { go(body) };
            S::Forall(bs2, Box::new(body2), subst_trigs(trigs, from, to, shadow))
        }
        S::Exists(bs, body, trigs) => {
            let (bs2, shadow) = subst_binders(bs, from, to);
            let body2 = if shadow { (**body).clone() } else { go(body) };
            S::Exists(bs2, Box::new(body2), subst_trigs(trigs, from, to, shadow))
        }
    }
}

/// Substitute inside a binder group's sub-terms, returning the rewritten binders
/// and whether the group shadows `from` (so the caller leaves the body alone).
fn subst_binders(bs: &[Binder], from: &str, to: &S) -> (Vec<Binder>, bool) {
    let shadow = bs.iter().any(|b| b.names.iter().any(|n| n == from));
    let bs2 = bs
        .iter()
        .map(|b| Binder {
            names: b.names.clone(),
            ty: b.ty.clone(),
            // range bounds + constraint rhs live in the ENCLOSING scope.
            range: b
                .range
                .as_ref()
                .map(|(lo, hi)| (Box::new(subst_surface(lo, from, to)), Box::new(subst_surface(hi, from, to)))),
            constraint: b
                .constraint
                .as_ref()
                .map(|(op, rhs)| (*op, Box::new(subst_surface(rhs, from, to)))),
            // the refinement predicate is in the binder's own scope.
            refinement: b.refinement.as_ref().map(|p| {
                if shadow { p.clone() } else { Box::new(subst_surface(p, from, to)) }
            }),
        })
        .collect();
    (bs2, shadow)
}

fn subst_trigs(trigs: &[Vec<S>], from: &str, to: &S, shadow: bool) -> Vec<Vec<S>> {
    if shadow {
        return trigs.to_vec();
    }
    trigs.iter().map(|pats| pats.iter().map(|p| subst_surface(p, from, to)).collect()).collect()
}

/// Left-fold surface predicates with `and`, dropping structurally-identical
/// conjuncts first (the idempotence `r ∧ … ∧ r ⟺ r`). `None` for the empty
/// conjunction (a vacuous precondition).
fn surface_conj_dedup(ts: Vec<S>) -> Option<S> {
    let mut uniq: Vec<S> = Vec::new();
    for t in ts {
        if !uniq.contains(&t) {
            uniq.push(t);
        }
    }
    let mut it = uniq.into_iter();
    let mut acc = it.next()?;
    for t in it {
        acc = S::Bin(BinOp::And, Box::new(acc), Box::new(t));
    }
    Some(acc)
}

/// Collect the free generic-predicate parameters (`'p`, [`is_tick_ident`]) used
/// in a surface predicate, into `acc` (Call heads + bare Vars).
fn collect_ticks(t: &S, acc: &mut Vec<String>) {
    let push = |n: &str, acc: &mut Vec<String>| {
        if crate::lexer::is_tick_ident(n) && !acc.iter().any(|x| x == n) {
            acc.push(n.to_string());
        }
    };
    match t {
        S::Var(n) => push(n, acc),
        S::Call(f, args) => {
            push(f, acc);
            for a in args {
                collect_ticks(a, acc);
            }
        }
        S::Not(a) | S::Neg(a) => collect_ticks(a, acc),
        S::Bin(_, a, b) => {
            collect_ticks(a, acc);
            collect_ticks(b, acc);
        }
        S::Let(_, e, body) => {
            collect_ticks(e, acc);
            collect_ticks(body, acc);
        }
        S::Forall(bs, body, _) | S::Exists(bs, body, _) => {
            for b in bs {
                if let Some(p) = &b.refinement {
                    collect_ticks(p, acc);
                }
            }
            collect_ticks(body, acc);
        }
        S::IntLit(_) | S::RealLit(_) | S::Bool(_) => {}
    }
}
