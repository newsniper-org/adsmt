//! Elaborate a parsed lu-kb-successor [`Module`] into a **kernel-checked**
//! [`Env`] + the obligation/hypothesis term lists. Every elaborated term is
//! re-checked by the adsmt-ir kernel (each `axiom`/`assume`/`goal` body must be
//! a closed `Prop`), so a face bug can only ever yield a [`FaceError`], never a
//! trusted ill-typed term — the same firewall as the SMT-LIB / ASP faces.

use std::collections::HashMap;
use std::collections::hash_map::Entry;

use adsmt_class::resolve::{ClassGoal, ResolutionResult, Resolver};
use adsmt_class::{Instance, InstanceDb, LawProver, Premise};
use adsmt_ir::theory;
use adsmt_ir::{
    Ctx, Env, Modality, Term as K, TriggerMap, Univ, as_const_app, declare_inductive, define,
    infer, is_def_eq, peel_pis, postulate, record_triggers, shift, subst_top, whnf,
};

use crate::ast::{Arm, BinOp, Binder, Item, Module, PatArg, Pattern, Term as S, Type};
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
    /// Out-of-band `trigger` metadata: each triggered surface `forall`,
    /// keyed by the hash-consed kernel term of the WHOLE quantifier (the
    /// outermost `Π` of its telescope; see [`adsmt_ir::triggers`]). Pattern
    /// terms are elaborated under the same de Bruijn window as the body.
    /// Purely advisory: a pattern that fails to elaborate drops that
    /// quantifier's triggers (never a [`FaceError`]).
    pub triggers: TriggerMap,
}

/// Parse + elaborate lu-kb-successor source. The pure-face entry: no law
/// prover is available, so each `data` declaration's `Eq` instance is the
/// STRUCTURAL grant (see [`elaborate_with_prover`] for the lawful form).
pub fn elaborate(src: &str) -> Result<Elaborated, FaceError> {
    elaborate_impl(src, None)
}

/// [`elaborate`] with an injected [`LawProver`] (F3,
/// docs/design/EQ_ORD_UPCAST_RELATIONS.md): each `data` declaration's
/// `Eq(T)` instance is admitted LAWFULLY — the prover must discharge the
/// `Eq` relation's equivalence + decidability laws at the carrier, and a
/// failed discharge BUILD-REJECTS the declaration (a [`FaceError`], never a
/// silent structural fallback). The live driver passes the engine-backed
/// prover; the face itself stays engine-free (the prover is a parameter, the
/// `adsmt-class` layering rule).
pub fn elaborate_with_prover(src: &str, prover: &dyn LawProver) -> Result<Elaborated, FaceError> {
    elaborate_impl(src, Some(prover))
}

fn elaborate_impl(src: &str, prover: Option<&dyn LawProver>) -> Result<Elaborated, FaceError> {
    let module: Module = parse(src)?;
    let mut e = Elab::new(prover)?;
    for item in &module.items {
        e.item(item)?;
    }
    Ok(Elaborated { env: e.env, hypotheses: e.hyps, goals: e.goals, triggers: e.triggers })
}

struct Elab<'p> {
    env: Env,
    hyps: Vec<K>,
    goals: Vec<K>,
    /// A counter for the fresh proof tokens of `solve … by …` (`!solve.N`).
    solve_n: usize,
    /// A counter for fresh `match` field binders (`!match.N` — a `!` name can
    /// never lex as a user identifier, so it cannot shadow one).
    fresh_n: usize,
    /// The type-relation registry (F2, docs/design/EQ_ORD_UPCAST_RELATIONS.md):
    /// `=`/`!=` are Rust-style Eq-GATED (every declared sort is auto-granted a
    /// builtin `Eq`, so the gate is explicit but observationally conservative),
    /// cross-sort equality resolves `PartialEq(A, B)` (whose lattice edges
    /// premise the `UpCast` that performs the injection), and comparisons
    /// resolve `PartialOrd`.
    classes: InstanceDb,
    /// The injected law prover (F3): present → each `data` declaration's
    /// `Eq(T)` instance is admitted LAWFULLY (laws discharged at the concrete
    /// carrier, failure = build-reject); absent → the structural grant.
    prover: Option<&'p dyn LawProver>,
    /// The field-selector registry (#403): surface field name → the datatype
    /// plus the CANONICAL positional selector `{ctor}!sel{i}` (the name the
    /// #325 lowering synthesizes into `DatatypeDecl.selectors`, so the
    /// engine's datatype theory reduces its applications). `None` poisons an
    /// AMBIGUOUS field name (declared by more than one constructor) — a call
    /// on it keeps the unknown-symbol error rather than guessing a target.
    selector_fields: HashMap<String, Option<(String, String)>>,
    /// Out-of-band trigger metadata (see [`Elaborated::triggers`]).
    triggers: TriggerMap,
}

impl<'p> Elab<'p> {
    fn new(prover: Option<&'p dyn LawProver>) -> Result<Self, FaceError> {
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
        // `ite : Π(T: Type). Prop → T → T → T` — the polymorphic conditional the
        // surface `if`/`match`-on-`true`/`false` elaborates to, spelled exactly
        // `"ite"` so the #325 lowering recognizes it (`hoist_term_ite` removes a
        // term-`ite` by the verified atom-duplication; the Bool-branch instance
        // lowers classically). A prelude postulate, not a kernel change.
        let ite_ty = K::pi(
            K::type_(0),
            K::arrow(K::prop(), K::arrow(K::bound(0), K::arrow(K::bound(0), K::bound(0)))),
        );
        postulate(&mut env, "ite", ite_ty)?;
        // `nop : Π(T: Type). T → Prop := λ T x. true` — the trivial (always-true)
        // predicate. An UNREFINED type `x: T` is treated as `{x: T | nop(x)}`, so
        // the refinement-aware logic always sees a predicate (the user's
        // uniformity); a `nop`/true refinement is vacuous and dropped at use.
        let nop_ty = K::pi(K::type_(0), K::arrow(K::bound(0), K::prop()));
        let nop_body = K::lam(K::type_(0), K::lam(K::bound(0), K::cnst("true")));
        define(&mut env, "nop", nop_ty, nop_body)?;
        // the FULL arithmetic prelude (Int/Real/Nat/WNat + ops + injections +
        // pow/odd/prime) — the lu-kb surface uses Nat/WNat/pow/… as built-ins.
        theory::install_arith(&mut env)?;
        // the type-relation registry: the Eq/UpCast family + the numeric
        // builtins, the diagonal + lattice-edge PartialOrd instances, and the
        // `Bool` (= Prop) equality. User sorts / ring sorts / datatypes are
        // granted their builtin `Eq` at their declaration sites.
        let mut classes = InstanceDb::new();
        adsmt_class::declare_eq_ord_relations(&mut classes);
        classes.declare_relation(adsmt_class::partial_ord());
        classes.declare_relation(adsmt_class::ord());
        adsmt_class::install_eq_ord_numeric(&mut classes);
        const NUMERICS: [&str; 4] = ["Nat", "WNat", "Int", "Real"];
        const EDGES: [(&str, &str); 6] = [
            ("Nat", "WNat"),
            ("WNat", "Int"),
            ("Int", "Real"),
            ("Nat", "Int"),
            ("Nat", "Real"),
            ("WNat", "Real"),
        ];
        let cty = |n: &str| adsmt_core::Type::const_(n, adsmt_core::Kind::Type);
        for n in NUMERICS {
            let c = cty(n);
            classes
                .declare_instance(
                    Instance::new(adsmt_class::numberlike::PARTIAL_ORD, vec![c.clone(), c.clone()])
                        .with_premise(Premise::new(adsmt_class::PARTIAL_EQ, vec![c.clone(), c.clone()]))
                        .with_premise(Premise::new(adsmt_class::UP_CAST, vec![c.clone(), c])),
                )
                .map_err(|e| unsupported(format!("class registry: {e}")))?;
        }
        for (f, t) in EDGES {
            let (cf, ct) = (cty(f), cty(t));
            classes
                .declare_instance(
                    Instance::new(
                        adsmt_class::numberlike::PARTIAL_ORD,
                        vec![cf.clone(), ct.clone()],
                    )
                    .with_premise(Premise::new(adsmt_class::PARTIAL_EQ, vec![cf.clone(), ct.clone()]))
                    .with_premise(Premise::new(adsmt_class::UP_CAST, vec![cf, ct])),
                )
                .map_err(|e| unsupported(format!("class registry: {e}")))?;
        }
        let mut elab = Elab {
            env,
            hyps: Vec::new(),
            goals: Vec::new(),
            solve_n: 0,
            fresh_n: 0,
            classes,
            prover,
            selector_fields: HashMap::new(),
            triggers: TriggerMap::new(),
        };
        elab.grant_eq("Bool"); // surface Bool = kernel Prop: equality (iff), no order
        Ok(elab)
    }

    /// Grant the BUILTIN `Eq` (+ diagonal `PartialEq`) instance a declared sort
    /// receives (owner ruling 2: `=` is Eq-gated, so every declared sort —
    /// uninterpreted, ring, `Bool`, numeric, datatype — carries one; numerics
    /// are installed by `install_eq_ord_numeric`, everything else lands here).
    /// Idempotent: a duplicate grant is ignored (the registry's coherence check
    /// makes re-declaration an error, so a second grant is simply skipped).
    fn grant_eq(&mut self, sort: &str) {
        let _ = self.classes.declare_instance(adsmt_class::partial_eq_diag_instance(sort));
        let _ = self.classes.declare_instance(adsmt_class::eq_instance(sort));
    }

    /// The `data`-declaration `Eq` grant (F3): with an injected prover the
    /// `Eq(T)` instance is admitted LAWFULLY — the prover discharges the
    /// equivalence + decidability laws of `=` at the carrier (the diagonal
    /// `PartialEq` premise carries the `=` method body they are stated over),
    /// and a failed discharge BUILD-REJECTS the datatype's equality (a
    /// [`FaceError`], never a silent structural fallback). Without a prover
    /// (the pure face) this is the structural [`Self::grant_eq`].
    fn grant_eq_data(&mut self, sort: &str) -> Result<(), FaceError> {
        match self.prover {
            None => {
                self.grant_eq(sort);
                Ok(())
            }
            Some(p) => {
                let _ =
                    self.classes.declare_instance(adsmt_class::partial_eq_diag_instance(sort));
                self.classes
                    .declare_instance_lawful(adsmt_class::eq_instance(sort), p)
                    .map_err(|e| {
                        unsupported(format!("lawful `Eq({sort})` derivation rejected: {e}"))
                    })
            }
        }
    }

    /// The class-registry carrier name of a kernel SORT term: `Prop` ↦ `Bool`,
    /// a plain sort constant ↦ its name. `None` for anything else (a function
    /// sort / applied sort has no registry carrier).
    fn class_sort_name(&self, s: &K) -> Option<String> {
        // whnf first: a `match`'s motive application leaves a β-redex sort
        // (`(λ:N. Int) n`) that must reduce before classification.
        let s = adsmt_ir::whnf(&self.env, s);
        if is_def_eq(&self.env, &s, &K::prop()) {
            return Some("Bool".into());
        }
        match adsmt_ir::as_const_app(&s) {
            Some((n, args)) if args.is_empty() => Some(n),
            _ => None,
        }
    }

    /// The Rust-style `Eq` gate for a SAME-sort `=`/`!=` (owner ruling 2): the
    /// sort must carry an `Eq` instance. Every declared sort is auto-granted
    /// one, so today this is observationally conservative — the gate exists
    /// for the future opt-out and for the F3 lawful datatype derivation.
    fn require_eq(&self, s: &K) -> Result<(), FaceError> {
        let n = self
            .class_sort_name(s)
            .ok_or_else(|| unsupported(format!("`=` needs a registry sort, got `{s}`")))?;
        let c = adsmt_core::Type::const_(&n, adsmt_core::Kind::Type);
        match Resolver::new(&self.classes).resolve(&ClassGoal::new(adsmt_class::EQ, vec![c])) {
            ResolutionResult::Found(_) => Ok(()),
            _ => Err(unsupported(format!("no `Eq({n})` instance licenses `=` at sort `{n}`"))),
        }
    }

    /// The CROSS-sort equality gate: `PartialEq(A, B)` must resolve (the
    /// synchronized mirror covers the flipped operand order); its lattice-edge
    /// instances premise the `UpCast` that `unify_sorts` then performs.
    fn require_partial_eq(&self, sa: &K, sb: &K) -> Result<(), FaceError> {
        let (na, nb) = match (self.class_sort_name(sa), self.class_sort_name(sb)) {
            (Some(a), Some(b)) => (a, b),
            _ => return Err(unsupported(format!("operands of differing sorts `{sa}` and `{sb}`"))),
        };
        let (ca, cb) = (
            adsmt_core::Type::const_(&na, adsmt_core::Kind::Type),
            adsmt_core::Type::const_(&nb, adsmt_core::Kind::Type),
        );
        match Resolver::new(&self.classes)
            .resolve(&ClassGoal::new(adsmt_class::PARTIAL_EQ, vec![ca, cb]))
        {
            ResolutionResult::Found(_) => Ok(()),
            _ => Err(unsupported(format!(
                "no `PartialEq({na}, {nb})` instance licenses `=` across sorts `{na}` and `{nb}`"
            ))),
        }
    }

    /// The comparison gate: `PartialOrd` must resolve in EITHER operand order
    /// (`a < b` with only `PartialOrd(B, A)` is the flipped comparison — the
    /// order is decided in the upcast target either way).
    fn require_partial_ord(&self, sa: &K, sb: &K) -> Result<(), FaceError> {
        let (na, nb) = match (self.class_sort_name(sa), self.class_sort_name(sb)) {
            (Some(a), Some(b)) => (a, b),
            _ => {
                return Err(unsupported(format!(
                    "comparison needs registry sorts, got `{sa}` and `{sb}`"
                )));
            }
        };
        let (ca, cb) = (
            adsmt_core::Type::const_(&na, adsmt_core::Kind::Type),
            adsmt_core::Type::const_(&nb, adsmt_core::Kind::Type),
        );
        let r = Resolver::new(&self.classes);
        let po = adsmt_class::numberlike::PARTIAL_ORD;
        if matches!(
            r.resolve(&ClassGoal::new(po, vec![ca.clone(), cb.clone()])),
            ResolutionResult::Found(_)
        ) || matches!(r.resolve(&ClassGoal::new(po, vec![cb, ca])), ResolutionResult::Found(_))
        {
            Ok(())
        } else {
            Err(unsupported(format!(
                "no `PartialOrd({na}, {nb})` instance licenses a comparison between `{na}` and `{nb}`"
            )))
        }
    }

    fn item(&mut self, item: &Item) -> Result<(), FaceError> {
        match item {
            Item::Sort(s) => {
                postulate(&mut self.env, s, K::type_(0))?;
                self.grant_eq(s); // owner ruling 2: every declared sort carries Eq
            }
            Item::Const(x, ty) => {
                self.ensure_ring_sorts(ty)?; // pre-declare any GF(p)/IntModulo/GFPower sort
                // a refinement-typed constant `const c: {v: T | φ}` postulates
                // `c : T` PLUS the trusted fact `φ[v := c]` as a top-level
                // hypothesis. Dropping it would be unsound: an arbitrary `T`
                // value could violate `φ`, admitting a spurious model (the same
                // reason the Nat/WNat collapse re-asserts free-const positivity).
                if let Type::Refine { var, base, pred } = ty {
                    let kbase = self.elab_type(base)?;
                    postulate(&mut self.env, x, kbase.clone())?;
                    let phi = self.refine_pred_at(var, &kbase, pred, &K::cnst(x.clone()))?;
                    // a vacuous (trivially-true, e.g. `nop`) refinement adds no
                    // hypothesis — so `const c: {v:T | nop(v)}` ≡ `const c: T`.
                    if !is_def_eq(&self.env, &phi, &K::cnst("true")) {
                        self.hyps.push(phi);
                    }
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
                let mut kctors: Vec<(String, Vec<K>)> = Vec::with_capacity(ctors.len());
                // named fields, for the selector admission below (#403):
                // `(surface field name, ctor, field index, elaborated field type)`.
                let mut named_fields: Vec<(String, String, usize, K)> = Vec::new();
                for (cname, fields) in ctors {
                    let mut ftypes = Vec::with_capacity(fields.len());
                    for (i, (selname, fty)) in fields.iter().enumerate() {
                        self.ensure_ring_sorts(fty)?; // pre-declare GF(p)/… field sorts
                        let kty = self.elab_field_type(fty, name)?;
                        if let Some(sn) = selname {
                            named_fields.push((sn.clone(), cname.clone(), i, kty.clone()));
                        }
                        ftypes.push(kty);
                    }
                    kctors.push((cname.clone(), ftypes));
                }
                declare_inductive(&mut self.env, name, Vec::new(), Univ::Type(0), kctors)?;
                // the datatype's Eq grant (F3): LAWFUL when a prover is
                // injected (see `grant_eq_data`), structural in the pure
                // face — the `is-{ctor}` testers ride this instance.
                self.grant_eq_data(name)?;
                // #403: field-selector admission. Each NAMED field postulates
                // the CANONICAL positional selector `{ctor}!sel{i} : D → fieldTy`
                // (so kernel `infer` types its applications; the #325 lowering
                // recognizes the name and the engine's `DatatypeDecl` already
                // declares it — see `spec_to_decl`) and registers the surface
                // field name so `elab_call` can rewrite a field APPLICATION
                // `field(x)` onto the canonical head. A second declaration of
                // the same field name poisons the entry (ambiguous — refuse to
                // guess which constructor's field was meant).
                for (field, cname, i, kty) in named_fields {
                    let canonical = format!("{cname}!sel{i}");
                    if self.env.lookup(&canonical).is_none() {
                        postulate(&mut self.env, &canonical, K::arrow(K::cnst(name), kty))?;
                    }
                    match self.selector_fields.entry(field) {
                        Entry::Vacant(v) => {
                            v.insert(Some((name.clone(), canonical)));
                        }
                        // duplicate targets are impossible (a ctor name is
                        // kernel-unique and a ctor's fields are positional), so
                        // any occupied hit IS a cross-constructor ambiguity.
                        Entry::Occupied(mut o) => {
                            o.insert(None);
                        }
                    }
                }
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
        // 0. pre-declare any GF(p)/IntModulo(m)/GFPower(p,n) sort in a parameter or
        //    return type (validating the parameters) before the immutable elab_type.
        for (_, ty) in params {
            self.ensure_ring_sorts(ty)?;
        }
        self.ensure_ring_sorts(ret)?;

        // 1. collect the generic predicate parameters `'p` (in first-seen order)
        //    from every refinement predicate, each over its refinement's base.
        //    `collect_pred_params` recurses through `Type::Arrow`/`Type::App`, so
        //    a **refined-arrow** parameter `{u:A|'p(u)} -> {v:A|'q(v)}` (the user's
        //    `preserving` surface) contributes both `'p` and `'q`.
        let mut pred_names: Vec<String> = Vec::new();
        let mut pred_bases: Vec<Type> = Vec::new();
        for (_, ty) in params {
            collect_pred_params(ty, &mut pred_names, &mut pred_bases)?;
        }
        collect_pred_params(ret, &mut pred_names, &mut pred_bases)?;

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
                        image: None,
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

    /// Pre-declare (postulate as `Type(0)`) every value-parameterized RING sort
    /// (`GF(p)` / `IntModulo(m)` / `GFPower(p, n)`) reachable in `ty`, validating
    /// the parameters (a non-prime `GF`, an `m < 2` `IntModulo`, a degree-0
    /// `GFPower` → error). Idempotent (memoized by the postulated canonical name).
    /// Must run under `&mut self` BEFORE the immutable `elab_type` looks the sort up.
    fn ensure_ring_sorts(&mut self, ty: &Type) -> Result<(), FaceError> {
        match ty {
            Type::App(n, args) => match ring_sort_name(n, args)? {
                Some(canon) => {
                    if self.env.lookup(&canon).is_none() {
                        postulate(&mut self.env, &canon, K::type_(0))?;
                        self.grant_eq(&canon); // ring sorts carry Eq too
                    }
                }
                None => {
                    for a in args {
                        self.ensure_ring_sorts(a)?;
                    }
                }
            },
            Type::Arrow(d, c) => {
                self.ensure_ring_sorts(d)?;
                self.ensure_ring_sorts(c)?;
            }
            Type::Refine { base, .. } => self.ensure_ring_sorts(base)?,
            Type::Name(_) => {}
        }
        Ok(())
    }

    fn elab_type(&self, ty: &Type) -> Result<K, FaceError> {
        match ty {
            Type::Name(n) if n == "Bool" => Ok(K::prop()),
            Type::Name(n) => match self.env.lookup(n) {
                Some(d) if is_type0(&d.ty) => Ok(K::cnst(n.clone())),
                Some(_) => Err(unsupported(format!("`{n}` is not a sort"))),
                None => Err(unsupported(format!("unknown sort `{n}`"))),
            },
            // A value-parameterized ("dependent") RING sort: `GF(p)` (finite
            // field), `IntModulo(m)` (`ℤ/mℤ`), `GFPower(p, n)` (`GF(pⁿ)`). It
            // elaborates to a canonical NAMED sort (`GF!7`, …) that `ensure_ring_sorts`
            // has already postulated as `Type(0)` — so the KERNEL is unchanged (no
            // dependent types; the parameter validation lives here, at the face). A
            // non-ring parametric sort is still a later slice. NOTE (ring-native
            // arithmetic): the four operations over such a sort are NOT integer
            // arithmetic — reasoning over them routes to the `adsmt-cas` re-check
            // core (the CAS-delegation follow-on), never an `Int` relativization.
            Type::App(n, args) => match ring_sort_name(n, args)? {
                Some(canon) => match self.env.lookup(&canon) {
                    Some(d) if is_type0(&d.ty) => Ok(K::cnst(canon)),
                    _ => Err(unsupported(format!("ring sort `{n}(…)` was not pre-declared"))),
                },
                None => Err(unsupported(format!("parametric sort `{n}(…)` is a later slice"))),
            },
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
            // them, so a `forall`'s triggers are threaded OUT-OF-BAND into
            // `self.triggers` (keyed by the whole hash-consed `Π` telescope;
            // see [`adsmt_ir::triggers`]) — advisory metadata, so a pattern
            // that fails to elaborate only drops that quantifier's triggers,
            // never rejects the module. `exists` keeps dropping (the solver
            // path Skolemizes; there is no instantiation to guide).
            S::Forall(bs, body, trigs) => self.elab_quant(ctx, bs, body, true, trigs),
            S::Exists(bs, body, _trigs) => self.elab_quant(ctx, bs, body, false, &[]),
            S::Let(x, e, body) => {
                let ke = self.elab_term(ctx, e)?;
                let ty = infer(&self.env, &kernel_ctx(ctx), &ke)?;
                ctx.push((x.clone(), ty.clone()));
                let kb = self.elab_term(ctx, body);
                ctx.pop();
                Ok(K::let_(ty, ke, kb?))
            }
            // `if c then a else b` → the polymorphic `ite` prelude application
            // `(ite T c a b)` — NEVER a `Bool`-inductive match (the prelude has
            // no Bool inductive; surface Bool = kernel Prop). The condition must
            // be a Prop; the branch sorts reconcile through the same numeric
            // lattice binary operators use, so `if p then 1 else 2.5` injects
            // Int→Real. Lowering then routes by the instance sort: a first-order
            // value rides `hoist_term_ite` (verified atom-duplication), a Prop
            // instance the classical `(c → a) ∧ (¬c → b)`.
            S::If(c, a, b) => {
                let kc = self.elab_term(ctx, c)?;
                let sc = infer(&self.env, &kernel_ctx(ctx), &kc)?;
                if !is_def_eq(&self.env, &sc, &K::prop()) {
                    return Err(unsupported(format!(
                        "`if` condition must be a Bool/Prop, got sort `{sc}`"
                    )));
                }
                let ka = self.elab_term(ctx, a)?;
                let kb = self.elab_term(ctx, b)?;
                let sa = infer(&self.env, &kernel_ctx(ctx), &ka)?;
                let sb = infer(&self.env, &kernel_ctx(ctx), &kb)?;
                let (ka, kb, s) = self.unify_sorts(ka, kb, sa, sb)?;
                Ok(K::apps(K::cnst("ite"), [s, kc, ka, kb]))
            }
            S::Match(scrut, arms) => self.elab_match(ctx, scrut, arms),
            S::SolveBy(g, l) => self.elab_solve_by(ctx, g, l),
        }
    }

    /// Elaborate `solve G by L` (semantics B, the cut): elaborate `G`/`L` to
    /// `Prop`s, emit the **leaf** `∀ctx. L` and the **bridge** `∀ctx. (L ⟹ G)` as
    /// goals (both closed over the ambient context so they are well-formed at top
    /// level), and return a **proof of `G`** — a fresh token `!solve.N : ∀ctx. G`
    /// applied to the ambient binders. The token is admitted, but `G` only holds
    /// once both obligations discharge (the cut), so the module is rejected if
    /// either fails — no `by` shortcuts an obligation
    /// (`docs/design/SOLVE_BY_PROOF_TERMS.md` §3, §6).
    fn elab_solve_by(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        g: &S,
        l: &S,
    ) -> Result<K, FaceError> {
        let kg = self.elab_term(ctx, g)?;
        let kl = self.elab_term(ctx, l)?;
        let prop = K::prop();
        let tg = infer(&self.env, &kernel_ctx(ctx), &kg)?;
        if !is_def_eq(&self.env, &tg, &prop) {
            return Err(unsupported(format!("`solve` goal has sort `{tg}`, expected Bool/Prop")));
        }
        let tl = infer(&self.env, &kernel_ctx(ctx), &kl)?;
        if !is_def_eq(&self.env, &tl, &prop) {
            return Err(unsupported(format!("`solve … by` lemma has sort `{tl}`, expected Bool/Prop")));
        }
        // close the obligations over the ambient context (outermost binder first).
        let ctx_sorts: Vec<K> = ctx.iter().map(|(_, t)| t.clone()).collect();
        let leaf = adsmt_ir::build_pi(&ctx_sorts, kl.clone());
        let bridge = adsmt_ir::build_pi(&ctx_sorts, K::arrow(kl, kg.clone()));
        self.goals.push(leaf);
        self.goals.push(bridge);
        // the proof token `!solve.N : ∀ctx. G`, applied to the ambient binders.
        let tok = format!("!solve.{}", self.solve_n);
        self.solve_n += 1;
        postulate(&mut self.env, &tok, adsmt_ir::build_pi(&ctx_sorts, kg))?;
        let args: Vec<K> = (0..ctx.len()).rev().map(K::bound).collect();
        Ok(K::apps(K::cnst(tok), args))
    }

    /// The PREIMAGE name + its kernel sort for an image binder `{y = e | c}`.
    /// `e` must have the form `f(x)`: the preimage is `x` and its sort is `f`'s
    /// domain (inferred — the heavy abbreviation the surface relies on).
    fn image_preimage(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        e: &S,
    ) -> Result<(String, K), FaceError> {
        if let S::Call(f, args) = e
            && let [S::Var(x)] = args.as_slice()
        {
            let kf = self.elab_term(ctx, &S::Var(f.clone()))?;
            let tf = infer(&self.env, &kernel_ctx(ctx), &kf)?;
            if let adsmt_ir::TermKind::Pi(dom, _) = tf.kind() {
                return Ok((x.clone(), dom.clone()));
            }
            return Err(unsupported(format!(
                "image binder `{{… = {f}(…) | …}}`: `{f}` is not a function (type `{tf}`)"
            )));
        }
        Err(unsupported("an image binder `{ y = e | c }` requires `e` of the form `f(x)`"))
    }

    fn elab_quant(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        binders: &[Binder],
        body: &S,
        forall: bool,
        trigs: &[Vec<S>],
    ) -> Result<K, FaceError> {
        let depth0 = ctx.len();
        let mut sorts = Vec::new();
        // a binder's inline refinement constraint `(names: T) op rhs` desugars to
        // one guard `name op rhs` per name — a *domain* restriction, conjoined
        // into the antecedent (∀) / conjunct (∃), kept distinct from any body
        // antecedent the author writes.
        let mut guards: Vec<S> = Vec::new();
        // image binders `{y = f(x) | c}` unfold `y := f(x)` in the body.
        let mut body_substs: Vec<(String, S)> = Vec::new();
        for b in binders {
            // an **image binder** `{y = f(x) | c}` ranges over the inferred
            // PREIMAGE `x` (type = `f`'s domain), guards it by `c`, and unfolds
            // `y := f(x)` in the body (the pre-verified `image_quantifier_desugar`).
            if let Some((e, c)) = &b.image {
                let (x, dom) = self.image_preimage(ctx, e)?;
                sorts.push(dom.clone());
                ctx.push((x, dom));
                guards.push((**c).clone());
                body_substs.push((b.names[0].clone(), (**e).clone()));
                continue;
            }
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
        // unfold image-binder definitions (`y := f(x)`) in the body.
        let body_owned;
        let body = if body_substs.is_empty() {
            body
        } else {
            let mut b = body.clone();
            for (y, e) in &body_substs {
                b = subst_surface(&b, y, e);
            }
            body_owned = b;
            &body_owned
        };
        // elaborate the guards + body in the binder context; restore the context
        // regardless of success so an error doesn't leave it dirty.
        let r = self.elab_guards_and_body(ctx, &guards, body);
        // trigger patterns elaborate under the SAME binder window (identical
        // de Bruijn indices as the body) — but ADVISORILY: any failure yields
        // `None` (drop this quantifier's triggers), never a `FaceError`.
        let ktrigs = if forall && !trigs.is_empty() && r.is_ok() {
            self.elab_trigger_groups(ctx, trigs, &body_substs)
        } else {
            None
        };
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
            let pi = adsmt_ir::build_pi(&sorts, inner);
            // record the triggers keyed by the WHOLE telescope term; arity =
            // the number of value binders (guard-arrows sit INSIDE the
            // telescope, so they don't count — the lowering peels exactly
            // `arity` Πs and finds the guard implication in the residual).
            if let Some(groups) = ktrigs {
                record_triggers(&mut self.triggers, pi.clone(), sorts.len(), groups);
            }
            Ok(pi)
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

    /// Elaborate a `forall`'s trigger groups in the (already extended) binder
    /// context. Returns `None` — never an error — if ANY pattern fails to
    /// elaborate or kernel-typecheck: triggers are advisory instantiation
    /// guidance, and a bad pattern must not reject a working module.
    fn elab_trigger_groups(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        trigs: &[Vec<S>],
        body_substs: &[(String, S)],
    ) -> Option<Vec<Vec<K>>> {
        let kctx = kernel_ctx(ctx);
        let mut groups = Vec::with_capacity(trigs.len());
        for group in trigs {
            let mut kgroup = Vec::with_capacity(group.len());
            for pat in group {
                // image binders unfold `y := f(x)` in the body — patterns get
                // the SAME substitution (they range over the same window).
                let pat_owned;
                let pat = if body_substs.is_empty() {
                    pat
                } else {
                    let mut p = pat.clone();
                    for (y, e) in body_substs {
                        p = subst_surface(&p, y, e);
                    }
                    pat_owned = p;
                    &pat_owned
                };
                let kpat = match self.elab_term(ctx, pat) {
                    Ok(k) => k,
                    Err(e) => {
                        if std::env::var_os("ADSMT_LUKB_DEBUG").is_some() {
                            eprintln!("[lukb-dbg] trigger pattern dropped (elab): {e}");
                        }
                        return None;
                    }
                };
                // a pattern must at least be kernel-well-typed in the window.
                let sort = match infer(&self.env, &kctx, &kpat) {
                    Ok(s) => s,
                    Err(e) => {
                        if std::env::var_os("ADSMT_LUKB_DEBUG").is_some() {
                            eprintln!("[lukb-dbg] trigger pattern dropped (typecheck): {e}");
                        }
                        return None;
                    }
                };
                // …and FULLY applied: a function-sorted pattern (a partial
                // application like `g2(x)` for binary `g2`) is legal CIC but
                // renders as an ill-arity `:pattern` the solver accepts yet can
                // never e-match — a DEAD trigger that suppresses inference and
                // denies the verdict. Drop it (over-application already fails
                // `infer` above; this closes the under-application half).
                if matches!(whnf(&self.env, &sort).kind(), adsmt_ir::TermKind::Pi(..)) {
                    if std::env::var_os("ADSMT_LUKB_DEBUG").is_some() {
                        eprintln!(
                            "[lukb-dbg] trigger pattern dropped (function-sorted / partial application)"
                        );
                    }
                    return None;
                }
                kgroup.push(kpat);
            }
            if !kgroup.is_empty() {
                groups.push(kgroup);
            }
        }
        if groups.is_empty() { None } else { Some(groups) }
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
        // `nop(x)` — the trivial predicate. It is polymorphic (`Π(T).T→Prop`), so
        // infer the implicit type argument from `x`'s sort: `nop[typeof(x)](x)`.
        if name == "nop" && args.len() == 1 {
            let kx = self.elab_term(ctx, &args[0])?;
            let sort = infer(&self.env, &kernel_ctx(ctx), &kx)?;
            return Ok(K::apps(K::cnst("nop"), [sort, kx]));
        }
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
                    // F3: the `is-{ctor}` recognizer (verus emits tester
                    // calls for datatype constructors). Only a constructor of
                    // a DECLARED datatype desugars — anything else keeps the
                    // unknown-symbol error, and a DECLARED `is-…` symbol
                    // never reaches here (the env lookup above wins).
                    if let Some(ctor) = name.strip_prefix("is-") {
                        if let Some(k) = self.elab_tester(ctx, ctor, &kargs)? {
                            return Ok(k);
                        }
                    }
                    // #403: a datatype FIELD name applied as a selector (verus
                    // emits AIR selector applies verbatim) — rewrite onto the
                    // canonical positional selector head.
                    if let Some(k) = self.elab_selector(ctx, name, &kargs)? {
                        return Ok(k);
                    }
                    return Err(unsupported(format!("unknown function symbol `{name}`")));
                }
                // a declared function / bound functional — resolve as a Var head.
                let f = self.elab_term(ctx, &S::Var(name.to_string()))?;
                return Ok(K::apps(f, kargs));
            }
        };
        Ok(K::apps(K::cnst(head), kargs))
    }

    /// The `is-{ctor}` recognizer (F3, docs/design/EQ_ORD_UPCAST_RELATIONS.md
    /// §"How this solves #391"). `Some(term)` when `ctor` names a constructor
    /// of a declared non-parametric datatype `D`:
    ///
    /// * nullary `C` ⟶ the bare equality `x = C` (a single licensed atom);
    /// * field-bearing `C` ⟶ the kernel `Match`
    ///   `match x { C(..) => true, _ => false }` — the kernel has NO selector
    ///   PRIMITIVE (the canonical `{C}!sel{i}` names are opaque postulates,
    ///   see [`Self::elab_selector`]), so the kernel-native tester is the
    ///   definitional case split;
    ///   its lowering image is exactly the selector-applied shape-equality
    ///   form the engine's datatype theory decides (the SMT-LIB face's
    ///   `9881b21` biconditional, encoded per-constructor).
    ///
    /// Both forms are LICENSED by the datatype's `Eq` instance (the F3 lawful
    /// derivation) — the family's design point: the tester rides `Eq(T)`.
    /// `None` when `ctor` is not a declared constructor (the caller keeps its
    /// unknown-symbol error); a recognized constructor with the wrong arity
    /// or a wrongly-sorted argument is a hard error naming the tester.
    fn elab_tester(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        ctor: &str,
        kargs: &[K],
    ) -> Result<Option<K>, FaceError> {
        // `ctor` must be a declared constructor; its result sort names the
        // datatype (a non-parametric ctor type is `field₀ → … → D`).
        let ctor_ty = match self.env.lookup(ctor) {
            Some(d) if matches!(d.modality, Modality::Constructor) => d.ty.clone(),
            _ => return Ok(None),
        };
        let mut rty = ctor_ty;
        while let adsmt_ir::TermKind::Pi(_, b) = rty.kind() {
            rty = b.clone();
        }
        let Some((dt, targs)) = as_const_app(&rty) else { return Ok(None) };
        if !targs.is_empty() {
            return Err(unsupported(format!(
                "tester `is-{ctor}` over parametric/indexed datatype `{dt}` (a later slice)"
            )));
        }
        // constructor readback (the `elab_match` idiom): names + field sorts,
        // in declaration order.
        let ctors: Vec<(String, Vec<K>)> = {
            let Some(ind) = self.env.inductive(&dt) else { return Ok(None) };
            if !ind.params.is_empty() || !ind.indices.is_empty() {
                return Err(unsupported(format!(
                    "tester `is-{ctor}` over parametric/indexed datatype `{dt}` (a later slice)"
                )));
            }
            ind.ctors
                .iter()
                .map(|c| {
                    let doms =
                        peel_pis(&c.ty, c.args_count).map(|(d, _)| d).unwrap_or_default();
                    (c.name.clone(), doms)
                })
                .collect()
        };
        if kargs.len() != 1 {
            return Err(unsupported(format!(
                "tester `is-{ctor}` is unary, got {} argument(s)",
                kargs.len()
            )));
        }
        let arg = kargs[0].clone();
        let asort = infer(&self.env, &kernel_ctx(ctx), &arg)?;
        if !is_def_eq(&self.env, &asort, &K::cnst(dt.clone())) {
            return Err(unsupported(format!(
                "tester `is-{ctor}` expects a `{dt}`, got sort `{asort}`"
            )));
        }
        // the Eq(T) license — the tester elaborates THROUGH the datatype's Eq.
        self.require_eq(&K::cnst(dt.clone()))?;
        let field_bearing =
            ctors.iter().any(|(cn, doms)| cn == ctor && !doms.is_empty());
        if !field_bearing {
            return Ok(Some(K::apps(K::cnst("="), [K::cnst(dt), arg, K::cnst(ctor)])));
        }
        let motive = K::lam(K::cnst(dt.clone()), K::prop());
        let minors = ctors
            .iter()
            .map(|(cname, doms)| {
                let mut acc =
                    if cname == ctor { K::cnst("true") } else { K::cnst("false") };
                for d in doms.iter().rev() {
                    acc = K::lam(d.clone(), acc);
                }
                acc
            })
            .collect();
        Ok(Some(K::mtch(dt, motive, minors, arg)))
    }

    /// The datatype **field-selector** application (#403 — the #391 tester
    /// pattern one seat over): verus's AIR emits selector applies verbatim
    /// (`` `<Ind>./<Ctor>/?N`(x) ``) while the `data` declaration names that
    /// selector as constructor-field sugar — this hook connects the two.
    /// `Some(term)` when `name` is the declared field of exactly ONE
    /// constructor: the call rewrites onto the CANONICAL positional selector
    /// `{ctor}!sel{i}` (postulated `D → fieldTy` at the `data` site — the
    /// name the #325 lowering emits as a `Const` leaf and the engine's
    /// datatype theory reduces, `sel(C(..a..)) = a_i` congruence-closed
    /// (#330), unconstrained on the other constructors — exactly SMT-LIB
    /// selector semantics). `None` when `name` is not a declared field (the
    /// caller keeps its unknown-symbol error) or is AMBIGUOUS (two
    /// constructors declare it — the positional target would be a guess);
    /// the wrong arity or a wrongly-sorted argument is a hard error naming
    /// the selector, mirroring [`Self::elab_tester`].
    fn elab_selector(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        name: &str,
        kargs: &[K],
    ) -> Result<Option<K>, FaceError> {
        let Some(Some((dt, canonical))) = self.selector_fields.get(name) else {
            return Ok(None);
        };
        let (dt, canonical) = (dt.clone(), canonical.clone());
        if kargs.len() != 1 {
            return Err(unsupported(format!(
                "selector `{name}` is unary, got {} argument(s)",
                kargs.len()
            )));
        }
        let arg = kargs[0].clone();
        let asort = infer(&self.env, &kernel_ctx(ctx), &arg)?;
        if !is_def_eq(&self.env, &asort, &K::cnst(dt.clone())) {
            return Err(unsupported(format!(
                "selector `{name}` expects a `{dt}`, got sort `{asort}`"
            )));
        }
        Ok(Some(K::apps(K::cnst(canonical), [arg])))
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
        // the type-relation gates (F2): `=`/`!=` are Eq-gated (same sort) /
        // PartialEq-gated (cross sort); comparisons are PartialOrd-gated. The
        // arithmetic ops stay lattice-governed by `unify_sorts` alone.
        match op {
            BinOp::Eq | BinOp::Ne => {
                if is_def_eq(&self.env, &sa, &sb) {
                    self.require_eq(&sa)?;
                } else {
                    self.require_partial_eq(&sa, &sb)?;
                }
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                self.require_partial_ord(&sa, &sb)?;
            }
            _ => {}
        }
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

    // ── `match` elaboration (the 2026-07-03 verus-fork proposal §4/§6) ──────

    /// A fresh `match` field-binder name. `!` cannot lex as a user identifier,
    /// so a fresh name can never shadow one (the `!solve.N` convention).
    fn fresh_name(&mut self) -> String {
        let n = self.fresh_n;
        self.fresh_n += 1;
        format!("!match.{n}")
    }

    /// Elaborate `match scrut { arms }`. Routing is by SCRUTINEE SORT, not
    /// keyword: a `Prop` scrutinee is a `true`/`false`-literal match and
    /// elaborates to the SAME `ite` prelude application as `if` (a definitional
    /// identity — the prelude has no `Bool` inductive to match on); a datatype
    /// scrutinee elaborates to the kernel `Match` eliminator.
    ///
    /// ## Exhaustiveness (proposal §6 — strict, owner-confirmed)
    ///
    /// The kernel demands exactly one TOTAL minor per constructor in
    /// declaration order (`check.rs`'s `BadElim` gate, no wildcard/default), so
    /// the surface buckets the arms per constructor (first-match, source
    /// order), expands wildcard/binder catch-alls into every bucket,
    /// right-folds guarded arms into the bucket's single minor as nested
    /// `ite`s, and requires each bucket to END in an unguarded arm (the
    /// syntactic backstop — semantic guard-completeness is undecidable and
    /// never attempted). A constructor with no total bucket is a HARD
    /// elaboration error: the surface NEVER fabricates a branch, so every
    /// kernel `Match` it emits is exhaustive by construction.
    fn elab_match(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        scrut: &S,
        arms: &[Arm],
    ) -> Result<K, FaceError> {
        if arms.is_empty() {
            return Err(unsupported("`match` needs at least one arm"));
        }
        let kscrut = self.elab_term(ctx, scrut)?;
        let sty = whnf(&self.env, &infer(&self.env, &kernel_ctx(ctx), &kscrut)?);
        if is_def_eq(&self.env, &sty, &K::prop()) {
            return self.elab_prop_match(ctx, &kscrut, scrut, arms);
        }
        if numeric_rank(&self.env, &sty).is_some() {
            return self.elab_scalar_match(ctx, &kscrut, &sty, scrut, arms);
        }
        let Some((ind_name, spine)) = as_const_app(&sty) else {
            return Err(unsupported(format!(
                "`match` scrutinee must be a datatype or Bool/Prop value, got sort `{sty}`"
            )));
        };
        // Constructor readback (names + per-ctor field sorts, owned so the env
        // borrow ends before arm bodies elaborate) — the one new elaborator
        // capability the proposal names (the `data` path only DECLARES).
        let ctors: Vec<(String, Vec<K>)> = {
            let Some(ind) = self.env.inductive(&ind_name) else {
                return Err(unsupported(format!(
                    "`match` scrutinee sort `{ind_name}` is not a datatype"
                )));
            };
            if !ind.params.is_empty() || !ind.indices.is_empty() || !spine.is_empty() {
                return Err(unsupported(format!(
                    "`match` over parametric/indexed datatype `{ind_name}` (a later slice)"
                )));
            }
            ind.ctors
                .iter()
                .map(|c| {
                    let doms = peel_pis(&c.ty, c.args_count).map(|(d, _)| d).unwrap_or_default();
                    (c.name.clone(), doms)
                })
                .collect()
        };
        let is_ctor = |n: &str| ctors.iter().any(|(cn, _)| cn == n);
        // Arm validation: unknown constructor, arity mismatch, a bare
        // non-nullary constructor name, a Prop-literal pattern on a datatype.
        for arm in arms {
            match &arm.pattern {
                Pattern::Ctor(n, pargs) => {
                    let Some((_, doms)) = ctors.iter().find(|(cn, _)| cn == n) else {
                        return Err(unsupported(format!(
                            "`{n}` is not a constructor of `{ind_name}`"
                        )));
                    };
                    if pargs.len() != doms.len() {
                        return Err(unsupported(format!(
                            "constructor pattern `{n}` has {} argument(s), expected {}",
                            pargs.len(),
                            doms.len()
                        )));
                    }
                }
                Pattern::Bind(n) if is_ctor(n) => {
                    let (_, doms) = ctors.iter().find(|(cn, _)| cn == n).expect("is_ctor");
                    if !doms.is_empty() {
                        return Err(unsupported(format!(
                            "bare constructor pattern `{n}` needs its {} field pattern(s)",
                            doms.len()
                        )));
                    }
                }
                Pattern::Bool(_) => {
                    return Err(unsupported(format!(
                        "`true`/`false` pattern on a `{ind_name}` scrutinee"
                    )));
                }
                Pattern::IntLit(_) | Pattern::RealLit(_) => {
                    return Err(unsupported(format!(
                        "numeric-literal pattern on a `{ind_name}` scrutinee"
                    )));
                }
                Pattern::Wild | Pattern::Bind(_) => {}
            }
        }
        // Bucket per constructor (declaration order; first-match in source
        // order; the bucket CLOSES at its first unguarded contributor — later
        // arms are unreachable for this constructor and silently kept, the
        // Rust warn-but-keep stance without a diagnostics channel yet).
        let mut per_ctor: Vec<(Vec<K>, Vec<MatchEntry>)> = Vec::with_capacity(ctors.len());
        for (cname, doms) in &ctors {
            let mut entries: Vec<MatchEntry> = Vec::new();
            let mut closed = false;
            for arm in arms {
                let applies = match &arm.pattern {
                    Pattern::Ctor(n, _) => n == cname,
                    Pattern::Bind(n) => {
                        if is_ctor(n) { n == cname } else { true } // catch-all binder
                    }
                    Pattern::Wild => true,
                    // rejected in the validation pass above
                    Pattern::Bool(_) | Pattern::IntLit(_) | Pattern::RealLit(_) => false,
                };
                if !applies {
                    continue;
                }
                let depth0 = ctx.len();
                // one λ-binder per non-parameter constructor field
                match &arm.pattern {
                    Pattern::Ctor(_, pargs) => {
                        for (pa, d) in pargs.iter().zip(doms) {
                            let nm = match pa {
                                PatArg::Bind(n) => n.clone(),
                                PatArg::Wild => self.fresh_name(),
                            };
                            ctx.push((nm, d.clone()));
                        }
                    }
                    _ => {
                        for d in doms {
                            let nm = self.fresh_name();
                            ctx.push((nm, d.clone()));
                        }
                    }
                }
                // A catch-all BINDER names the whole scrutinee: substitute the
                // SURFACE scrutinee for it (the fn-inline idiom) — re-elaborating
                // it under the field binders shifts its de Bruijn indices
                // correctly for free.
                let (body_s, guard_s) = match &arm.pattern {
                    Pattern::Bind(x) if !is_ctor(x) => (
                        subst_surface(&arm.body, x, scrut),
                        arm.guard.as_ref().map(|g| subst_surface(g, x, scrut)),
                    ),
                    _ => (arm.body.clone(), arm.guard.clone()),
                };
                let r = self.elab_arm_parts(ctx, &body_s, guard_s.as_ref());
                ctx.truncate(depth0);
                let entry = r?;
                let unguarded = entry.guard.is_none();
                entries.push(entry);
                if unguarded {
                    closed = true;
                    break;
                }
            }
            if !closed {
                return Err(unsupported(format!(
                    "non-exhaustive `match`: constructor `{cname}` of `{ind_name}` is uncovered \
                     (or reached only by guarded arms with no unguarded backstop)"
                )));
            }
            per_ctor.push((doms.clone(), entries));
        }
        // Common result sort across every entry (the numeric lattice, as in
        // `unify_sorts`), then coerce + guard-fold + λ-wrap each minor.
        let common = self.common_sort(per_ctor.iter().flat_map(|(_, es)| es.iter()))?;
        let mut minors = Vec::with_capacity(per_ctor.len());
        for (doms, entries) in per_ctor {
            let mut acc = self.fold_entries(entries, &common)?;
            for d in doms.iter().rev() {
                acc = K::lam(d.clone(), acc);
            }
            minors.push(acc);
        }
        // Non-dependent motive `λ(x : I). T` (Prop-valued T keeps the kernel's
        // Prop large-elimination bar trivially satisfied; a VALUE-valued T
        // type-checks too — the #325 lowering then soundly abstains on the
        // data-valued match).
        let motive = K::lam(K::cnst(ind_name.clone()), shift(1, 0, &common));
        Ok(K::mtch(ind_name, motive, minors, kscrut))
    }

    /// A `true`/`false` (Prop-literal) match — routed to the SAME `ite` builder
    /// as `if` (`match c {{ true => a, false => b }}` ≡ `if c then a else b` is
    /// definitional), never a `Bool` inductive.
    fn elab_prop_match(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        kscrut: &K,
        scrut: &S,
        arms: &[Arm],
    ) -> Result<K, FaceError> {
        let then_entries = self.prop_bucket(ctx, scrut, arms, true)?;
        let else_entries = self.prop_bucket(ctx, scrut, arms, false)?;
        let common = self.common_sort(then_entries.iter().chain(else_entries.iter()))?;
        let then_acc = self.fold_entries(then_entries, &common)?;
        let else_acc = self.fold_entries(else_entries, &common)?;
        Ok(K::apps(K::cnst("ite"), [common, kscrut.clone(), then_acc, else_acc]))
    }

    /// A match over a NUMERIC scalar scrutinee (Int/Real/Nat/WNat): there is
    /// no inductive to eliminate — a literal pattern `n => body` desugars to
    /// the equality guard `x if x = n => body` (the proposal §3 rule; Int/Real
    /// are not finite-constructor inductives, so a literal can only ever be a
    /// guard) and the whole match right-folds to a nested `ite` chain, which
    /// the verified term-`ite` lowering then DECIDES. Scalars cannot be
    /// exhausted by literals, so an UNGUARDED catch-all backstop (`_` or a
    /// binder) is mandatory — without one the match is non-exhaustive (hard
    /// error, §6 case 5a).
    fn elab_scalar_match(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        kscrut: &K,
        sty: &K,
        scrut: &S,
        arms: &[Arm],
    ) -> Result<K, FaceError> {
        let mut entries: Vec<MatchEntry> = Vec::new();
        let mut closed = false;
        for arm in arms {
            let lit: Option<S> = match &arm.pattern {
                Pattern::IntLit(s) => Some(S::IntLit(s.clone())),
                Pattern::RealLit(s) => Some(S::RealLit(s.clone())),
                Pattern::Wild | Pattern::Bind(_) => None,
                Pattern::Ctor(n, _) => {
                    return Err(unsupported(format!(
                        "constructor pattern `{n}` on a numeric scrutinee of sort `{sty}`"
                    )));
                }
                Pattern::Bool(_) => {
                    return Err(unsupported(format!(
                        "`true`/`false` pattern on a numeric scrutinee of sort `{sty}`"
                    )));
                }
            };
            // a binder catch-all names the scrutinee (surface substitution,
            // as in the datatype/Prop cases)
            let (body_s, guard_s) = match &arm.pattern {
                Pattern::Bind(x) => (
                    subst_surface(&arm.body, x, scrut),
                    arm.guard.as_ref().map(|g| subst_surface(g, x, scrut)),
                ),
                _ => (arm.body.clone(), arm.guard.clone()),
            };
            // the literal's equality guard `scrut = n` (numeric-lattice
            // reconciled, so `match x:Int { … }` rejects a Real literal it
            // cannot widen to)
            let lit_guard: Option<K> = match &lit {
                Some(l) => {
                    let kl = self.elab_term(ctx, l)?;
                    let sl = infer(&self.env, &kernel_ctx(ctx), &kl)?;
                    let (ks, kl, s) =
                        self.unify_sorts(kscrut.clone(), kl, sty.clone(), sl)?;
                    Some(K::apps(K::cnst("="), [s, ks, kl]))
                }
                None => None,
            };
            let entry = self.elab_arm_parts(ctx, &body_s, guard_s.as_ref())?;
            // `n if g => body` matches iff BOTH the literal equality and `g`.
            let combined = match (lit_guard, entry.guard) {
                (Some(l), Some(g)) => Some(K::apps(K::cnst("and"), [l, g])),
                (Some(l), None) => Some(l),
                (None, g) => g,
            };
            let unguarded = combined.is_none();
            entries.push(MatchEntry { guard: combined, body: entry.body, sort: entry.sort });
            if unguarded {
                closed = true;
                break;
            }
        }
        if !closed {
            return Err(unsupported(format!(
                "non-exhaustive `match` over the numeric sort `{sty}`: literals cannot \
                 exhaust it — add an unguarded `_` or binder backstop arm"
            )));
        }
        let common = self.common_sort(entries.iter())?;
        self.fold_entries(entries, &common)
    }

    /// The contributor entries of one Prop-literal bucket (`true` or `false`):
    /// first-match, closing at the first unguarded contributor; a bucket that
    /// never closes is a non-exhaustive hard error.
    fn prop_bucket(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        scrut: &S,
        arms: &[Arm],
        want: bool,
    ) -> Result<Vec<MatchEntry>, FaceError> {
        let mut entries: Vec<MatchEntry> = Vec::new();
        for arm in arms {
            let applies = match &arm.pattern {
                Pattern::Bool(b) => *b == want,
                // no constructors exist on Prop — a bare name is always a binder
                Pattern::Wild | Pattern::Bind(_) => true,
                Pattern::Ctor(n, _) => {
                    return Err(unsupported(format!(
                        "constructor pattern `{n}` on a Bool/Prop scrutinee"
                    )));
                }
                Pattern::IntLit(_) | Pattern::RealLit(_) => {
                    return Err(unsupported(
                        "numeric-literal pattern on a Bool/Prop scrutinee",
                    ));
                }
            };
            if !applies {
                continue;
            }
            let (body_s, guard_s) = match &arm.pattern {
                Pattern::Bind(x) => (
                    subst_surface(&arm.body, x, scrut),
                    arm.guard.as_ref().map(|g| subst_surface(g, x, scrut)),
                ),
                _ => (arm.body.clone(), arm.guard.clone()),
            };
            let entry = self.elab_arm_parts(ctx, &body_s, guard_s.as_ref())?;
            let unguarded = entry.guard.is_none();
            entries.push(entry);
            if unguarded {
                return Ok(entries);
            }
        }
        Err(unsupported(format!(
            "non-exhaustive `match`: `{want}` is uncovered (or reached only by guarded arms \
             with no unguarded backstop)"
        )))
    }

    /// Elaborate one contributor's body (+ optional guard, which must be a
    /// Prop) under the already-extended field-binder context. The caller
    /// truncates the context (even on error).
    fn elab_arm_parts(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        body: &S,
        guard: Option<&S>,
    ) -> Result<MatchEntry, FaceError> {
        let kb = self.elab_term(ctx, body)?;
        let sb = infer(&self.env, &kernel_ctx(ctx), &kb)?;
        let kg = match guard {
            Some(g) => {
                let kg = self.elab_term(ctx, g)?;
                let sg = infer(&self.env, &kernel_ctx(ctx), &kg)?;
                if !is_def_eq(&self.env, &sg, &K::prop()) {
                    return Err(unsupported(format!(
                        "match guard must be a Bool/Prop, got sort `{sg}`"
                    )));
                }
                Some(kg)
            }
            None => None,
        };
        Ok(MatchEntry { guard: kg, body: kb, sort: sb })
    }

    /// The common result sort of a non-empty entry iterator: def-eq sorts pass
    /// through, numeric sorts widen along the `Nat ⊂ WNat ⊂ Int ⊂ Real`
    /// lattice, anything else is rejected (the n-ary `unify_sorts`).
    fn common_sort<'a>(
        &self,
        mut entries: impl Iterator<Item = &'a MatchEntry>,
    ) -> Result<K, FaceError> {
        let mut common = entries.next().expect("non-empty bucket").sort.clone();
        for e in entries {
            if is_def_eq(&self.env, &e.sort, &common) {
                continue;
            }
            match (numeric_rank(&self.env, &common), numeric_rank(&self.env, &e.sort)) {
                (Some(ra), Some(rb)) if ra < rb => common = e.sort.clone(),
                (Some(ra), Some(rb)) if ra > rb => {}
                _ => {
                    return Err(unsupported(format!(
                        "match arms of differing sorts `{common}` and `{}`",
                        e.sort
                    )));
                }
            }
        }
        Ok(common)
    }

    /// Right-fold one bucket's contributors into a single body: the terminal
    /// (unguarded) entry seeds the accumulator, each earlier (guarded) entry
    /// wraps it as `(ite T g body acc)`. Every body is coerced up to the common
    /// sort first (numeric injections).
    fn fold_entries(&self, entries: Vec<MatchEntry>, common: &K) -> Result<K, FaceError> {
        let mut it = entries.into_iter().rev();
        let last = it.next().expect("closed bucket has a terminal entry");
        debug_assert!(last.guard.is_none(), "the terminal contributor is unguarded");
        let mut acc = self.coerce_to(last.body, &last.sort, common)?;
        for e in it {
            let g = e.guard.expect("non-terminal contributors are guarded");
            let b = self.coerce_to(e.body, &e.sort, common)?;
            acc = K::apps(K::cnst("ite"), [common.clone(), g, b, acc]);
        }
        Ok(acc)
    }

    /// Coerce `t : s` up to the `common` sort (identity when def-eq, numeric
    /// injection when narrower — `common_sort` guarantees one of the two).
    fn coerce_to(&self, t: K, s: &K, common: &K) -> Result<K, FaceError> {
        if is_def_eq(&self.env, s, common) {
            return Ok(t);
        }
        match (numeric_rank(&self.env, s), numeric_rank(&self.env, common)) {
            (Some(ra), Some(rb)) if ra < rb => Ok(inject(t, ra, rb)),
            _ => Err(unsupported(format!(
                "match arm of sort `{s}` cannot widen to `{common}`"
            ))),
        }
    }
}

/// One elaborated `match` contributor: its (Prop-checked) guard, its body, and
/// the body's inferred sort (pre-coercion).
struct MatchEntry {
    guard: Option<K>,
    body: K,
    sort: K,
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

/// If `n(args)` names a value-parameterized RING sort, its CANONICAL sort name —
/// `GF(7)` → `"GF!7"`, `IntModulo(6)` → `"IntModulo!6"`, `GFPower(2, 8)` →
/// `"GFPower!2!8"` — with the parameters VALIDATED (`GF`/`GFPower` need a PRIME
/// `p`; `IntModulo` needs `m ≥ 2`; `GFPower` needs degree `n ≥ 1`). `Ok(None)` if
/// `n` is not a ring sort; `Err` if it IS one but the parameters are invalid or
/// non-numeral. `!` cannot appear in a user identifier, so the canonical name
/// never collides with a user symbol. Parameter validation lives HERE at the face
/// (the kernel stays plain-CIC — the sort is just a postulated `Type(0)`); the
/// `adsmt-cas` re-check re-validates primality independently before trusting any
/// verdict, so this face check is a usability gate, not the soundness boundary.
fn ring_sort_name(n: &str, args: &[Type]) -> Result<Option<String>, FaceError> {
    if !matches!(n, "GF" | "IntModulo" | "GFPower") {
        return Ok(None);
    }
    let nums: Option<Vec<u64>> = args
        .iter()
        .map(|a| match a {
            Type::Name(s) => s.parse::<u64>().ok(),
            _ => None,
        })
        .collect();
    let Some(nums) = nums else {
        return Err(unsupported(format!("`{n}(…)` expects integer parameter(s)")));
    };
    match (n, nums.as_slice()) {
        ("GF", [p]) => {
            if !is_prime_u64(*p) {
                return Err(unsupported(format!("`GF({p})` requires a PRIME order; {p} is not prime")));
            }
            Ok(Some(format!("GF!{p}")))
        }
        ("IntModulo", [m]) => {
            if *m < 2 {
                return Err(unsupported(format!("`IntModulo({m})` requires a modulus m ≥ 2")));
            }
            Ok(Some(format!("IntModulo!{m}")))
        }
        ("GFPower", [p, k]) => {
            if !is_prime_u64(*p) {
                return Err(unsupported(format!("`GFPower({p}, {k})` requires a PRIME p; {p} is not prime")));
            }
            if *k < 1 {
                return Err(unsupported(format!("`GFPower({p}, {k})` requires an extension degree n ≥ 1")));
            }
            Ok(Some(format!("GFPower!{p}!{k}")))
        }
        _ => Err(unsupported(format!("`{n}` has the wrong number of parameters"))),
    }
}

/// Bounded trial-division primality (a usability gate for `GF`/`GFPower`; the
/// `adsmt-cas` re-check independently re-verifies before any trusted verdict).
fn is_prime_u64(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    if n.is_multiple_of(2) {
        return n == 2;
    }
    let mut d = 3u64;
    while d.saturating_mul(d) <= n {
        if n.is_multiple_of(d) {
            return false;
        }
        d += 2;
    }
    true
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
        // `if` binds nothing — substitute in all three parts.
        S::If(c, a, b) => S::If(Box::new(go(c)), Box::new(go(a)), Box::new(go(b))),
        // `match`: pattern-bound names SHADOW `from` in that arm's guard + body.
        // A bare-name pattern MIGHT be a nullary constructor (resolved only in
        // elab, against the env) — treating it as a binder here is the
        // conservative choice; the pathological "constructor name collides with
        // the substituted name" case is a known limitation, mirroring the
        // image-binder note below.
        S::Match(scrut, arms) => {
            let arms2 = arms
                .iter()
                .map(|arm| {
                    let shadow = match &arm.pattern {
                        Pattern::Bind(n) => n == from,
                        Pattern::Ctor(_, pargs) => pargs
                            .iter()
                            .any(|p| matches!(p, PatArg::Bind(n) if n == from)),
                        Pattern::Wild
                        | Pattern::Bool(_)
                        | Pattern::IntLit(_)
                        | Pattern::RealLit(_) => false,
                    };
                    Arm {
                        pattern: arm.pattern.clone(),
                        guard: arm
                            .guard
                            .as_ref()
                            .map(|g| if shadow { g.clone() } else { go(g) }),
                        body: if shadow { arm.body.clone() } else { go(&arm.body) },
                    }
                })
                .collect();
            S::Match(Box::new(go(scrut)), arms2)
        }
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
        S::SolveBy(g, l) => S::SolveBy(Box::new(go(g)), Box::new(go(l))),
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
            // an image binder's `e`/`c` mention the (locally-introduced) preimage;
            // substituting an outer var into them is sound (the common case —
            // shadowing the preimage itself is not tracked, a known limitation).
            image: b.image.as_ref().map(|(e, c)| {
                (Box::new(subst_surface(e, from, to)), Box::new(subst_surface(c, from, to)))
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

/// Collect the generic predicate parameters (`'p`) of a (possibly compound)
/// `fn` parameter/return **type**, recording each over its refinement's base
/// sort (first-seen order). Recurses through `Type::Arrow`/`Type::App` so a
/// **refined-arrow** type `{u:A|'p(u)} -> {v:A|'q(v)}` contributes both `'p` and
/// `'q`: the value sort erases the refinements (an arrow argument is `A → A`),
/// but its domain/codomain predicates are still bound at the `fn` head as
/// `Π('p: A→Prop)`. This is what lets the user's `preserving` predicate —
/// `fn preserving(f: {u:A|'p(u)} -> {v:A|'q(v)}): Bool = ∀x. 'p(x) ⟹ 'p(f(x))`
/// — name `'p`/`'q` in its body (see `docs/design/SOLVE_BY_PROOF_TERMS.md` §7).
/// A `'p` reused across refinements must keep a single domain.
fn collect_pred_params(
    ty: &Type,
    pn: &mut Vec<String>,
    pb: &mut Vec<Type>,
) -> Result<(), FaceError> {
    match ty {
        Type::Name(_) => Ok(()),
        Type::App(_, args) => {
            for a in args {
                collect_pred_params(a, pn, pb)?;
            }
            Ok(())
        }
        Type::Arrow(dom, cod) => {
            collect_pred_params(dom, pn, pb)?;
            collect_pred_params(cod, pn, pb)
        }
        Type::Refine { base, pred, .. } => {
            let mut ticks = Vec::new();
            collect_ticks(pred, &mut ticks);
            for t in ticks {
                if let Some(i) = pn.iter().position(|x| *x == t) {
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
            // a refinement's base may itself be compound (nested arrows etc.).
            collect_pred_params(base, pn, pb)
        }
    }
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
        S::If(c, a, b) => {
            collect_ticks(c, acc);
            collect_ticks(a, acc);
            collect_ticks(b, acc);
        }
        S::Match(scrut, arms) => {
            collect_ticks(scrut, acc);
            for arm in arms {
                if let Some(g) = &arm.guard {
                    collect_ticks(g, acc);
                }
                collect_ticks(&arm.body, acc);
            }
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
                if let Some((e, c)) = &b.image {
                    collect_ticks(e, acc);
                    collect_ticks(c, acc);
                }
            }
            collect_ticks(body, acc);
        }
        S::SolveBy(g, l) => {
            collect_ticks(g, acc);
            collect_ticks(l, acc);
        }
        S::IntLit(_) | S::RealLit(_) | S::Bool(_) => {}
    }
}
