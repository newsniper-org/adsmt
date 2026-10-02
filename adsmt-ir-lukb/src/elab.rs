//! Elaborate a parsed lu-kb-successor [`Module`] into a **kernel-checked**
//! [`Env`] + the obligation/hypothesis term lists. Every elaborated term is
//! re-checked by the adsmt-ir kernel (each `axiom`/`assume`/`goal` body must be
//! a closed `Prop`), so a face bug can only ever yield a [`FaceError`], never a
//! trusted ill-typed term — the same firewall as the SMT-LIB / ASP faces.

use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;

use adsmt_class::resolve::{ClassGoal, ResolutionResult, Resolver};
use adsmt_class::{Instance, InstanceDb, LawProver, Premise};
use adsmt_ir::theory;
use adsmt_ir::{
    Ctx, Env, Modality, Term as K, TriggerMap, Univ, as_const_app, declare_inductive, define,
    infer, is_def_eq, peel_pis, postulate, record_triggers, shift, subst_top, whnf,
};

use crate::ast::{Arm, BinOp, Binder, Ctor, Item, Module, PatArg, Pattern, Term as S, Type};
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
    /// One entry per refinement-typed `const`: the constant's name and the
    /// refinement predicate instantiated at it, `φ[v := c]`.
    ///
    /// `const c: {v: T | φ}` postulates `c : T` and ASSERTS `φ[v := c]` — an
    /// assertion that `T`'s subset is inhabited. When it is not, the assumption
    /// set is contradictory and every goal in the module comes back `unsat`,
    /// which reads as "proved" and is vacuous:
    ///
    /// ```text
    /// const x: {y: Int | y > 0 and y < 0}
    /// goal: x = x        ⤳  unsat        (and so would `goal: false`)
    /// ```
    ///
    /// The elaborator cannot decide emptiness — that is `∃y. φ`, an SMT
    /// question — so it hands each predicate to whoever has a solver. Kept
    /// separate from [`Self::hypotheses`], where these also appear: this is a
    /// list of things to CHECK, not a second assumption set.
    pub refinement_witnesses: Vec<(String, K)>,
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
    Ok(Elaborated {
        env: e.env,
        hypotheses: e.hyps,
        goals: e.goals,
        triggers: e.triggers,
        refinement_witnesses: e.refinement_witnesses,
    })
}

const RESERVED_BUILTINS: &[&str] = &[
    "Int", "Real", "Nat", "WNat", "Bool", "Prop", "abs", "div", "mod", "to_real", "pow", "prime", "odd",
];

fn check_reserved_name(name: &str) -> Result<(), FaceError> {
    if RESERVED_BUILTINS.contains(&name) {
        return Err(FaceError::Unsupported(format!(
            "constant `{name}` is a reserved builtin and cannot be declared or shadowed"
        )));
    }
    // Not just digit-LEADING. A backtick-quoted identifier takes any characters,
    // so `\`-3\`` and `\`2.5\`` slipped through — and the kernel's convention is
    // that a numeral spelling IS that number, so those became literals. Measured:
    // `const \`-3\`: S` and `const \`-4\`: S` made `not(\`-3\` = \`-4\`)` answer
    // `unsat` (the same program with ordinary names answers `sat`), and
    // `const \`-5\`: Int` made `\`-5\` < 100` answer `unsat` for a constant the
    // user declared opaque.
    if adsmt_ir::is_numeral_spelling(name) {
        return Err(FaceError::Unsupported(format!(
            "identifier `{name}` is spelled like a numeral, which names a literal"
        )));
    }
    if name.starts_with(|c: char| c.is_ascii_digit()) {
        return Err(FaceError::Unsupported(format!(
            "identifier `{name}` cannot start with a digit"
        )));
    }
    Ok(())
}

struct Elab<'p> {
    env: Env,
    hyps: Vec<K>,
    goals: Vec<K>,
    /// See [`Elaborated::refinement_witnesses`].
    refinement_witnesses: Vec<(String, K)>,
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
        // NO `Acc` / `acc` prelude. The termination-proof branch is not
        // implemented (a `decreases` clause is refused), and what was installed
        // for it was worse than nothing: `acc : Π(A) Π(R) Π(x). Prop → Acc A R x`
        // makes the accessibility predicate inhabited from ANY proposition —
        // `false` included — so it carried no well-foundedness content while
        // looking like an obligation. Every lu-kb environment got that pair.
        //
        // When the branch lands, `Acc` must be a real INDUCTIVE, admitted with
        // the introduction rule `(Π y. R y x → Acc A R y) → Acc A R x`, so that
        // inhabiting it means something. Postulating a weaker one in advance
        // only adds a trust source. See LUKB_SUCCESSOR_SURFACE.md §11.
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
            refinement_witnesses: Vec::new(),
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
                check_reserved_name(s)?;
                postulate(&mut self.env, s, K::type_(0))?;
                self.grant_eq(s); // owner ruling 2: every declared sort carries Eq
            }
            Item::Const(x, ty) => {
                check_reserved_name(x)?;
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
                        self.refinement_witnesses.push((x.clone(), phi.clone()));
                        self.hyps.push(phi);
                    }
                } else {
                    let kty = self.elab_type(ty)?;
                    postulate(&mut self.env, x, kty)?;
                }
            }
            Item::Fn { name, params, ret, body, rec, decreases, mutual } => {
                check_reserved_name(name)?;
                if mutual.is_empty() {
                    self.elab_fn(name, params, ret, body, *rec, decreases.as_ref())?;
                } else {
                    let mut group = vec![(name.clone(), params.clone(), ret.clone(), body.clone(), *rec, decreases.clone())];
                    for (mname, mparams, mret, mdec, mbody) in mutual {
                        group.push((mname.clone(), mparams.clone(), mret.clone(), mbody.clone(), *rec, mdec.clone()));
                    }
                    self.elab_mutual_fn(&group)?;
                }
            }
            Item::Data { name, ctors, mutual } => {
                if mutual.is_empty() {
                    check_reserved_name(name)?;
                    // Inhabitation is NOT checked here. It is a property of the
                    // whole declaration set — a cycle can run through a sibling
                    // (`data A = a(B) and B = b(A)`) — and the lowering is where
                    // the whole set is visible and where the constraint actually
                    // bites (an empty CIC type must not become a non-empty SMT
                    // sort). Duplicating a per-member approximation here is what
                    // let mutual groups through in the first place; the lowering
                    // now owns it, once, as a least fixed point.
                    for (cname, fields) in ctors {
                        check_reserved_name(cname)?;
                        for (selname, _) in fields {
                            if let Some(sn) = selname {
                                check_reserved_name(sn)?;
                            }
                        }
                    }
                    let mut kctors: Vec<(String, Vec<K>)> = Vec::with_capacity(ctors.len());
                    let mut named_fields: Vec<(String, String, usize, K)> = Vec::new();
                    for (cname, fields) in ctors {
                        let mut ftypes = Vec::with_capacity(fields.len());
                        for (i, (selname, fty)) in fields.iter().enumerate() {
                            self.ensure_ring_sorts(fty)?;
                            let kty = self.elab_field_type(fty, name)?;
                            if let Some(sn) = selname {
                                named_fields.push((sn.clone(), cname.clone(), i, kty.clone()));
                            }
                            ftypes.push(kty);
                        }
                        kctors.push((cname.clone(), ftypes));
                    }
                    declare_inductive(&mut self.env, name, Vec::new(), Univ::Type(0), kctors)?;
                    self.grant_eq_data(name)?;
                    for (field, cname, i, kty) in named_fields {
                        let canonical = format!("{cname}!sel{i}");
                        if self.env.lookup(&canonical).is_none() {
                            postulate(&mut self.env, &canonical, K::arrow(K::cnst(name), kty))?;
                        }
                        match self.selector_fields.entry(field) {
                            Entry::Vacant(v) => {
                                v.insert(Some((name.clone(), canonical)));
                            }
                            Entry::Occupied(mut o) => {
                                o.insert(None);
                            }
                        }
                    }
                } else {
                    let mut all_members: Vec<(&str, &Vec<Ctor>)> = vec![(name.as_str(), ctors)];
                    for (mname, mctors) in mutual {
                        all_members.push((mname.as_str(), mctors));
                    }
                    let all_names: Vec<&str> = all_members.iter().map(|(n, _)| *n).collect();
                    for (mname, mctors) in &all_members {
                        check_reserved_name(mname)?;
                        for (cname, fields) in *mctors {
                            check_reserved_name(cname)?;
                            for (selname, _) in fields {
                                if let Some(sn) = selname {
                                    check_reserved_name(sn)?;
                                }
                            }
                        }
                    }
                    let mut mut_members: Vec<adsmt_ir::MutualMember> = Vec::with_capacity(all_members.len());
                    let mut all_named_fields: Vec<(String, Vec<(String, String, usize, K)>)> = Vec::new();
                    for (mname, mctors) in &all_members {
                        let mut kctors: Vec<(String, Vec<K>, Vec<K>)> = Vec::with_capacity(mctors.len());
                        let mut named_fields: Vec<(String, String, usize, K)> = Vec::new();
                        for (cname, fields) in *mctors {
                            let mut ftypes = Vec::with_capacity(fields.len());
                            for (i, (selname, fty)) in fields.iter().enumerate() {
                                self.ensure_ring_sorts(fty)?;
                                let kty = self.elab_mutual_field_type(fty, &all_names)?;
                                if let Some(sn) = selname {
                                    named_fields.push((sn.clone(), cname.clone(), i, kty.clone()));
                                }
                                ftypes.push(kty);
                            }
                            kctors.push((cname.clone(), ftypes, Vec::new()));
                        }
                        mut_members.push(adsmt_ir::MutualMember {
                            name: mname.to_string(),
                            params: Vec::new(),
                            indices: Vec::new(),
                            sort: Univ::Type(0),
                            ctors: kctors,
                        });
                        all_named_fields.push((mname.to_string(), named_fields));
                    }
                    adsmt_ir::declare_mutual(&mut self.env, mut_members)?;
                    for (mname, named_fields) in all_named_fields {
                        self.grant_eq_data(&mname)?;
                        for (field, cname, i, kty) in named_fields {
                            let canonical = format!("{cname}!sel{i}");
                            if self.env.lookup(&canonical).is_none() {
                                postulate(&mut self.env, &canonical, K::arrow(K::cnst(&mname), kty))?;
                            }
                            match self.selector_fields.entry(field) {
                                Entry::Vacant(v) => {
                                    v.insert(Some((mname.clone(), canonical)));
                                }
                                Entry::Occupied(mut o) => {
                                    o.insert(None);
                                }
                            }
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
    /// Wrap `lam` in the kernel `fix`, choosing the decreasing argument.
    ///
    /// The surface does not say WHICH parameter decreases, so every value
    /// parameter is tried and the KERNEL decides: `infer` on a `Fix` runs both
    /// the "is this argument's type inductive" check and `guard::guard_ok`, so
    /// a candidate that type-checks is one the guard accepted. First hit wins.
    /// (`'p` binders lead `ty`, so value parameter `j` is argument
    /// `pred_count + j`.)
    ///
    /// Failure is the **(d-2) branch not being implemented**, not a claim that
    /// the function diverges — `guard_ok` is deliberately conservative and
    /// rejects terminating functions it cannot see through (`f(n - 1)` on an
    /// `Int`, two arguments decreasing alternately, a measure that does not
    /// follow the term structure). The message has to say that, or a user
    /// reads a completeness limit as a soundness verdict.
    fn build_fix(
        &self,
        name: &str,
        ty: &K,
        lam: K,
        pred_count: usize,
        value_count: usize,
    ) -> Result<K, FaceError> {
        let mut first_err: Option<String> = None;
        for j in 0..value_count {
            let cand = K::fix(pred_count + j, ty.clone(), lam.clone());
            match infer(&self.env, &Ctx::new(), &cand) {
                Ok(_) => return Ok(cand),
                Err(e) => {
                    if first_err.is_none() {
                        first_err = Some(e.to_string());
                    }
                }
            }
        }
        let why = first_err.unwrap_or_else(|| "it abstracts no argument".to_string());
        Err(unsupported(format!(
            "`rec fn {name}`: no parameter is structurally decreasing, so the \
             kernel's `fix` guard rejected it ({why}). The guard is conservative \
             — a terminating function can fail it — but the branch that admits \
             those on a termination proof is not implemented yet"
        )))
    }

    fn elab_fn(
        &mut self,
        name: &str,
        params: &[(Vec<String>, Type)],
        ret: &Type,
        body: &Option<S>,
        rec: bool,
        decreases: Option<&S>,
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
                if rec {
                    return Err(unsupported(format!(
                        "`rec fn {name}` has no body — `rec` marks a recursive \
                         DEFINITION, and a signature has nothing to recurse into"
                    )));
                }
                postulate(&mut self.env, name, ty.clone())?;
            }
            Some(b) => {
                // Does the body call `name`? That is what makes it recursive,
                // and recursion is admitted only under `rec` — so an
                // unmarked self-reference is reported AS a self-reference
                // rather than surfacing as `unknown function symbol` (which
                // is what the caller saw before: `name` is genuinely not in
                // `env` yet at this point).
                let self_ref = mentions_surface(b, name);
                if self_ref && !rec {
                    return Err(unsupported(format!(
                        "`{name}` calls itself; a recursive definition requires \
                         the `rec` modifier (write `rec fn {name}(…)`)"
                    )));
                }
                // The recursive function itself is the OUTERMOST context entry
                // when there is one: `Fix` reads `body` with `f : ty` at
                // `Bound(0)`, i.e. bound outside the parameter λs.
                let mut ctx: Vec<(String, K)> = Vec::new();
                if self_ref {
                    ctx.push((name.to_string(), ty.clone()));
                }
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
                if self_ref {
                    if decreases.is_some() {
                        // The rule is `admit(rec f) ⟸ structural(f) ∨
                        // proves_termination(f)`, and the SECOND branch does not
                        // exist yet. What used to happen here was worse than not
                        // having it: the clause's sort was checked and then the
                        // function was `postulate`d, so `lam` — the body the user
                        // wrote — was computed and thrown away. `f` became an
                        // opaque constant, and every goal that was true BECAUSE of
                        // the definition came back a confident countermodel:
                        //
                        //     rec fn f(n: Int): Int decreases [<acc …>] =
                        //         if n = 0 then 0 else f(n - 1)
                        //     goal g: f(0) = 0        ⤳  smt definite-sat
                        //
                        // Two more things followed from `postulate` never seeing
                        // the body. It skips `check`, so a body whose sort
                        // contradicts the return type was admitted. And it turned
                        // a REJECTION into an admission: the bare form of that
                        // same program is required to be refused
                        // (`non_structural_recursion_is_rejected_…`), and adding
                        // the clause laundered it through.
                        //
                        // The gate it did apply was vacuous anyway — `acc` builds
                        // an accessibility witness from ANY proposition, `false`
                        // included, so `Acc` carried no well-foundedness content.
                        //
                        // Fail-first until the real branch lands: `Acc` declared
                        // as a genuine inductive with the introduction rule
                        // `(Π y. R y x → Acc A R y) → Acc A R x`, a
                        // well-foundedness license for `R`, and a decrease
                        // obligation the engine discharges — with the definition
                        // REFUSED when it cannot. See
                        // docs/design/LUKB_SUCCESSOR_SURFACE.md §11.
                        return Err(unsupported(format!(
                            "`rec fn {name}`: a `decreases` clause needs the \
                             termination-proof branch, which is not implemented yet \
                             (only structural recursion is admitted). Removing the \
                             clause makes `{name}` take the structural branch."
                        )));
                    }
                    let value = self.build_fix(name, &ty, lam, pred_sorts.len(), vsorts.len())?;
                    define(&mut self.env, name, ty.clone(), value)?;
                } else {
                    define(&mut self.env, name, ty.clone(), lam)?;
                }
            }
        }
        // 6. the contract obligation — only when the RETURN is refined.
        if let Type::Refine { var: rv, pred: rp, .. } = ret {
            // result = g('p…, x…); for a def it δ-unfolds to the body.
            let mut result_args: Vec<S> = pred_names.iter().map(|n| S::Var(n.clone())).collect();
            result_args.extend(vnames.iter().map(|n| S::Var(n.clone())));
            let result = S::Call(name.to_string(), result_args);
            let post = self.subst(rp, rv, &result);
            // precondition: the deduped conjunction of every param refinement,
            // each instantiated at its parameter name (idempotence dedup).
            let mut pre: Vec<S> = Vec::new();
            for (vn, refine) in vnames.iter().zip(&vrefine) {
                if let Some((rvar, rpred)) = refine {
                    pre.push(self.subst(rpred, rvar, &S::Var(vn.clone())));
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

    fn elab_mutual_field_type(&self, ty: &Type, data_names: &[&str]) -> Result<K, FaceError> {
        match ty {
            Type::Name(n) if data_names.contains(&n.as_str()) => Ok(K::cnst(n.clone())),
            _ => self.elab_type(ty),
        }
    }

    fn elab_mutual_fn(
        &mut self,
        group: &[(String, Vec<(Vec<String>, Type)>, Type, Option<S>, bool, Option<S>)],
    ) -> Result<(), FaceError> {
        let all_names: Vec<&str> = group.iter().map(|(n, ..)| n.as_str()).collect();
        for name in &all_names {
            check_reserved_name(name)?;
        }

        // Pass 1: compute signatures and register in env
        let mut signatures: Vec<(String, K)> = Vec::with_capacity(group.len());
        for (name, params, ret, ..) in group {
            let mut vsorts = Vec::new();
            for (names, ty) in params {
                let kty = self.elab_type(ty)?;
                for _ in names {
                    vsorts.push(kty.clone());
                }
            }
            let kret = self.elab_type(ret)?;
            let mut ty = kret;
            for s in vsorts.iter().rev() {
                ty = K::arrow(s.clone(), ty);
            }
            postulate(&mut self.env, name, ty.clone())?;
            signatures.push((name.clone(), ty));
        }

        // Pass 2: elaborate bodies, then admit the whole group at once.
        let mut defs: Vec<(String, K, K)> = Vec::with_capacity(group.len());
        for (name, params, ret, body, rec, dec) in group {
            let Some(b) = body else {
                continue;
            };
            let mentions_group = all_names.iter().any(|gn| mentions_surface(b, gn));
            if mentions_group && !rec {
                return Err(unsupported(format!(
                    "`{name}` calls a mutual function; recursion requires the `rec` modifier"
                )));
            }
            let mut ctx: Vec<(String, K)> = Vec::new();
            for (names, ty) in params {
                let kty = self.elab_type(ty)?;
                for n in names {
                    ctx.push((n.clone(), kty.clone()));
                }
            }
            let kbody = self.elab_term(&mut ctx, b)?;
            let kret = self.elab_type(ret)?;
            let body_ty = infer(&self.env, &kernel_ctx(&ctx), &kbody)?;
            if !is_def_eq(&self.env, &body_ty, &kret) {
                return Err(unsupported(format!(
                    "`{name}` body has sort `{body_ty}`, expected return sort `{kret}`"
                )));
            }
            if dec.is_some() {
                // Same rule as the single-function path: the termination-proof
                // branch does not exist, so the clause is refused rather than
                // validated-and-ignored. Here it was strictly decorative — the
                // sort was checked and then execution fell through, so a user
                // writing a termination annotation got neither a proof nor a
                // diagnostic.
                return Err(unsupported(format!(
                    "`rec fn {name}`: a `decreases` clause needs the \
                     termination-proof branch, which is not implemented yet \
                     (only structural recursion is admitted)."
                )));
            }
            let mut vsorts = Vec::new();
            for (names, ty) in params {
                let kty = self.elab_type(ty)?;
                for _ in names {
                    vsorts.push(kty.clone());
                }
            }
            let mut lam = kbody;
            for s in vsorts.iter().rev() {
                lam = K::lam(s.clone(), lam);
            }
            let (_, ty) = signatures.iter().find(|(n, _)| n == name).unwrap();
            defs.push((name.clone(), ty.clone(), lam));
        }
        // The group goes in through the CHECKED admitter, all at once.
        //
        // It used to go in through `Env::declare` — the raw, unchecked
        // insertion the kernel documents as "prefer the checked admitters" —
        // one member at a time. That skipped two things. The admission journal,
        // so the group could never be banked (`bank_encode`'s self-check
        // rejects an env its journal cannot rebuild). And, far worse, every
        // termination check: `f x = g x, g x = f x` was admitted, and the
        // kernel's head reduction then had no normal form to find. It hung; the
        // variant with the call under an argument overflowed the stack.
        //
        // `define_mutual` type-checks every body against its signature with the
        // whole group in scope, and then requires the group to be structurally
        // decreasing — the same rule, and the same conservatism, that a single
        // `rec fn` already meets through the kernel's `fix` guard. A group it
        // cannot prove decreasing is REFUSED, not postulated: postulating would
        // throw the bodies away and turn a goal that is true by definition into
        // a confident countermodel (the defect `decreases` had at 3efcc89).
        if !defs.is_empty() {
            adsmt_ir::define_mutual(&mut self.env, &defs)?;
        }
        Ok(())
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
                None => Err(unsupported(format!(
                    "unknown sort `{n}` — a module elaborates top to bottom, so \
                     `{n}` must be declared ABOVE its first use (two datatypes \
                     that reference each other need the `and` group form)"
                ))),
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
            // positivity hypothesis / fn pre-/post-condition / a quantifier
            // binder's domain guard, see `membership_guard`), handled by the
            // callers that own the binding name — never here. A caller that
            // binds a name at a refinement type and does NOT take the
            // predicate back has dropped a constraint; in a binder position
            // that is unsound in both directions.
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

    /// The domain restriction a quantifier binder of type `ty` places on the
    /// bound value `x`, as a surface guard; `None` when `ty` restricts nothing.
    ///
    /// * `{v: T | φ}` — `T`'s own restriction, and `let v = x in φ`. A `let`
    ///   rather than a substitution: `φ` may bind names of its own, and a
    ///   textual `v := x` would be captured under them.
    /// * `A -> B` — `forall a: A. <B's restriction on x(a)>`, with `a` fresh
    ///   and bound at `A` itself, so a refinement on the domain guards that
    ///   inner quantifier the same way. A refined domain alone restricts
    ///   nothing about `x`: what a function does outside it is unconstrained
    ///   either way.
    /// * a plain sort — `None`.
    ///
    /// `later` is this binder's name and every name the same quantifier binds
    /// after it. The guard is elaborated where they are all in scope, but `φ`
    /// was written where they were not, so a `φ` that mentions one would be
    /// silently re-bound to the quantified variable (`forall x: {v: Int | v >
    /// x}` would compare `x` with itself). That is refused, not guessed.
    fn membership_guard(&mut self, x: S, ty: &Type, later: &[&str]) -> Result<Option<S>, FaceError> {
        if let Some((var, n)) = refinement_capture(ty, later) {
            return Err(unsupported(format!(
                "the refinement over `{var}` mentions `{n}`, which this quantifier binds \
                 at or after the refined binder; rename one of them"
            )));
        }
        Ok(self.membership_guard_unchecked(x, ty))
    }

    fn membership_guard_unchecked(&mut self, x: S, ty: &Type) -> Option<S> {
        match ty {
            Type::Refine { var, base, pred } => {
                let own = S::Let(var.clone(), Box::new(x.clone()), pred.clone());
                Some(match self.membership_guard_unchecked(x, base) {
                    Some(inner) => S::Bin(BinOp::And, Box::new(inner), Box::new(own)),
                    None => own,
                })
            }
            Type::Arrow(dom, cod) => {
                let a = format!("!arg.{}", self.fresh_n);
                self.fresh_n += 1;
                let applied = S::App(Box::new(x), vec![S::Var(a.clone())]);
                let g = self.membership_guard_unchecked(applied, cod)?;
                let binder = Binder {
                    names: vec![a],
                    ty: (**dom).clone(),
                    constraint: None,
                    range: None,
                    refinement: None,
                    image: None,
                };
                Some(S::Forall(vec![binder], Box::new(g), Vec::new()))
            }
            Type::Name(_) | Type::App(..) => None,
        }
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
            S::App(f, args) => {
                let kf = self.elab_term(ctx, f)?;
                let kargs: Vec<K> =
                    args.iter().map(|a| self.elab_term(ctx, a)).collect::<Result<_, _>>()?;
                let mut cur = kf;
                for arg in kargs {
                    let w = whnf(&self.env, &cur);
                    if let adsmt_ir::TermKind::Lam(_, body) = w.kind() {
                        cur = subst_top(body, &arg);
                    } else {
                        cur = K::app(cur, arg);
                    }
                }
                Ok(cur)
            }
            S::Lam { name, params, ret, body, rec } => {
                self.elab_lambda(ctx, name.as_deref(), params, ret, body, *rec)
            }
        }
    }
    fn elab_lambda(
        &mut self,
        ctx: &mut Vec<(String, K)>,
        name: Option<&str>,
        params: &[(Vec<String>, Type)],
        ret: &Type,
        body: &S,
        rec: bool,
    ) -> Result<K, FaceError> {
        let fn_name = name.unwrap_or("!self");
        let self_ref = mentions_surface(body, fn_name);
        if self_ref && !rec {
            return Err(unsupported(format!(
                "anonymous lambda calls `{fn_name}`; recursion requires the `rec` modifier"
            )));
        }

        let mut vnames: Vec<String> = Vec::new();
        let mut vsorts: Vec<K> = Vec::new();
        for (names, ty) in params {
            let kty = self.elab_type(ty)?;
            for n in names {
                vnames.push(n.clone());
                vsorts.push(kty.clone());
            }
        }
        let kret = self.elab_type(ret)?;

        let mut fn_ty = kret.clone();
        for s in vsorts.iter().rev() {
            fn_ty = K::arrow(s.clone(), fn_ty);
        }

        let saved_len = ctx.len();
        if self_ref {
            ctx.push((fn_name.to_string(), fn_ty.clone()));
        }
        for (n, s) in vnames.iter().zip(&vsorts) {
            ctx.push((n.clone(), s.clone()));
        }
        let mut term = self.elab_term(ctx, body)?;
        ctx.truncate(saved_len);

        for s in vsorts.iter().rev() {
            term = K::lam(s.clone(), term);
        }
        if self_ref {
            term = self.build_fix(fn_name, &fn_ty, term, 0, vsorts.len())?;
        }

        if ctx.is_empty() {
            let lift_name = self.fresh_name();
            let lam_ty = infer(&self.env, &Ctx::new(), &term)?;
            define(&mut self.env, &lift_name, lam_ty, term)?;
            Ok(K::cnst(lift_name))
        } else {
            Ok(term)
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
        for (bi, b) in binders.iter().enumerate() {
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
            // a binder whose TYPE is (or ends in) a refinement — `m: {v: T | φ}`,
            // `f: A -> {r: B | ψ}` — restricts the domain exactly as the
            // `{m: T | φ}` binder form does. `elab_type` keeps only the base
            // sort, so the restriction has to come back here as a guard; it
            // used to be dropped, and the quantifier then ranged over all of
            // `T`:
            //
            //   goal: forall m: {v: Int | v > 5}. m > 5      ⤳  definite-sat
            //
            // a confident countermodel (`m = 0`) to a valid goal. In an axiom
            // the same drop strengthens the assumption (`forall m: {v | v > 5}.
            // f(m) > 0` became `forall m. f(m) > 0`), which proves `f(0) > 0`.
            for (i, name) in b.names.iter().enumerate() {
                let later: Vec<&str> = b.names[i..]
                    .iter()
                    .chain(binders[bi + 1..].iter().flat_map(|l| l.names.iter()))
                    .map(String::as_str)
                    .collect();
                if let Some(g) = self.membership_guard(S::Var(name.clone()), &b.ty, &later)? {
                    guards.push(g);
                }
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
        // unfold image-binder definitions (`y := f(x)`) in the body, and in
        // the guards: they are elaborated in this same window, where `y` is
        // not in the context, so a guard naming `y` would otherwise reach
        // whatever OUTER `y` there is.
        let body_owned;
        let body = if body_substs.is_empty() {
            body
        } else {
            // An image variable spelled like another name this quantifier
            // binds would make the sequential unfolding below ambiguous.
            let bound = quant_bound(binders);
            for (y, _) in &body_substs {
                if bound.iter().filter(|n| **n == y).count() > 1 {
                    ctx.truncate(depth0);
                    return Err(unsupported(format!(
                        "the image variable `{y}` is bound twice by one quantifier; rename one"
                    )));
                }
            }
            let mut b = body.clone();
            for (y, e) in &body_substs {
                b = self.subst(&b, y, e);
                for g in &mut guards {
                    *g = self.subst(g, y, e);
                }
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
                        p = self.subst(&p, y, e);
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
        // A LOCAL binding always wins over a builtin name. The builtin arms
        // below match on the spelling alone, so a `fn` parameter, a lambda
        // parameter or a quantifier binder named `abs`/`to_real`/`nop`/… was
        // silently replaced by the theory constant. Measured:
        //
        //     fn ap(abs: Int -> Int, x: Int): Int = abs(x)
        //     fn g(y: Int): Int = y + 1
        //     goal: ap(g, 3) = 4                            sat
        //
        // with the identical program renaming the parameter to `gg` answering
        // `unsat`. The `_` arm below already consults `ctx` — the builtin arms
        // just ran first. (A TOP-LEVEL name cannot shadow: `check_reserved_name`
        // refuses those at declaration. Only binders reach here.)
        let locally_bound = ctx.iter().any(|(n, _)| n == name);
        // `nop(x)` — the trivial predicate. It is polymorphic (`Π(T).T→Prop`), so
        // infer the implicit type argument from `x`'s sort: `nop[typeof(x)](x)`.
        if name == "nop" && args.len() == 1 && !locally_bound {
            let kx = self.elab_term(ctx, &args[0])?;
            let sort = infer(&self.env, &kernel_ctx(ctx), &kx)?;
            return Ok(K::apps(K::cnst("nop"), [sort, kx]));
        }
        let kargs: Vec<K> =
            args.iter().map(|a| self.elab_term(ctx, a)).collect::<Result<_, _>>()?;
        // built-in function names map to the arithmetic prelude constants;
        // anything else must be a declared symbol.
        let head = match name {
            "pow" if !locally_bound => theory::POW,
            "odd" if !locally_bound => theory::ODD,
            "prime" if !locally_bound => theory::PRIME,
            "abs" if !locally_bound => theory::INT_ABS,
            "div" if !locally_bound => theory::INT_DIV,
            "mod" if !locally_bound => theory::INT_MOD,
            "to_real" if !locally_bound => theory::INT2REAL,
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
                    // Declaration order is significant here, and saying only
                    // "unknown" hides that: a module elaborates in ONE pass, so
                    // when an item is read the environment holds exactly the
                    // items before it. A name that IS declared, later in the
                    // same module, reads identically to one that is not.
                    return Err(unsupported(format!(
                        "unknown function symbol `{name}` — a module elaborates \
                         top to bottom, so `{name}` must be declared ABOVE its \
                         first use (a definition that calls itself needs `rec`; \
                         two that call each other need the `and fn` group form)"
                    )));
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
    /// A bare-name pattern that is no constructor of the scrutinee's type is
    /// a catch-all binder — unless the name is a constructor of SOME type.
    /// That spelling is refused: [`subst_surface`] cannot see the scrutinee's
    /// type and reads every constructor name in pattern position as a
    /// constructor, so admitting it would let the two disagree on what the
    /// arm binds.
    fn catch_all_is_no_ctor(&self, n: &str) -> Result<(), FaceError> {
        match self.env.ctor_of(n) {
            Some((ind, _)) => Err(unsupported(format!(
                "the catch-all pattern `{n}` is spelled like a constructor of `{ind}`; rename the binder"
            ))),
            None => Ok(()),
        }
    }

    /// [`subst_surface`] against this environment's constructor table.
    fn subst(&self, t: &S, from: &str, to: &S) -> S {
        subst_surface(t, from, to, &|n| self.env.ctor_of(n).is_some())
    }

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
                Pattern::Bind(n) if !is_ctor(n) => self.catch_all_is_no_ctor(n)?,
                Pattern::Bind(n) => {
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
                Pattern::Wild => {}
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
                        self.subst(&arm.body, x, scrut),
                        arm.guard.as_ref().map(|g| self.subst(g, x, scrut)),
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
                Pattern::Bind(x) => {
                    self.catch_all_is_no_ctor(x)?;
                    (
                        self.subst(&arm.body, x, scrut),
                        arm.guard.as_ref().map(|g| self.subst(g, x, scrut)),
                    )
                }
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
                Pattern::Bind(x) => {
                    self.catch_all_is_no_ctor(x)?;
                    (
                        self.subst(&arm.body, x, scrut),
                        arm.guard.as_ref().map(|g| self.subst(g, x, scrut)),
                    )
                }
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

/// The first refinement predicate inside `ty` (at any depth: a refined base,
/// either side of an arrow) that mentions one of `names` other than its own
/// bound variable — as `(that variable, the name)`. See
/// [`Elab::membership_guard`].
fn refinement_capture(ty: &Type, names: &[&str]) -> Option<(String, String)> {
    match ty {
        Type::Name(_) => None,
        Type::App(_, args) => args.iter().find_map(|a| refinement_capture(a, names)),
        Type::Arrow(dom, cod) => {
            refinement_capture(dom, names).or_else(|| refinement_capture(cod, names))
        }
        Type::Refine { var, base, pred } => names
            .iter()
            .find(|n| **n != var && mentions_surface(pred, n))
            .map(|n| (var.clone(), (*n).to_string()))
            .or_else(|| refinement_capture(base, names)),
    }
}

/// The names one quantifier binds over ALL of its parts. The elaborator puts
/// every binder in the context before it elaborates any guard, so a range
/// bound, a constraint's right-hand side, a refinement predicate, a refined
/// type and the body all see every binder. An image binder `{y = f(x) | c}`
/// binds both `y` and its preimage `x`.
fn quant_bound(bs: &[Binder]) -> Vec<&str> {
    let mut out = Vec::new();
    for b in bs {
        out.extend(b.names.iter().map(String::as_str));
        if let Some((e, _)) = &b.image
            && let S::Call(_, args) = &**e
            && let [S::Var(x)] = args.as_slice()
        {
            out.push(x.as_str());
        }
    }
    out
}

/// Does `name` occur FREE in the surface term `t`?
///
/// Used to decide whether a `fn` body is recursive. Its scoping is the one
/// [`subst_surface`] uses, except that a bare-name match pattern always counts
/// as a binder here (no constructor table is at hand). That can only hide a
/// self-reference, and a hidden one then fails to elaborate as an unknown
/// symbol; it never admits a wrong definition.
fn mentions_surface(t: &S, name: &str) -> bool {
    let go = |x: &S| mentions_surface(x, name);
    match t {
        S::Var(n) => n == name,
        S::IntLit(_) | S::RealLit(_) | S::Bool(_) => false,
        S::Not(a) | S::Neg(a) => go(a),
        S::Bin(_, a, b) | S::SolveBy(a, b) => go(a) || go(b),
        // A call's HEAD is the recursive occurrence we are looking for.
        S::Call(f, args) => f == name || args.iter().any(&go),
        S::If(c, a, b) => go(c) || go(a) || go(b),
        S::Let(x, e, body) => go(e) || (x != name && go(body)),
        S::Match(scrut, arms) => {
            go(scrut)
                || arms.iter().any(|arm| {
                    let shadow = match &arm.pattern {
                        Pattern::Bind(n) => n == name,
                        Pattern::Ctor(_, pargs) => {
                            pargs.iter().any(|p| matches!(p, PatArg::Bind(n) if n == name))
                        }
                        Pattern::Wild
                        | Pattern::Bool(_)
                        | Pattern::IntLit(_)
                        | Pattern::RealLit(_) => false,
                    };
                    if shadow {
                        return false;
                    }
                    arm.guard.as_ref().is_some_and(&go) || go(&arm.body)
                })
        }
        S::Forall(bs, body, trigs) | S::Exists(bs, body, trigs) => {
            !quant_bound(bs).contains(&name)
                && (bs.iter().any(|b| binder_mentions(b, name))
                    || go(body)
                    || trigs.iter().flatten().any(&go))
        }
        S::App(f, args) => go(f) || args.iter().any(&go),
        S::Lam { name: opt_n, params, ret, body, .. } => {
            let bound = opt_n.as_deref() == Some(name)
                || params.iter().any(|(ns, _)| ns.iter().any(|n| n == name));
            !bound
                && (go(body)
                    || type_mentions(ret, name)
                    || params.iter().any(|(_, ty)| type_mentions(ty, name)))
        }
    }
}

/// Does `name` occur free in one binder's own sub-terms (its type's
/// refinements, range, constraint, refinement, image)? The caller has
/// already checked that the quantifier does not bind `name`.
fn binder_mentions(b: &Binder, name: &str) -> bool {
    let go = |x: &S| mentions_surface(x, name);
    type_mentions(&b.ty, name)
        || b.range.as_ref().is_some_and(|(lo, hi)| go(lo) || go(hi))
        || b.constraint.as_ref().is_some_and(|(_, rhs)| go(rhs))
        || b.refinement.as_ref().is_some_and(|p| go(p))
        || b.image.as_ref().is_some_and(|(e, c)| go(e) || go(c))
}

/// Does `name` occur free in a refinement predicate inside `ty`?
fn type_mentions(ty: &Type, name: &str) -> bool {
    match ty {
        Type::Name(_) => false,
        Type::App(_, args) => args.iter().any(|a| type_mentions(a, name)),
        Type::Arrow(d, c) => type_mentions(d, name) || type_mentions(c, name),
        Type::Refine { var, base, pred } => {
            type_mentions(base, name) || (var != name && mentions_surface(pred, name))
        }
    }
}

/// Capture-avoiding substitution of the free surface variable `from` by the
/// term `to`. It instantiates a refinement's bound value at an argument or a
/// result, unfolds an image binder's `y := f(x)`, and names a match scrutinee
/// by its catch-all binder.
///
/// Scoping follows the elaborator, which is what gives a name its meaning:
/// - `let x = e in b`: `e` outside, `b` under `x`.
/// - a quantifier: every part (range bounds, constraint right-hand sides,
///   refinement predicates, refined types, an image binder's `e`/`c`, the body,
///   the triggers) under all of its binders ([`quant_bound`]).
/// - a match arm: under its pattern's binders. A bare-name pattern is a binder
///   only when `is_ctor` says the name is no constructor; the match elaborator
///   refuses a catch-all spelled like a constructor, so the two agree.
/// - a lambda: its body and its own types under its name and parameters.
/// - a refinement type `{v: T | φ}`: `φ` under `v`.
///
/// A binder that would capture a name `to` mentions is renamed first, to a
/// spelling that occurs nowhere in its scope or in `to` and names no
/// constructor. Renaming happens only when `from` occurs in that scope, so a
/// substitution without a clash returns the same shape it always did.
///
/// A local function binder can be called with call syntax (`g(x)`;
/// [`Elab::elab_call`] consults the context first), so a call HEAD spelled
/// `from` is substituted as well: renamed when `to` is a variable, applied
/// (`to(args)`) otherwise.
fn subst_surface(t: &S, from: &str, to: &S, is_ctor: &dyn Fn(&str) -> bool) -> S {
    let mut avoid = HashSet::new();
    names_in(to, &mut avoid);
    Subst { from, to, avoid: &avoid, is_ctor }.term(t)
}

struct Subst<'a> {
    from: &'a str,
    to: &'a S,
    /// Every name `to` mentions (free or not — an over-approximation only
    /// renames more often). A binder spelled like one of these is renamed
    /// before `to` is put under it.
    avoid: &'a HashSet<String>,
    is_ctor: &'a dyn Fn(&str) -> bool,
}

impl Subst<'_> {
    fn term(&self, t: &S) -> S {
        let go = |x: &S| self.term(x);
        match t {
            S::Var(n) => {
                if n == self.from {
                    self.to.clone()
                } else {
                    t.clone()
                }
            }
            S::IntLit(_) | S::RealLit(_) | S::Bool(_) => t.clone(),
            S::Not(a) => S::Not(Box::new(go(a))),
            S::Neg(a) => S::Neg(Box::new(go(a))),
            S::Bin(op, a, b) => S::Bin(*op, Box::new(go(a)), Box::new(go(b))),
            S::Call(f, args) => {
                let args = args.iter().map(go).collect();
                match self.to {
                    _ if f != self.from => S::Call(f.clone(), args),
                    S::Var(n) => S::Call(n.clone(), args),
                    to => S::App(Box::new(to.clone()), args),
                }
            }
            S::If(c, a, b) => S::If(Box::new(go(c)), Box::new(go(a)), Box::new(go(b))),
            S::SolveBy(g, l) => S::SolveBy(Box::new(go(g)), Box::new(go(l))),
            S::App(f, args) => S::App(Box::new(go(f)), args.iter().map(go).collect()),
            S::Let(x, e, body) => {
                let (x2, body2) = self.under_one(x, body);
                S::Let(x2, Box::new(go(e)), Box::new(body2))
            }
            S::Match(scrut, arms) => {
                S::Match(Box::new(go(scrut)), arms.iter().map(|a| self.arm(a)).collect())
            }
            S::Forall(bs, body, trigs) => {
                let (bs, body, trigs) = self.quant(bs, body, trigs);
                S::Forall(bs, Box::new(body), trigs)
            }
            S::Exists(bs, body, trigs) => {
                let (bs, body, trigs) = self.quant(bs, body, trigs);
                S::Exists(bs, Box::new(body), trigs)
            }
            S::Lam { name, params, ret, body, rec } => self.lam(name, params, ret, body, *rec),
        }
    }

    fn ty(&self, ty: &Type) -> Type {
        match ty {
            Type::Name(_) => ty.clone(),
            Type::App(n, args) => Type::App(n.clone(), args.iter().map(|a| self.ty(a)).collect()),
            Type::Arrow(d, c) => Type::Arrow(Box::new(self.ty(d)), Box::new(self.ty(c))),
            Type::Refine { var, base, pred } => {
                let (var, pred) = self.under_one(var, pred);
                Type::Refine { var, base: Box::new(self.ty(base)), pred: Box::new(pred) }
            }
        }
    }

    /// The fresh names for the binders in `bound` that would capture `to`,
    /// given every name occurring in their scope. Empty when nothing clashes
    /// or `from` does not occur in the scope.
    fn renames(&self, bound: &[&str], scope: HashSet<String>) -> Vec<(String, String)> {
        if !scope.contains(self.from) {
            return Vec::new();
        }
        let mut taken = scope;
        taken.extend(self.avoid.iter().cloned());
        taken.extend(bound.iter().map(|n| (*n).to_string()));
        let mut out: Vec<(String, String)> = Vec::new();
        for old in bound.iter().filter(|n| self.avoid.contains(**n)) {
            if out.iter().any(|(o, _)| o == old) {
                continue;
            }
            let fresh = (1..)
                .map(|k| format!("{old}!{k}"))
                .find(|c| !taken.contains(c) && !(self.is_ctor)(c))
                .expect("an unbounded supply of spellings");
            taken.insert(fresh.clone());
            out.push(((*old).to_string(), fresh));
        }
        out
    }

    /// A substitution that renames `old` to the fresh `new`, which occurs
    /// nowhere in the scope it is applied to (so it can never be captured).
    fn rename<R>(&self, old: &str, new: &str, f: impl FnOnce(&Subst<'_>) -> R) -> R {
        let to = S::Var(new.to_string());
        let avoid = HashSet::from([new.to_string()]);
        f(&Subst { from: old, to: &to, avoid: &avoid, is_ctor: self.is_ctor })
    }

    /// One binder `x` over `body` (a `let`, a refinement type's variable).
    fn under_one(&self, x: &str, body: &S) -> (String, S) {
        if x == self.from {
            return (x.to_string(), body.clone());
        }
        if !self.avoid.contains(x) {
            return (x.to_string(), self.term(body));
        }
        let mut scope = HashSet::new();
        names_in(body, &mut scope);
        match self.renames(&[x], scope).pop() {
            Some((old, new)) => {
                let body = self.rename(&old, &new, |r| r.term(body));
                (new, self.term(&body))
            }
            None => (x.to_string(), self.term(body)),
        }
    }

    fn quant(&self, bs: &[Binder], body: &S, trigs: &[Vec<S>]) -> (Vec<Binder>, S, Vec<Vec<S>>) {
        let bound = quant_bound(bs);
        if bound.contains(&self.from) {
            return (bs.to_vec(), body.clone(), trigs.to_vec());
        }
        let renames = if bound.iter().any(|n| self.avoid.contains(*n)) {
            let mut scope = HashSet::new();
            for b in bs {
                binder_names_in(b, &mut scope);
            }
            names_in(body, &mut scope);
            for p in trigs.iter().flatten() {
                names_in(p, &mut scope);
            }
            self.renames(&bound, scope)
        } else {
            Vec::new()
        };
        let (mut bs, mut body, mut trigs) = (bs.to_vec(), body.clone(), trigs.to_vec());
        for (old, new) in &renames {
            // the preimage of an image binder is a `Var` inside its `e`, so
            // renaming the parts renames it too.
            (bs, body, trigs) = self.rename(old, new, |r| r.quant_parts(&bs, &body, &trigs));
            for n in bs.iter_mut().flat_map(|b| b.names.iter_mut()) {
                if n == old {
                    n.clone_from(new);
                }
            }
        }
        self.quant_parts(&bs, &body, &trigs)
    }

    /// Every part of a quantifier, with no shadowing check of its own binders
    /// (the caller made that decision).
    fn quant_parts(&self, bs: &[Binder], body: &S, trigs: &[Vec<S>]) -> (Vec<Binder>, S, Vec<Vec<S>>) {
        let go = |x: &S| Box::new(self.term(x));
        let bs = bs
            .iter()
            .map(|b| Binder {
                names: b.names.clone(),
                ty: self.ty(&b.ty),
                constraint: b.constraint.as_ref().map(|(op, rhs)| (*op, go(rhs))),
                range: b.range.as_ref().map(|(lo, hi)| (go(lo), go(hi))),
                refinement: b.refinement.as_ref().map(|p| go(p)),
                image: b.image.as_ref().map(|(e, c)| (go(e), go(c))),
            })
            .collect();
        let trigs = trigs.iter().map(|g| g.iter().map(|p| self.term(p)).collect()).collect();
        (bs, self.term(body), trigs)
    }

    fn arm(&self, arm: &Arm) -> Arm {
        let bound: Vec<&str> = match &arm.pattern {
            Pattern::Bind(n) if !(self.is_ctor)(n) => vec![n.as_str()],
            Pattern::Ctor(_, pargs) => pargs
                .iter()
                .filter_map(|p| match p {
                    PatArg::Bind(n) => Some(n.as_str()),
                    PatArg::Wild => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        if bound.contains(&self.from) {
            return arm.clone();
        }
        let mut arm = arm.clone();
        if bound.iter().any(|n| self.avoid.contains(*n)) {
            let mut scope = HashSet::new();
            if let Some(g) = &arm.guard {
                names_in(g, &mut scope);
            }
            names_in(&arm.body, &mut scope);
            for (old, new) in self.renames(&bound, scope) {
                arm = self.rename(&old, &new, |r| r.arm_parts(&arm));
                match &mut arm.pattern {
                    Pattern::Bind(n) if *n == old => n.clone_from(&new),
                    Pattern::Ctor(_, pargs) => {
                        for p in pargs {
                            if matches!(p, PatArg::Bind(n) if *n == old) {
                                *p = PatArg::Bind(new.clone());
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        self.arm_parts(&arm)
    }

    fn arm_parts(&self, arm: &Arm) -> Arm {
        Arm {
            pattern: arm.pattern.clone(),
            guard: arm.guard.as_ref().map(|g| self.term(g)),
            body: self.term(&arm.body),
        }
    }

    fn lam(
        &self,
        name: &Option<String>,
        params: &[(Vec<String>, Type)],
        ret: &Type,
        body: &S,
        rec: bool,
    ) -> S {
        let mut bound: Vec<&str> = name.iter().map(String::as_str).collect();
        bound.extend(params.iter().flat_map(|(ns, _)| ns.iter().map(String::as_str)));
        if bound.contains(&self.from) {
            return S::Lam {
                name: name.clone(),
                params: params.to_vec(),
                ret: ret.clone(),
                body: Box::new(body.clone()),
                rec,
            };
        }
        let (mut name, mut params, mut ret, mut body) =
            (name.clone(), params.to_vec(), ret.clone(), body.clone());
        if bound.iter().any(|n| self.avoid.contains(*n)) {
            let mut scope = HashSet::new();
            names_in(&body, &mut scope);
            type_names_in(&ret, &mut scope);
            for (_, ty) in &params {
                type_names_in(ty, &mut scope);
            }
            for (old, new) in self.renames(&bound, scope) {
                (params, ret, body) = self.rename(&old, &new, |r| r.lam_parts(&params, &ret, &body));
                for n in name.iter_mut().chain(params.iter_mut().flat_map(|(ns, _)| ns.iter_mut())) {
                    if *n == old {
                        n.clone_from(&new);
                    }
                }
            }
        }
        let (params, ret, body) = self.lam_parts(&params, &ret, &body);
        S::Lam { name, params, ret, body: Box::new(body), rec }
    }

    fn lam_parts(
        &self,
        params: &[(Vec<String>, Type)],
        ret: &Type,
        body: &S,
    ) -> (Vec<(Vec<String>, Type)>, Type, S) {
        let params = params.iter().map(|(ns, ty)| (ns.clone(), self.ty(ty))).collect();
        (params, self.ty(ret), self.term(body))
    }
}

/// Every identifier spelled anywhere in `t` — variables, call heads, binder
/// and pattern names, refinement variables — free or bound.
fn names_in(t: &S, acc: &mut HashSet<String>) {
    match t {
        S::Var(n) => {
            acc.insert(n.clone());
        }
        S::IntLit(_) | S::RealLit(_) | S::Bool(_) => {}
        S::Not(a) | S::Neg(a) => names_in(a, acc),
        S::Bin(_, a, b) | S::SolveBy(a, b) => {
            names_in(a, acc);
            names_in(b, acc);
        }
        S::Call(f, args) => {
            acc.insert(f.clone());
            args.iter().for_each(|a| names_in(a, acc));
        }
        S::If(c, a, b) => {
            names_in(c, acc);
            names_in(a, acc);
            names_in(b, acc);
        }
        S::Let(x, e, body) => {
            acc.insert(x.clone());
            names_in(e, acc);
            names_in(body, acc);
        }
        S::Match(scrut, arms) => {
            names_in(scrut, acc);
            for arm in arms {
                match &arm.pattern {
                    Pattern::Bind(n) => {
                        acc.insert(n.clone());
                    }
                    Pattern::Ctor(c, pargs) => {
                        acc.insert(c.clone());
                        for p in pargs {
                            if let PatArg::Bind(n) = p {
                                acc.insert(n.clone());
                            }
                        }
                    }
                    Pattern::Wild | Pattern::Bool(_) | Pattern::IntLit(_) | Pattern::RealLit(_) => {}
                }
                if let Some(g) = &arm.guard {
                    names_in(g, acc);
                }
                names_in(&arm.body, acc);
            }
        }
        S::Forall(bs, body, trigs) | S::Exists(bs, body, trigs) => {
            bs.iter().for_each(|b| binder_names_in(b, acc));
            names_in(body, acc);
            trigs.iter().flatten().for_each(|p| names_in(p, acc));
        }
        S::App(f, args) => {
            names_in(f, acc);
            args.iter().for_each(|a| names_in(a, acc));
        }
        S::Lam { name, params, ret, body, .. } => {
            acc.extend(name.iter().cloned());
            for (ns, ty) in params {
                acc.extend(ns.iter().cloned());
                type_names_in(ty, acc);
            }
            type_names_in(ret, acc);
            names_in(body, acc);
        }
    }
}

fn binder_names_in(b: &Binder, acc: &mut HashSet<String>) {
    acc.extend(b.names.iter().cloned());
    type_names_in(&b.ty, acc);
    for t in b.range.iter().flat_map(|(lo, hi)| [lo, hi]) {
        names_in(t, acc);
    }
    if let Some((_, rhs)) = &b.constraint {
        names_in(rhs, acc);
    }
    if let Some(p) = &b.refinement {
        names_in(p, acc);
    }
    for t in b.image.iter().flat_map(|(e, c)| [e, c]) {
        names_in(t, acc);
    }
}

fn type_names_in(ty: &Type, acc: &mut HashSet<String>) {
    match ty {
        Type::Name(_) => {}
        Type::App(_, args) => args.iter().for_each(|a| type_names_in(a, acc)),
        Type::Arrow(d, c) => {
            type_names_in(d, acc);
            type_names_in(c, acc);
        }
        Type::Refine { var, base, pred } => {
            acc.insert(var.clone());
            type_names_in(base, acc);
            names_in(pred, acc);
        }
    }
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
        S::App(f, args) => {
            collect_ticks(f, acc);
            for a in args {
                collect_ticks(a, acc);
            }
        }
        S::Lam { body, .. } => {
            collect_ticks(body, acc);
        }
        S::IntLit(_) | S::RealLit(_) | S::Bool(_) => {}
    }
}
