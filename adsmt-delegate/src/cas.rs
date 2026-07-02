//! CAS delegation — classify `H ⊢ G` into an algebraic obligation, dispatch it to
//! the manifest-enabled backends, and return the admit-re-checked [`CasProof`].
//!
//! This is the logic that used to be inlined in `lu-smt`'s `Driver::cas_delegate`.
//! The Driver-specific *ledger split* (recovering `H` / `G` from the SMT-LIB
//! `:goal-negation` stream) stays in the CLI; this takes the already-split typed
//! sequent, so `adsmt-lukb-driver` — which already has typed hypotheses + a goal —
//! calls it directly.

use adsmt_cas::manifest::CasManifest;
use adsmt_cas::{CasBackend, CasClass, CasProof, Disposition, term};
use adsmt_core::{Term, TermInner};

/// Classify `hyps ⊢ goal` and route it to the manifest-enabled CAS backends,
/// returning the admit-re-checked [`CasProof`] iff a witness discharges the goal.
///
/// `goal` is the POSITIVE goal `G` (the caller has already stripped the outer `¬`
/// from the SMT query `H ∧ ¬G`). `Some(proof)` ⇒ `G` is valid ⇒ `H ∧ ¬G` is
/// `unsat`; the proof is the offline-re-checkable obligation+witness the caller
/// embeds in the certificate. `None` is the sound fallback.
///
/// Every recognized class only ever proves its goal *valid*, and every backend
/// witness is admit-re-checked with exact `BigRational` / `BigInt`, so a backend
/// bug can only ever yield `None` — never a wrong `Some`. Class gating mirrors the
/// original `Driver::cas_delegate`: membership + ∃-Diophantine (universally
/// reserved `+`/`*`/`=`/`∃`) are always routed; compositeness / primality (over
/// `prime`) only when the manifest attests `arith_builtins_reserved`.
#[must_use]
pub fn try_discharge(hyps: &[Term], goal: &Term, manifest: &CasManifest) -> Option<CasProof> {
    // Un-fold a `(=> H G)` goal into extra hypotheses + the conclusion (flattening
    // conjunctions), so a lu-kb obligation — which lowers the sequent `H |- G` into
    // ONE implication with no separate hypotheses — classifies the SAME as lu-smt's
    // already-split `:goal-negation` ledger. lu-smt passes an un-folded goal, so
    // this is a no-op there (its cas_glue tests use plain-equation goals).
    let mut all_hyps: Vec<Term> = hyps.to_vec();
    let goal = split_sequent(goal, &mut all_hyps);

    let obligation = if manifest.arith_builtins_reserved {
        let goal = promote_prime(&goal);
        term::classify_sequent(&all_hyps, &goal) // membership → ∃ → ¬prime → prime
    } else {
        term::classify_membership(&all_hyps, &goal).or_else(|| term::classify_diophantine(&goal))
    }?;

    // Constructing all three backends is free (no CAS spawns until `decide`):
    // Singular (subprocess; membership / factorization), MathHook (in-process;
    // factorization), NumTheory (pure; compositeness / primality). The manifest's
    // `enabled` order selects which run; `dispatch_with_proof` filters by
    // allow-list ∩ `capabilities()` and admit-gates every witness.
    let singular = cas_backend_singular::SingularBackend::new(
        manifest
            .backends
            .get("singular")
            .and_then(|c| c.path.clone())
            .or_else(|| std::env::var("ADSMT_SINGULAR_PATH").ok())
            .unwrap_or_else(|| "Singular".to_string()),
    );
    let mathhook = cas_backend_mathhook::MathhookBackend::new();
    let numtheory = cas_backend_numtheory::NumTheoryBackend::new();
    let backends: Vec<&dyn CasBackend> = vec![&singular, &mathhook, &numtheory];

    match adsmt_cas::dispatch_with_proof(manifest, &backends, &obligation) {
        // A re-checked verdict on the POSITIVE goal `G` means `G` is VALID, so the
        // SMT query `H ∧ ¬G` is UNSAT. Return the re-checked proof.
        (Disposition::Verdict(_), proof) => proof,
        (Disposition::Unknown, _) => None,
    }
}

/// Peel leading implications off `goal`, flattening each antecedent's conjuncts
/// into `hyps`, and return the final conclusion. `(=> (and A B) C)` ⇒ pushes `A`,
/// `B` and returns `C`. A non-implication goal is returned unchanged (lu-smt's
/// already-split path). This bridges a lu-kb obligation (the sequent `H |- G`
/// lowered into one implication `H => G` with no separate hypotheses) to the
/// hyps-and-goal shape the `adsmt-cas` classifiers expect.
fn split_sequent(goal: &Term, hyps: &mut Vec<Term>) -> Term {
    let mut g = goal.clone();
    while let Some((ante, cons)) = dest_bin(&g, "=>") {
        flatten_and(&ante, hyps);
        g = cons;
    }
    g
}

/// `(op a b)` = `App(App(Const(op), a), b)` destructured to `(a, b)`.
fn dest_bin(t: &Term, op: &str) -> Option<(Term, Term)> {
    if let TermInner::App(f, b) = t.kind()
        && let TermInner::App(g, a) = f.kind()
        && let TermInner::Const(c) = g.kind()
        && c.name == op
    {
        return Some((a.clone(), b.clone()));
    }
    None
}

/// Flatten a (possibly nested / curried) conjunction into its conjunct leaves.
fn flatten_and(t: &Term, out: &mut Vec<Term>) {
    if let Some((a, b)) = dest_bin(t, "and") {
        flatten_and(&a, out);
        flatten_and(&b, out);
    } else {
        out.push(t.clone());
    }
}

/// Promote the SMT-LIB-face `Var("prime")` to the built-in `Const("prime")` the
/// compositeness / primality classifiers expect. Only meaningful when the manifest
/// attests `arith_builtins_reserved`. Recurses through applications; a rebuild
/// failure is a no-op.
#[must_use]
pub fn promote_prime(t: &Term) -> Term {
    match t.kind() {
        TermInner::Var(v) if v.name == "prime" => Term::const_("prime", t.type_of()),
        TermInner::App(f, x) => {
            Term::app(promote_prime(f), promote_prime(x)).unwrap_or_else(|_| t.clone())
        }
        _ => t.clone(),
    }
}

/// The manifest kebab-case name of a CAS obligation class — stamped into a
/// `TheoryWitness::Cas` certificate for provenance + offline re-check routing.
#[must_use]
pub fn class_kebab(c: CasClass) -> &'static str {
    match c {
        CasClass::IdealMembership => "ideal-membership",
        CasClass::Factorization => "factorization",
        CasClass::Compositeness => "compositeness",
        CasClass::Primality => "primality",
        CasClass::DiophantineExists => "diophantine-exists",
        CasClass::UniversalRefutation => "universal-refutation",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Type};

    fn int_t() -> Type {
        Type::const_("Int", Kind::Type)
    }
    fn iv(n: &str) -> Term {
        Term::var(n, int_t())
    }
    fn ic(n: &str) -> Term {
        Term::const_(n, int_t())
    }
    fn app2(op: &str, a: Term, b: Term, ret: Type) -> Term {
        let ty = Type::fun(int_t(), Type::fun(int_t(), ret).unwrap()).unwrap();
        Term::app(Term::app(Term::const_(op, ty), a).unwrap(), b).unwrap()
    }
    fn bin_bool(op: &str, a: Term, b: Term) -> Term {
        let bt = Type::bool_();
        let ty = Type::fun(bt.clone(), Type::fun(bt.clone(), bt.clone()).unwrap()).unwrap();
        Term::app(Term::app(Term::const_(op, ty), a).unwrap(), b).unwrap()
    }

    #[test]
    fn split_sequent_unfolds_a_lukb_folded_implication() {
        // The shape lu-kb lowers `x=2, y=3 |- x*y=6` into:
        //   (=> (and (= x 2) (= y 3)) (= (* x y) 6))
        let eq = |a, b| app2("=", a, b, Type::bool_());
        let mul = |a, b| app2("*", a, b, int_t());
        let h1 = eq(iv("x"), ic("2"));
        let h2 = eq(iv("y"), ic("3"));
        let concl = eq(mul(iv("x"), iv("y")), ic("6"));
        let folded = bin_bool("=>", bin_bool("and", h1.clone(), h2.clone()), concl.clone());

        let mut hyps = Vec::new();
        let g = split_sequent(&folded, &mut hyps);
        assert_eq!(hyps.len(), 2, "both conjuncts become hypotheses");
        assert!(hyps.contains(&h1) && hyps.contains(&h2));
        assert_eq!(g, concl, "the conclusion is peeled out");
    }

    #[test]
    fn split_sequent_leaves_a_plain_goal_untouched() {
        // lu-smt passes an already-split (non-implication) goal — a no-op here.
        let goal = app2("=", iv("x"), ic("5"), Type::bool_());
        let mut hyps = Vec::new();
        let g = split_sequent(&goal, &mut hyps);
        assert!(hyps.is_empty());
        assert_eq!(g, goal);
    }
}
