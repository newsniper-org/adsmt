//! The ground program + the **forward Horn least-fixpoint evaluator** — the one
//! genuinely new runtime primitive of the typed-ASP face (DESIGN.md §7).
//!
//! It plays three roles at once: the **solver** for the definite (L0/L1)
//! fragment, the **re-check gate** (every claimed answer is verified by
//! recomputing the least model and confirming membership), and the abductive
//! engine's **forward-chainer** (the missing forward direction — the existing
//! SLD engine runs *backward*).
//!
//! ## What it computes
//!
//! Given a set of ground definite rules `head :- b₁, …, bₙ` each carrying a
//! pre-evaluated theory **guard** (the conjunction of the rule's `open` SMT
//! atoms, fixed by a verified `θ`; a fact is the empty-body, `guard = true`
//! case), [`GroundProgram::least_model`] returns the **least Herbrand model**:
//! the ⊆-minimal set of atoms closed under rule application. For a definite
//! program this least model *is* the unique answer set (DESIGN.md §3) — so for
//! the MVP fragment the fixpoint is the whole solver, with no model to guess.
//!
//! ## Soundness properties (the gate relies on these)
//!
//! - **Deterministic + total**: the least model is unique and the evaluation
//!   terminates (each atom enters the model at most once; the worklist is
//!   bounded by the atom count) — even on cyclic programs (`p :- q. q :- p.`
//!   derives neither, the correct least model).
//! - **Minimal**: an atom is in the model *iff* it has a finite derivation from
//!   the facts through guard-satisfied rules. Nothing is invented — so a
//!   claimed answer set that contains an extra atom is detected by recomputation
//!   (`least_model() != claimed`), and the gate can only ever *shrink* a buggy
//!   over-claim, never manufacture a false entailment.

use std::collections::{BTreeSet, HashMap};

/// A ground atom, interned to a small integer id by the (future) elaborator /
/// grounder. The fixpoint is purely structural over these ids, so it is
/// independent of the surface syntax and of the kernel term representation.
pub type Atom = u32;

/// A ground definite rule `head :- body…` whose `open` theory atoms have already
/// been collapsed (by a verified `θ`) into a single boolean **guard**. A *fact*
/// is `{ body: [], guard: true }`; a rule whose theory guard is false under `θ`
/// is `{ guard: false }` and never fires.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroundRule {
    pub head: Atom,
    pub body: Vec<Atom>,
    pub guard: bool,
}

impl GroundRule {
    /// A fact `head.` (empty body, guard satisfied).
    pub fn fact(head: Atom) -> Self {
        GroundRule { head, body: Vec::new(), guard: true }
    }

    /// A rule `head :- body…` with the theory guard already evaluated.
    pub fn rule(head: Atom, body: Vec<Atom>, guard: bool) -> Self {
        GroundRule { head, body, guard }
    }
}

/// A ground definite program: a multiset of [`GroundRule`]s.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GroundProgram {
    pub rules: Vec<GroundRule>,
}

impl GroundProgram {
    pub fn new() -> Self {
        GroundProgram::default()
    }

    pub fn push(&mut self, r: GroundRule) {
        self.rules.push(r);
    }

    /// The **least Herbrand model**, by semi-naïve forward chaining: seed with
    /// the guard-satisfied facts, then re-examine a rule only when one of its
    /// body atoms is newly derived (so each rule is revisited `O(body)` times,
    /// not once per round). For a definite program this is the unique answer set.
    pub fn least_model(&self) -> BTreeSet<Atom> {
        // index: body atom → the rules that mention it (so a newly-derived atom
        // wakes only the rules that could now fire).
        let mut uses: HashMap<Atom, Vec<usize>> = HashMap::new();
        for (ri, r) in self.rules.iter().enumerate() {
            // distinct body atoms only — a repeated body atom needn't wake the
            // rule twice.
            let mut seen = BTreeSet::new();
            for &b in &r.body {
                if seen.insert(b) {
                    uses.entry(b).or_default().push(ri);
                }
            }
        }

        let mut model: BTreeSet<Atom> = BTreeSet::new();
        let mut delta: Vec<Atom> = Vec::new();

        // seed: every guard-satisfied fact.
        for r in &self.rules {
            if r.guard && r.body.is_empty() && model.insert(r.head) {
                delta.push(r.head);
            }
        }

        // propagate: a rule fires when its LAST missing body atom is derived.
        while let Some(a) = delta.pop() {
            let Some(ris) = uses.get(&a) else { continue };
            for &ri in ris {
                let r = &self.rules[ri];
                if r.guard
                    && !model.contains(&r.head)
                    && r.body.iter().all(|b| model.contains(b))
                {
                    model.insert(r.head);
                    delta.push(r.head);
                }
            }
        }
        model
    }

    /// Whether `atom` is in the least model (a derivation exists).
    pub fn entails(&self, atom: Atom) -> bool {
        self.least_model().contains(&atom)
    }

    /// The **re-check gate**: is `claimed` exactly the least model? Used to
    /// independently verify a solver/heuristic's claimed answer set — a buggy
    /// producer that over-claims is caught here (extra atoms ⇒ inequality),
    /// never trusted.
    pub fn is_exact_model(&self, claimed: &BTreeSet<Atom>) -> bool {
        &self.least_model() == claimed
    }
}

/// A ground rule that **retains its negative body** — the one piece of state the
/// L3 stable-model gate needs that the definite [`GroundRule`] folds away. The
/// L2 grounder collapses each `not q` into the scalar guard against a frozen
/// lower stratum, which is correct under stratification but *destroys* the
/// negative body, so the [Gelfond–Lifschitz reduct] is unbuildable from a
/// [`GroundProgram`]. [`GroundNRule`] keeps `neg` separate.
///
/// Invariant: the theory **guard is already true** — a guard-false ground
/// instance is *dropped at grounding time* (mirroring [`GroundProgram::least_model`]'s
/// `r.guard &&`), and a guard that *errors* propagates as a `FaceError`. So the
/// θ-theory decides a rule's **presence** during grounding, and the GL reduct
/// decides its **survival**; the two negations stay orthogonal and every
/// `GroundNRule` here is an unconditional `head :- pos…, not neg…`. A fact is
/// `{ pos: [], neg: [] }`.
///
/// [Gelfond–Lifschitz reduct]: https://en.wikipedia.org/wiki/Stable_model_semantics
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroundNRule {
    pub head: Atom,
    pub pos: Vec<Atom>,
    pub neg: Vec<Atom>,
}

impl GroundNRule {
    /// A fact `head.` (empty positive and negative body).
    pub fn fact(head: Atom) -> Self {
        GroundNRule { head, pos: Vec::new(), neg: Vec::new() }
    }

    /// A rule `head :- pos…, not neg…` (theory guard already true and dropped).
    pub fn rule(head: Atom, pos: Vec<Atom>, neg: Vec<Atom>) -> Self {
        GroundNRule { head, pos, neg }
    }
}

/// A ground **normal** logic program (rules carrying negation-as-failure). The
/// stable-model gate ([`GroundNProgram::is_stable`]) is the L3 trust boundary; it
/// reuses [`GroundProgram::least_model`] verbatim, so no new trusted fixpoint
/// code is introduced.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GroundNProgram {
    pub rules: Vec<GroundNRule>,
}

impl GroundNProgram {
    pub fn new() -> Self {
        GroundNProgram::default()
    }

    pub fn push(&mut self, r: GroundNRule) {
        self.rules.push(r);
    }

    /// The **Gelfond–Lifschitz reduct** `Pᴹ`: keep each rule whose negative body
    /// is *disjoint* from `m`, deleting its `not` literals — a positive
    /// [`GroundProgram`] whose least model is computed by the trusted lfp. This is
    /// a verbatim transcription of GL-1988: drop a rule with a `not q`, `q ∈ M`;
    /// the survivors lose their (now-satisfied) `not` literals and become
    /// definite.
    pub fn reduct(&self, m: &BTreeSet<Atom>) -> GroundProgram {
        let mut out = GroundProgram::new();
        for r in &self.rules {
            if r.neg.iter().any(|q| m.contains(q)) {
                continue; // a `not q` with q ∈ M kills the rule
            }
            out.push(GroundRule::rule(r.head, r.pos.clone(), true));
        }
        out
    }

    /// **The gate.** `m` is a stable model iff `least_model(Pᴹ) == m`.
    ///
    /// This is the sole new trusted surface — a syntactic rule filter
    /// ([`Self::reduct`]) plus two existing calls ([`GroundProgram::least_model`]
    /// via [`GroundProgram::is_exact_model`]). The candidate `m` is *untrusted*:
    /// a buggy enumerator can only propose a non-stable `m` (rejected here, since
    /// certification *is* the recompute) or skip a stable one (a sound
    /// under-report) — it can never certify a non-stable model. Same
    /// generate-and-check firewall as the abductive search, lifted from
    /// single-goal membership to whole-model equality.
    pub fn is_stable(&self, m: &BTreeSet<Atom>) -> bool {
        self.reduct(m).is_exact_model(m)
    }

    /// The **support base** `B`: the heads of all rules. Every stable model is
    /// supported (each of its atoms is the head of a reduct rule that fired in
    /// the lfp, and `least_model` only ever inserts heads), so `M ⊆ B` — an atom
    /// that is never a head is in no stable model. Used to bracket the search.
    pub fn heads(&self) -> BTreeSet<Atom> {
        self.rules.iter().map(|r| r.head).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Facts + a join rule: `c :- a, b` fires once both facts are present.
    #[test]
    fn facts_and_join() {
        let mut p = GroundProgram::new();
        p.push(GroundRule::fact(0)); // a
        p.push(GroundRule::fact(1)); // b
        p.push(GroundRule::rule(2, vec![0, 1], true)); // c :- a, b
        p.push(GroundRule::rule(3, vec![2], true)); // d :- c
        let m = p.least_model();
        assert_eq!(m, BTreeSet::from([0, 1, 2, 3]));
    }

    /// A rule whose body atom is never derived does not fire (least model).
    #[test]
    fn missing_body_atom_blocks() {
        let mut p = GroundProgram::new();
        p.push(GroundRule::fact(0)); // a
        p.push(GroundRule::rule(2, vec![0, 99], true)); // e :- a, x  (x absent)
        assert_eq!(p.least_model(), BTreeSet::from([0]));
    }

    /// A false theory guard blocks the rule even when the body holds (L1: the
    /// `open` SMT atom is unsatisfied under θ).
    #[test]
    fn false_guard_blocks() {
        let mut p = GroundProgram::new();
        p.push(GroundRule::fact(0)); // a
        p.push(GroundRule::rule(1, vec![0], false)); // f :- a, {θ-false}
        assert_eq!(p.least_model(), BTreeSet::from([0]));
        // and with the guard true it fires.
        let mut q = GroundProgram::new();
        q.push(GroundRule::fact(0));
        q.push(GroundRule::rule(1, vec![0], true));
        assert_eq!(q.least_model(), BTreeSet::from([0, 1]));
    }

    /// Transitive closure over a small graph terminates and is exact — including
    /// a self-loop (a cyclic positive program must still reach a fixpoint).
    #[test]
    fn transitive_closure_with_cycle() {
        // ground reach atoms: encode reach(i,j) as atom 100*i + j.
        let r = |i: u32, j: u32| 100 * i + j;
        let mut p = GroundProgram::new();
        // edges 1->2, 2->3, 3->2 (a cycle), as base reach facts.
        for &(i, j) in &[(1, 2), (2, 3), (3, 2)] {
            p.push(GroundRule::fact(r(i, j)));
        }
        // transitivity, fully grounded over nodes {1,2,3}.
        for a in 1..=3 {
            for b in 1..=3 {
                for c in 1..=3 {
                    // reach(a,c) :- reach(a,b), reach(b,c)
                    p.push(GroundRule::rule(r(a, c), vec![r(a, b), r(b, c)], true));
                }
            }
        }
        let m = p.least_model();
        // 1 reaches 2,3; 2 reaches 2,3; 3 reaches 2,3 (via the 2<->3 cycle).
        let expect = BTreeSet::from([
            r(1, 2), r(1, 3),
            r(2, 2), r(2, 3),
            r(3, 2), r(3, 3),
        ]);
        assert_eq!(m, expect);
    }

    /// A purely cyclic program with no facts derives nothing (the correct least
    /// model — termination on a cycle, no spurious derivation).
    #[test]
    fn cycle_without_facts_derives_nothing() {
        let mut p = GroundProgram::new();
        p.push(GroundRule::rule(0, vec![1], true)); // p :- q
        p.push(GroundRule::rule(1, vec![0], true)); // q :- p
        assert_eq!(p.least_model(), BTreeSet::new());
    }

    /// The re-check gate rejects an over-claim (a claimed answer set with an atom
    /// that has no derivation) and accepts the exact least model.
    #[test]
    fn gate_rejects_overclaim() {
        let mut p = GroundProgram::new();
        p.push(GroundRule::fact(0));
        p.push(GroundRule::rule(1, vec![0], true)); // q :- a
        assert!(p.is_exact_model(&BTreeSet::from([0, 1])), "the true least model");
        assert!(!p.is_exact_model(&BTreeSet::from([0, 1, 2])), "over-claim caught");
        assert!(!p.is_exact_model(&BTreeSet::from([0])), "under-claim caught");
    }

    // -----------------------------------------------------------------------
    // L3 — the Gelfond–Lifschitz stable-model gate (`GroundNProgram`).
    // -----------------------------------------------------------------------

    /// A small brute-force stable-model oracle over the full head base, to
    /// cross-check the gate (no bracketing — exhaustive over 2^|heads|).
    fn brute_stable(p: &GroundNProgram) -> BTreeSet<BTreeSet<Atom>> {
        let heads: Vec<Atom> = p.heads().into_iter().collect();
        let mut out = BTreeSet::new();
        for mask in 0u64..(1u64 << heads.len()) {
            let m: BTreeSet<Atom> =
                heads.iter().enumerate().filter(|(i, _)| mask >> i & 1 == 1).map(|(_, &a)| a).collect();
            if p.is_stable(&m) {
                out.insert(m);
            }
        }
        out
    }

    /// The classic even loop `p :- not q. q :- not p.` has exactly two stable
    /// models, `{p}` and `{q}` — and the gate accepts only those (rejects `{}`
    /// and `{p,q}`).
    #[test]
    fn gate_even_loop_two_models() {
        let (p, q) = (0u32, 1u32);
        let mut prog = GroundNProgram::new();
        prog.push(GroundNRule::rule(p, vec![], vec![q])); // p :- not q
        prog.push(GroundNRule::rule(q, vec![], vec![p])); // q :- not p
        assert!(prog.is_stable(&BTreeSet::from([p])), "{{p}} is stable");
        assert!(prog.is_stable(&BTreeSet::from([q])), "{{q}} is stable");
        assert!(!prog.is_stable(&BTreeSet::new()), "{{}} is not stable");
        assert!(!prog.is_stable(&BTreeSet::from([p, q])), "{{p,q}} is not stable");
        assert_eq!(brute_stable(&prog), BTreeSet::from([BTreeSet::from([p]), BTreeSet::from([q])]));
    }

    /// Direct self-negation `p :- not p.` has **no** stable model.
    #[test]
    fn gate_self_negation_no_model() {
        let p = 0u32;
        let mut prog = GroundNProgram::new();
        prog.push(GroundNRule::rule(p, vec![], vec![p])); // p :- not p
        assert!(!prog.is_stable(&BTreeSet::new()));
        assert!(!prog.is_stable(&BTreeSet::from([p])));
        assert!(brute_stable(&prog).is_empty(), "no answer set");
    }

    /// The reduct drops a rule whose `not q` is satisfied (`q ∈ M`) and deletes
    /// the `not` literals from the survivors, leaving a positive program.
    #[test]
    fn reduct_drops_and_deletes() {
        let (p, q, r) = (0u32, 1u32, 2u32);
        let mut prog = GroundNProgram::new();
        prog.push(GroundNRule::fact(q)); // q.
        prog.push(GroundNRule::rule(p, vec![], vec![q])); // p :- not q   (q ∈ M ⇒ dropped)
        prog.push(GroundNRule::rule(r, vec![q], vec![p])); // r :- q, not p (p ∉ M ⇒ kept, → r :- q)
        let red = prog.reduct(&BTreeSet::from([q]));
        // survivors: the fact q, and r :- q (the `not p` deleted); the p-rule gone.
        assert_eq!(red.rules, vec![GroundRule::fact(q), GroundRule::rule(r, vec![q], true)]);
        assert_eq!(red.least_model(), BTreeSet::from([q, r]));
    }

    /// On a **definite** (negation-free) `GroundNProgram` the unique stable model
    /// equals the `GroundProgram` least model of the same rules (L2 ≡ L3 on a
    /// stratified input).
    #[test]
    fn gate_definite_matches_least_model() {
        let mut gn = GroundNProgram::new();
        gn.push(GroundNRule::fact(0)); // a
        gn.push(GroundNRule::rule(1, vec![0], vec![])); // b :- a
        gn.push(GroundNRule::rule(2, vec![1], vec![])); // c :- b
        let mut gp = GroundProgram::new();
        gp.push(GroundRule::fact(0));
        gp.push(GroundRule::rule(1, vec![0], true));
        gp.push(GroundRule::rule(2, vec![1], true));
        let lm = gp.least_model();
        assert!(gn.is_stable(&lm));
        assert_eq!(brute_stable(&gn), BTreeSet::from([lm]));
    }

    /// Determinism: the least model is independent of rule order.
    #[test]
    fn order_independent() {
        let mk = |order: &[GroundRule]| {
            let mut p = GroundProgram::new();
            for r in order {
                p.push(r.clone());
            }
            p.least_model()
        };
        let rules = [
            GroundRule::rule(3, vec![2], true),
            GroundRule::rule(2, vec![0, 1], true),
            GroundRule::fact(1),
            GroundRule::fact(0),
        ];
        let forward = mk(&rules);
        let mut rev = rules.to_vec();
        rev.reverse();
        assert_eq!(forward, mk(&rev));
        assert_eq!(forward, BTreeSet::from([0, 1, 2, 3]));
    }
}
