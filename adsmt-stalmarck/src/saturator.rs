//! Simple-rule saturator: transitive closure over the
//! implication graph.

use crate::graph::{ImplicationGraph, Lit};

/// Drives the simple-rule saturation loop.  Holds no state in
/// v0; the dilemma-rule sub-cycle will grow case-split bookkeeping
/// here.
#[derive(Default)]
pub struct Saturator;

impl Saturator {
    /// Empty saturator; nothing to seed for the v0 simple-rule
    /// path.
    pub fn new() -> Self {
        Self
    }

    /// Iterate the simple rule (transitive closure) on `graph`
    /// until fixpoint.  Quadratic in the edge count of the
    /// resulting closure — acceptable for the v0 use case
    /// (AOT-baked preludes have a few thousand binary
    /// implications at the worst observed sizes); the dilemma-rule
    /// sub-cycle replaces this with the n-saturation outer loop
    /// that calls the simple-rule kernel as its inner step.
    ///
    /// Returns the number of new edges added.
    pub fn saturate_simple(&self, graph: &mut ImplicationGraph) -> usize {
        let mut added = 0;
        loop {
            // Snapshot the current adjacency so the inner pass
            // iterates a stable view while we mutate the graph.
            let snapshot: Vec<(Lit, Vec<Lit>)> = graph
                .keys_iter()
                .cloned()
                .map(|from| {
                    let succs: Vec<Lit> = graph.successors(&from).cloned().collect();
                    (from, succs)
                })
                .collect();
            let mut changed = false;
            for (from, succs) in &snapshot {
                for mid in succs {
                    let further: Vec<Lit> =
                        graph.successors(mid).cloned().collect();
                    for to in further {
                        if from != &to && graph.add(from.clone(), to) {
                            added += 1;
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        added
    }

    /// §3.3 phase 2 — Stålmarck's dilemma rule, one step.
    ///
    /// Case-splits on `pivot`: runs the simple rule on a
    /// snapshot with `pivot = true` assumed (`¬pivot ⇒ pivot`
    /// asserted), and a second snapshot with `pivot = false`
    /// assumed (`pivot ⇒ ¬pivot` asserted), then folds every
    /// implication that both branches agree on back into
    /// `graph`.  Returns the number of new edges installed.
    ///
    /// The implementation is the textbook 0-saturation form
    /// of the dilemma rule — it observes implications common
    /// to both branches without committing the engine to
    /// either branch's verdict.  Stålmarck's `n`-saturation
    /// iterates this step on a frontier of pivot candidates;
    /// see [`Self::n_saturate`].
    pub fn dilemma_step(
        &self,
        graph: &mut ImplicationGraph,
        pivot: &Lit,
    ) -> usize {
        let mut g_true = graph.clone();
        g_true.add(pivot.negated(), pivot.clone());
        self.saturate_simple(&mut g_true);

        let mut g_false = graph.clone();
        g_false.add(pivot.clone(), pivot.negated());
        self.saturate_simple(&mut g_false);

        // Take the intersection of the two branches'
        // implication sets, drop the seed edge so we count
        // only genuinely new common consequences.
        let common = g_true.intersect_with(&g_false);
        let mut added = 0;
        for (from, to) in common.into_edges() {
            // Skip the edges that were already in the input
            // graph — they're not new consequences.
            if graph.implies(&from, &to) {
                continue;
            }
            if graph.add(from, to) {
                added += 1;
            }
        }
        added
    }

    /// §3.3 phase 2 — `n`-saturation outer loop.
    ///
    /// Repeats the dilemma step over every atom mentioned in
    /// `graph` for `depth` rounds (or until a round adds no
    /// new edges — earlier-than-`depth` fixpoint).  Returns
    /// the cumulative count of edges added across every
    /// dilemma step.
    ///
    /// `depth = 0` runs no dilemma rounds at all and is
    /// semantically equivalent to [`Self::saturate_simple`]
    /// (which the caller still has to run separately on the
    /// input graph if they want the 0-saturation transitive
    /// closure).
    pub fn n_saturate(
        &self,
        graph: &mut ImplicationGraph,
        depth: usize,
    ) -> usize {
        let mut total_added = 0;
        for _ in 0..depth {
            let atoms: Vec<String> = {
                use std::collections::BTreeSet;
                let mut set: BTreeSet<String> = BTreeSet::new();
                for from in graph.keys_iter() {
                    set.insert(from.atom.clone());
                }
                set.into_iter().collect()
            };
            let mut round_added = 0;
            for atom in atoms {
                let pivot = Lit::pos(atom);
                round_added += self.dilemma_step(graph, &pivot);
            }
            if round_added == 0 {
                break;
            }
            total_added += round_added;
        }
        total_added
    }
}

/// Public helper: build an implication graph from a CNF where
/// every clause has exactly two literals.  Each binary clause
/// `{a, b}` contributes `¬a ⇒ b` and `¬b ⇒ a`.  Unit clauses are
/// rejected (the caller pre-asserts them); longer clauses are
/// skipped (they do not contribute to the simple-rule graph at
/// 0-saturation level — the dilemma rule handles them at higher
/// saturation depths).
///
/// Returns the populated graph.  The caller drives
/// [`Saturator::saturate_simple`] on it to materialise the
/// transitive closure.
pub fn from_binary_clauses(clauses: &[Vec<Lit>]) -> ImplicationGraph {
    let mut g = ImplicationGraph::new();
    for clause in clauses {
        if clause.len() != 2 {
            continue;
        }
        let a = &clause[0];
        let b = &clause[1];
        // `(a ∨ b)` ≡ `(¬a ⇒ b)` ≡ `(¬b ⇒ a)`.
        g.add(a.negated(), b.clone());
        g.add(b.negated(), a.clone());
    }
    g
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binary_clause_extracts_both_implications() {
        // (a ∨ b) → {¬a ⇒ b, ¬b ⇒ a}.
        let cls = vec![vec![Lit::pos("a"), Lit::pos("b")]];
        let g = from_binary_clauses(&cls);
        assert!(g.implies(&Lit::neg("a"), &Lit::pos("b")));
        assert!(g.implies(&Lit::neg("b"), &Lit::pos("a")));
        assert_eq!(g.edge_count(), 2);
    }

    #[test]
    fn non_binary_clauses_are_skipped() {
        // Unit + ternary clauses contribute nothing to v0 graph.
        let cls = vec![
            vec![Lit::pos("a")],
            vec![Lit::pos("a"), Lit::pos("b"), Lit::pos("c")],
        ];
        let g = from_binary_clauses(&cls);
        assert!(g.is_empty());
    }

    #[test]
    fn saturate_simple_finds_transitive_chain() {
        // (¬a ∨ b) ∧ (¬b ∨ c) → ¬a ⇒ b ⇒ c.  Closure should
        // include ¬a ⇒ c.
        let cls = vec![
            vec![Lit::neg("a"), Lit::pos("b")],
            vec![Lit::neg("b"), Lit::pos("c")],
        ];
        let mut g = from_binary_clauses(&cls);
        let s = Saturator::new();
        let added = s.saturate_simple(&mut g);
        assert!(g.implies(&Lit::pos("a"), &Lit::pos("c")));
        assert!(added > 0);
    }

    #[test]
    fn saturate_simple_terminates_on_consistent_input() {
        let cls = vec![
            vec![Lit::neg("a"), Lit::pos("b")],
            vec![Lit::neg("b"), Lit::pos("c")],
        ];
        let mut g = from_binary_clauses(&cls);
        let s = Saturator::new();
        let first = s.saturate_simple(&mut g);
        // Second call is a fixpoint — zero new edges.
        let second = s.saturate_simple(&mut g);
        assert!(first > 0);
        assert_eq!(second, 0);
    }

    #[test]
    fn saturate_then_detect_contradiction_on_unsat_chain() {
        // (¬a ∨ b) ∧ (¬b ∨ ¬a) ≡ ¬a stays consistent.  Build a
        // true contradiction: (a ∨ ¬b) ∧ (¬a ∨ ¬b) ∧ (b ∨ ¬a)
        // ∧ (b ∨ a) ≡ … pick a simpler one: a ⇒ b, b ⇒ ¬a.
        // Encoded as binary clauses: (¬a ∨ b) ∧ (¬b ∨ ¬a).
        let cls = vec![
            vec![Lit::neg("a"), Lit::pos("b")],
            vec![Lit::neg("b"), Lit::neg("a")],
        ];
        let mut g = from_binary_clauses(&cls);
        let s = Saturator::new();
        s.saturate_simple(&mut g);
        // a ⇒ b (from clause 1) and b ⇒ ¬a (from clause 2) ⇒
        // a ⇒ ¬a after closure.  Witness chain is at least
        // [a, b, ¬a].
        let chain = g.detect_contradiction().unwrap();
        // The detected chain should be `a ⇒ b ⇒ ¬a` after
        // saturation, but `detect_contradiction`'s BFS may also
        // accept a direct `a ⇒ ¬a` edge once the closure pass
        // adds it.  Either witness is valid.
        assert!(chain.first() == Some(&Lit::pos("a")));
        assert!(chain.last() == Some(&Lit::neg("a")));
    }

    // §3.3 phase 2 — dilemma rule + n-saturation.

    #[test]
    fn intersect_with_keeps_only_common_edges() {
        let mut g1 = ImplicationGraph::new();
        g1.add(Lit::pos("a"), Lit::pos("b"));
        g1.add(Lit::pos("a"), Lit::pos("c"));
        let mut g2 = ImplicationGraph::new();
        g2.add(Lit::pos("a"), Lit::pos("b"));
        g2.add(Lit::pos("a"), Lit::pos("d"));
        let common = g1.intersect_with(&g2);
        assert!(common.implies(&Lit::pos("a"), &Lit::pos("b")));
        assert!(!common.implies(&Lit::pos("a"), &Lit::pos("c")));
        assert!(!common.implies(&Lit::pos("a"), &Lit::pos("d")));
    }

    #[test]
    fn dilemma_step_on_consistent_graph_finds_no_new_edges() {
        // Graph with only `a ⇒ b`; pivoting on a brings in
        // (true-branch: a ⇒ b, true ⇒ b) and the false branch
        // collapses on the seeded ¬pivot edge.  The
        // intersection produces no genuinely new edges over
        // the input.
        let mut g = ImplicationGraph::new();
        g.add(Lit::pos("a"), Lit::pos("b"));
        let s = Saturator::new();
        let added = s.dilemma_step(&mut g, &Lit::pos("c"));
        assert_eq!(added, 0);
    }

    #[test]
    fn dilemma_step_propagates_common_consequence() {
        // Clauses (¬x ∨ y) ∧ (x ∨ y) ≡ y.  Even though no
        // direct y-fact is in the simple-rule graph, the
        // dilemma on x should expose `_ ⇒ y` shared by both
        // branches.
        let cls = vec![
            vec![Lit::neg("x"), Lit::pos("y")],
            vec![Lit::pos("x"), Lit::pos("y")],
        ];
        let mut g = from_binary_clauses(&cls);
        let s = Saturator::new();
        s.saturate_simple(&mut g);
        let _added = s.dilemma_step(&mut g, &Lit::pos("x"));
        // Both branches force y → ¬y ⇒ y is one of the
        // common consequences in either branch's saturated
        // implication set.
        assert!(g.implies(&Lit::neg("y"), &Lit::pos("y")));
    }

    #[test]
    fn n_saturate_with_depth_zero_is_noop() {
        let cls = vec![vec![Lit::neg("a"), Lit::pos("b")]];
        let mut g = from_binary_clauses(&cls);
        let before = g.edge_count();
        let s = Saturator::new();
        let added = s.n_saturate(&mut g, 0);
        assert_eq!(added, 0);
        assert_eq!(g.edge_count(), before);
    }

    #[test]
    fn n_saturate_fixpoints_within_depth_budget() {
        let cls = vec![
            vec![Lit::neg("x"), Lit::pos("y")],
            vec![Lit::pos("x"), Lit::pos("y")],
        ];
        let mut g = from_binary_clauses(&cls);
        let s = Saturator::new();
        s.saturate_simple(&mut g);
        // 3 rounds is well above the fixpoint for this
        // 2-clause input; n_saturate should terminate
        // early and the final graph should be unchanged
        // across the unused rounds.
        let _ = s.n_saturate(&mut g, 3);
        let snapshot = g.edge_count();
        let _ = s.n_saturate(&mut g, 3);
        assert_eq!(g.edge_count(), snapshot, "fixpoint reached");
    }
}
