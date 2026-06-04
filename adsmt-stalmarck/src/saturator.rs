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
}
