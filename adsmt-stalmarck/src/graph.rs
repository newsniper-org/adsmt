//! Implication-graph data structures.

use std::collections::{BTreeMap, BTreeSet};

/// A propositional literal — atom name (free-form `String` to
/// stay independent of any specific term-DAG representation) +
/// polarity (`true` = positive, `false` = negative).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Lit {
    pub atom: String,
    pub polarity: bool,
}

impl Lit {
    /// Positive literal `atom`.
    pub fn pos(atom: impl Into<String>) -> Self {
        Self {
            atom: atom.into(),
            polarity: true,
        }
    }

    /// Negative literal `¬atom`.
    pub fn neg(atom: impl Into<String>) -> Self {
        Self {
            atom: atom.into(),
            polarity: false,
        }
    }

    /// Logical negation: flip polarity, keep atom.
    pub fn negated(&self) -> Lit {
        Lit {
            atom: self.atom.clone(),
            polarity: !self.polarity,
        }
    }
}

/// Implication graph: an edge `(l1, l2)` records `l1 ⇒ l2`.
/// Stored as `BTreeMap<Lit, BTreeSet<Lit>>` so the saturation
/// loop's iteration order is deterministic (the contradiction
/// witness chain wants reproducible output across runs).
#[derive(Default, Clone, Debug)]
pub struct ImplicationGraph {
    out: BTreeMap<Lit, BTreeSet<Lit>>,
}

impl ImplicationGraph {
    /// Empty graph; no literals registered.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of distinct `(from, to)` edges in the graph.
    pub fn edge_count(&self) -> usize {
        self.out.values().map(BTreeSet::len).sum()
    }

    /// `true` iff the graph has no edges.
    pub fn is_empty(&self) -> bool {
        self.out.values().all(BTreeSet::is_empty)
    }

    /// Add edge `from ⇒ to`.  Idempotent.  Returns `true` if the
    /// edge was new.
    pub fn add(&mut self, from: Lit, to: Lit) -> bool {
        self.out.entry(from).or_default().insert(to)
    }

    /// Iterate every successor of `from`.  Empty iterator if
    /// `from` has no recorded implications.
    pub fn successors(&self, from: &Lit) -> impl Iterator<Item = &Lit> {
        self.out
            .get(from)
            .into_iter()
            .flat_map(|s| s.iter())
    }

    /// Iterate every distinct `from`-literal currently registered
    /// in the graph.  Used by the saturator to snapshot the key
    /// set before iterating mutations.
    pub fn keys_iter(&self) -> impl Iterator<Item = &Lit> {
        self.out.keys()
    }

    /// §3.3 phase 2 — element-wise intersection of two
    /// implication graphs.  Returns a fresh graph that
    /// contains an edge `(from, to)` iff *both* `self` and
    /// `other` contained it.  Used by the dilemma rule to
    /// compute the implication set common to two case-split
    /// branches.
    pub fn intersect_with(&self, other: &ImplicationGraph) -> ImplicationGraph {
        let mut out = ImplicationGraph::new();
        for (from, succs) in &self.out {
            if let Some(other_succs) = other.out.get(from) {
                for to in succs {
                    if other_succs.contains(to) {
                        out.add(from.clone(), to.clone());
                    }
                }
            }
        }
        out
    }

    /// Drain every `(from, to)` edge into an owned `Vec`.
    /// Useful for the dilemma-rule fold-back step which
    /// otherwise would have to clone every edge twice.
    pub fn into_edges(self) -> Vec<(Lit, Lit)> {
        let mut out = Vec::new();
        for (from, succs) in self.out {
            for to in succs {
                out.push((from.clone(), to));
            }
        }
        out
    }

    /// `true` iff `from ⇒ to` is recorded in the graph.  Does
    /// **not** consider transitive closure — see
    /// [`crate::Saturator::saturate_simple`] to materialise that first.
    pub fn implies(&self, from: &Lit, to: &Lit) -> bool {
        self.out.get(from).map_or(false, |s| s.contains(to))
    }

    /// Detect a contradiction in the saturated graph: any literal
    /// `l` such that `l ⇒ ¬l`.  Returns the witness chain
    /// `[l, …, ¬l]` reconstructed via BFS over the implication
    /// graph; the chain is the minimal proof of UNSAT the AOT
    /// stage can hand to the certifier.  Returns `None` when no
    /// such literal exists.
    pub fn detect_contradiction(&self) -> Option<Vec<Lit>> {
        for from in self.out.keys() {
            let target = from.negated();
            if let Some(chain) = self.bfs_path(from, &target) {
                return Some(chain);
            }
        }
        None
    }

    fn bfs_path(&self, start: &Lit, goal: &Lit) -> Option<Vec<Lit>> {
        use std::collections::VecDeque;
        let mut parent: BTreeMap<Lit, Lit> = BTreeMap::new();
        let mut q: VecDeque<Lit> = VecDeque::new();
        q.push_back(start.clone());
        while let Some(cur) = q.pop_front() {
            for s in self.successors(&cur) {
                if s == goal {
                    let mut chain = vec![s.clone(), cur.clone()];
                    let mut at = &cur;
                    while let Some(p) = parent.get(at) {
                        chain.push(p.clone());
                        at = p;
                    }
                    chain.reverse();
                    return Some(chain);
                }
                if parent.contains_key(s) || s == start {
                    continue;
                }
                parent.insert(s.clone(), cur.clone());
                q.push_back(s.clone());
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_is_idempotent() {
        let mut g = ImplicationGraph::new();
        assert!(g.add(Lit::pos("a"), Lit::pos("b")));
        assert!(!g.add(Lit::pos("a"), Lit::pos("b")));
        assert_eq!(g.edge_count(), 1);
    }

    #[test]
    fn lit_negation_flips_polarity_only() {
        let p = Lit::pos("x");
        let np = p.negated();
        assert_eq!(np.atom, "x");
        assert!(!np.polarity);
        assert_eq!(np.negated(), p);
    }

    #[test]
    fn detect_contradiction_finds_direct_self_loop() {
        // a ⇒ ¬a directly.
        let mut g = ImplicationGraph::new();
        g.add(Lit::pos("a"), Lit::neg("a"));
        let chain = g.detect_contradiction().unwrap();
        // Witness: [a, ¬a].
        assert_eq!(chain, vec![Lit::pos("a"), Lit::neg("a")]);
    }

    #[test]
    fn detect_contradiction_traverses_intermediate_steps() {
        // a ⇒ b ⇒ ¬a.  BFS reconstructs [a, b, ¬a].
        let mut g = ImplicationGraph::new();
        g.add(Lit::pos("a"), Lit::pos("b"));
        g.add(Lit::pos("b"), Lit::neg("a"));
        let chain = g.detect_contradiction().unwrap();
        assert_eq!(chain, vec![Lit::pos("a"), Lit::pos("b"), Lit::neg("a")]);
    }

    #[test]
    fn detect_contradiction_returns_none_on_consistent_graph() {
        let mut g = ImplicationGraph::new();
        g.add(Lit::pos("a"), Lit::pos("b"));
        g.add(Lit::pos("b"), Lit::pos("c"));
        assert!(g.detect_contradiction().is_none());
    }
}
