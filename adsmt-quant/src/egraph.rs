//! v0.21 A.2 (stage 1) — incremental EUF E-graph skeleton.
//!
//! Builds the E-graph data structure that v0.19 A.3's
//! lightweight `learn_triggers` helper points at as its final
//! home. The current implementation is the **hash-consed +
//! union-find** skeleton:
//!
//! - Every term lowered into the graph is identified by an
//!   [`ENodeId`]; structurally equal terms share an id via
//!   the `hash_cons` map.
//! - An equality assertion (`a = b`) merges their
//!   representative classes via [`EGraph::merge`].
//! - The find operation walks the union-find parent chain
//!   with path compression so subsequent `find` calls are
//!   amortised O(α(n)).
//! - Congruence propagation — the EUF half — comes in **stage
//!   2**: when two nodes whose children are now in the same
//!   class become congruent, the merge needs to cascade. The
//!   stage-1 skeleton lays out the indexing required for that
//!   cascade (each class records its parent nodes), but does
//!   not yet fire the cascade.
//!
//! Stage roadmap:
//! - **Stage 1 (this commit)**: hash-cons + union-find +
//!   parent-list bookkeeping.
//! - **Stage 2**: congruence-closure cascade (`repair`/`upward
//!   merging`).
//! - **Stage 3**: incremental E-matching loop driven by
//!   [`crate::trigger::learn_triggers`].
//! - **Stage 4**: push/pop scope integration with
//!   `adsmt_theory::trait_::Theory`.

use std::collections::HashMap;
use std::sync::Arc;

use adsmt_core::{Term, Var};

/// Stable identifier for an E-node inside an [`EGraph`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ENodeId(u32);

/// Symbolic shape of an E-node — the head plus child ids. We
/// keep heads as strings (the term's printed form for atoms,
/// `"@app"` for applications, `"@lam:<ty>"` for lambdas) so
/// hash-consing doesn't have to depend on the full
/// [`adsmt_core::Term`] hash. The cost is one extra string
/// allocation per insert; in stage 3 we'll swap to an interned
/// symbol table.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ENodeKey {
    head: String,
    children: Vec<ENodeId>,
}

#[derive(Clone, Debug)]
struct ENode {
    /// Hash-cons key. Stable across merges (the key holds child
    /// ids, NOT child class ids — congruence-aware lookup walks
    /// through `find` before comparing). Stage 2's congruence
    /// cascade reads this to detect that two parents now point
    /// to congruent child classes.
    #[allow(dead_code)]
    key: ENodeKey,
    /// v0.21 A.2 stage 3 — the original [`Term`] that
    /// materialised this node. Retained so the EGraph can
    /// expose itself as a [`TermUniverse`] for the existing
    /// [`crate::ematch::EMatcher`] without rebuilding terms
    /// from the hash-cons key.
    term: Term,
}

/// Hash-consed + union-find E-graph.
#[derive(Default, Debug)]
pub struct EGraph {
    nodes: Vec<ENode>,
    /// Parent pointer per node — `parent[i] == i` means `i` is
    /// the class representative.
    parent: Vec<ENodeId>,
    /// Per-class list of parent E-nodes (nodes that mention
    /// this class as a child). Populated at insertion time and
    /// used by the stage-2 congruence cascade. Stage 1 already
    /// maintains it so stage 2 doesn't need a back-fill pass.
    class_parents: HashMap<ENodeId, Vec<ENodeId>>,
    /// Hash-cons: lookup-by-shape. Maps from key to the first
    /// E-node that materialised it.
    hash_cons: HashMap<ENodeKey, ENodeId>,
    /// v0.21 A.2 stage 4 — scope stack for incremental
    /// push/pop. Each entry is a full snapshot of the four
    /// hash/vec fields above; pop restores them in O(snapshot
    /// size). The naive clone-based snapshot is intentionally
    /// chosen over a delta-based scheme because adsmt's typical
    /// nesting depth (≤ 4) and graph size in solver tests make
    /// the clone cost negligible. A delta-based scheme can land
    /// later if profiling reveals it matters.
    scope_stack: Vec<EGraphSnapshot>,
}

#[derive(Clone, Debug)]
struct EGraphSnapshot {
    nodes: Vec<ENode>,
    parent: Vec<ENodeId>,
    class_parents: HashMap<ENodeId, Vec<ENodeId>>,
    hash_cons: HashMap<ENodeKey, ENodeId>,
}

impl EGraph {
    pub fn new() -> Self { Self::default() }

    pub fn len(&self) -> usize { self.nodes.len() }
    pub fn is_empty(&self) -> bool { self.nodes.is_empty() }

    /// Insert a [`Term`] into the graph and return the
    /// representative id of its class. Idempotent on
    /// α-equivalent terms (they hash-cons to the same id).
    pub fn add(&mut self, t: &Term) -> ENodeId {
        let (head, children) = self.lower(t);
        let key = ENodeKey { head, children: children.clone() };
        if let Some(&id) = self.hash_cons.get(&key) {
            return self.find(id);
        }
        let id = ENodeId(self.nodes.len() as u32);
        self.nodes.push(ENode {
            key: key.clone(),
            term: t.clone(),
        });
        self.parent.push(id);
        self.hash_cons.insert(key, id);
        for child in &children {
            self.class_parents
                .entry(self.find(*child))
                .or_default()
                .push(id);
        }
        id
    }

    /// Return the class representative for `id`.
    pub fn find(&self, mut id: ENodeId) -> ENodeId {
        // Iterative find without path compression — stage 1 keeps
        // the graph immutable on lookup so the API stays
        // `&self`. Stage 2's congruence cascade requires `&mut
        // self` already, so path compression will land there.
        loop {
            let p = self.parent[id.0 as usize];
            if p == id { return id; }
            id = p;
        }
    }

    /// Merge the classes of `a` and `b`. Returns `true` when
    /// the merge changed the union-find (i.e. they were in
    /// distinct classes), `false` when they were already
    /// equal.
    ///
    /// **Stage 2** — after the primitive union, runs the
    /// congruence-closure cascade (`Self::repair`, internal) so that
    /// peers `f(a)` and `f(b)` become equivalent whenever
    /// `a = b` is asserted. The cascade is the "upward
    /// merging" half of EUF and is what makes the E-graph
    /// useful as a backend for theory combination.
    pub fn merge(&mut self, a: ENodeId, b: ENodeId) -> bool {
        let changed = self.union(a, b);
        if changed {
            self.repair(self.find(a));
        }
        changed
    }

    /// Primitive union-find merge, no congruence cascade.
    /// Exposed as `pub(crate)` so the cascade can re-enter
    /// without re-triggering itself.
    fn union(&mut self, a: ENodeId, b: ENodeId) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb { return false; }
        let (root, child) = if ra.0 < rb.0 { (ra, rb) } else { (rb, ra) };
        self.parent[child.0 as usize] = root;
        let child_parents = self
            .class_parents
            .remove(&child)
            .unwrap_or_default();
        self.class_parents
            .entry(root)
            .or_default()
            .extend(child_parents);
        true
    }

    /// v0.21 A.2 stage 2 — congruence-closure cascade.
    ///
    /// Scans the parent E-nodes of `class`, groups them by
    /// (head, normalized-child-class-ids), and merges any
    /// parents that now share a normalised shape. Each new
    /// merge enqueues the resulting class so the cascade
    /// reaches a fixpoint. Worst-case linear in the parent-
    /// edge count of the merged class (no path compression yet).
    fn repair(&mut self, class: ENodeId) {
        let mut worklist: Vec<ENodeId> = vec![class];
        while let Some(c) = worklist.pop() {
            let c = self.find(c);
            let parents = self.class_parents(c);
            let mut by_norm_key: HashMap<(String, Vec<ENodeId>), ENodeId> =
                HashMap::new();
            for p_id in parents {
                let p_node = &self.nodes[p_id.0 as usize];
                let norm: Vec<ENodeId> = p_node
                    .key
                    .children
                    .iter()
                    .map(|ch| self.find(*ch))
                    .collect();
                let key = (p_node.key.head.clone(), norm);
                if let Some(&existing) = by_norm_key.get(&key) {
                    if self.union(p_id, existing) {
                        worklist.push(self.find(p_id));
                    }
                } else {
                    by_norm_key.insert(key, p_id);
                }
            }
        }
    }

    /// Are `a` and `b` in the same E-class?
    pub fn equivalent(&self, a: ENodeId, b: ENodeId) -> bool {
        self.find(a) == self.find(b)
    }

    /// Parent E-nodes of a class — the nodes that mention this
    /// class as a child. Stage-2 congruence cascade walks this
    /// list to find newly-congruent peers after a merge.
    pub fn class_parents(&self, id: ENodeId) -> Vec<ENodeId> {
        self.class_parents
            .get(&self.find(id))
            .cloned()
            .unwrap_or_default()
    }

    /// v0.21 A.2 stage 3 — return every term that lives in
    /// the class of `id`. The returned slice is in insertion
    /// order so deterministic iteration is preserved.
    pub fn terms_in_class(&self, id: ENodeId) -> Vec<Term> {
        let root = self.find(id);
        let mut out: Vec<Term> = Vec::new();
        for (i, n) in self.nodes.iter().enumerate() {
            if self.find(ENodeId(i as u32)) == root {
                out.push(n.term.clone());
            }
        }
        out
    }

    /// v0.21 A.2 stage 3 — project every E-node's term into a
    /// [`TermUniverse`](crate::ematch::TermUniverse) so the existing
    /// [`crate::ematch::EMatcher`] can run against the E-graph
    /// without re-implementation. The projection is union-find
    /// blind — every term ever added survives, congruence
    /// equalities are *not* materialised as duplicates (the
    /// matcher already handles α-equivalence on individual
    /// universe entries).
    pub fn as_universe(&self) -> crate::ematch::TermUniverse {
        let mut u = crate::ematch::TermUniverse::new();
        for n in &self.nodes {
            u.insert(n.term.clone());
        }
        u
    }

    /// v0.21 A.2 stage 4 — push a snapshot of the graph onto
    /// the scope stack. Subsequent inserts and merges are
    /// rolled back by a matching [`Self::pop`] call.
    pub fn push(&mut self) {
        self.scope_stack.push(EGraphSnapshot {
            nodes: self.nodes.clone(),
            parent: self.parent.clone(),
            class_parents: self.class_parents.clone(),
            hash_cons: self.hash_cons.clone(),
        });
    }

    /// Pop the top `levels` snapshots, restoring the graph
    /// state captured by each [`Self::push`]. Calls with no
    /// matching push are silently ignored — same semantics
    /// as `adsmt_theory`'s `Theory::pop`.
    pub fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if let Some(snap) = self.scope_stack.pop() {
                self.nodes = snap.nodes;
                self.parent = snap.parent;
                self.class_parents = snap.class_parents;
                self.hash_cons = snap.hash_cons;
            }
        }
    }

    /// Current scope depth — the number of pending pushes.
    pub fn scope_depth(&self) -> u32 {
        self.scope_stack.len() as u32
    }

    /// Lower a Term into (head_symbol, child_ids), recursing
    /// into the children via [`EGraph::add`].
    fn lower(&mut self, t: &Term) -> (String, Vec<ENodeId>) {
        match t {
            Term::Var(v) => (format!("var:{}:{}", v.name, v.ty), Vec::new()),
            Term::Const(c) => (format!("const:{}:{}", c.name, c.ty), Vec::new()),
            Term::App(f, x) => {
                let f_id = self.add(f);
                let x_id = self.add(x);
                ("@app".into(), vec![f_id, x_id])
            }
            Term::Lam(v, body) => {
                let body_id = self.add(body);
                let _ = v as &Arc<Var>;
                // Bound-variable α-renaming would need a real
                // de Bruijn lowering; stage 1 keeps lambdas
                // structurally distinct on body id alone, which
                // is conservative (some α-equivalent lambdas
                // hash-cons separately).
                (format!("@lam:{}", v.ty), vec![body_id])
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Type};

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    #[test]
    fn add_var_returns_same_id_on_alpha_eq() {
        let mut g = EGraph::new();
        let a1 = g.add(&Term::var("a", int_()));
        let a2 = g.add(&Term::var("a", int_()));
        assert_eq!(a1, a2);
    }

    #[test]
    fn add_const_hash_conses_distinct_from_var() {
        let mut g = EGraph::new();
        let v = g.add(&Term::var("a", int_()));
        let c = g.add(&Term::const_("a", int_()));
        assert_ne!(v, c);
    }

    #[test]
    fn merge_unifies_classes() {
        let mut g = EGraph::new();
        let a = g.add(&Term::var("a", int_()));
        let b = g.add(&Term::var("b", int_()));
        assert!(!g.equivalent(a, b));
        let changed = g.merge(a, b);
        assert!(changed);
        assert!(g.equivalent(a, b));
        // Second merge is a no-op.
        let changed2 = g.merge(a, b);
        assert!(!changed2);
    }

    #[test]
    fn application_lowers_into_app_node_with_child_ids() {
        let mut g = EGraph::new();
        let f = Term::const_("f", Type::fun(int_(), int_()).unwrap());
        let a = Term::var("a", int_());
        let fa = Term::app(f, a).unwrap();
        let id = g.add(&fa);
        // The class includes itself.
        assert_eq!(g.find(id), id);
        // The `f` and `a` sub-nodes were inserted with their own ids.
        assert!(g.len() >= 3);
    }

    #[test]
    fn class_parents_records_applications_of_a_class() {
        // `f a` and `f a`: hash-consed to the same node. `a`'s
        // class should list the `f a` node as a parent.
        let mut g = EGraph::new();
        let f = Term::const_("f", Type::fun(int_(), int_()).unwrap());
        let a = Term::var("a", int_());
        let a_id = g.add(&a);
        let fa_id = g.add(&Term::app(f, a).unwrap());
        let parents = g.class_parents(a_id);
        assert!(parents.contains(&fa_id));
    }

    #[test]
    fn merge_consolidates_class_parent_lists() {
        // (f a), (f b) — distinct E-nodes. Merge a = b: the
        // shared class's parent list contains both `f a` and
        // `f b`. With the stage-2 cascade in place, `f a` and
        // `f b` are now also in the same E-class.
        let mut g = EGraph::new();
        let f = Term::const_("f", Type::fun(int_(), int_()).unwrap());
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let a_id = g.add(&a);
        let b_id = g.add(&b);
        let fa = g.add(&Term::app(f.clone(), a).unwrap());
        let fb = g.add(&Term::app(f, b).unwrap());
        assert_ne!(fa, fb);
        g.merge(a_id, b_id);
        let parents = g.class_parents(a_id);
        assert!(parents.contains(&fa));
        assert!(parents.contains(&fb));
    }

    // === Stage 2 — congruence-closure cascade ===

    #[test]
    fn congruence_cascade_merges_fa_and_fb_after_a_equals_b() {
        // `(f a)` and `(f b)` start distinct; merging `a = b`
        // upward-merges them via the stage-2 cascade.
        let mut g = EGraph::new();
        let f = Term::const_("f", Type::fun(int_(), int_()).unwrap());
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let a_id = g.add(&a);
        let b_id = g.add(&b);
        let fa = g.add(&Term::app(f.clone(), a).unwrap());
        let fb = g.add(&Term::app(f, b).unwrap());
        assert!(!g.equivalent(fa, fb));
        g.merge(a_id, b_id);
        assert!(
            g.equivalent(fa, fb),
            "congruence cascade should equate (f a) and (f b)"
        );
    }

    #[test]
    fn congruence_cascade_chains_through_two_hops() {
        // `(f (g a))` and `(f (g b))` with `a = b`:
        // - merge a = b
        // - cascade lifts `(g a) = (g b)`
        // - cascade lifts `(f (g a)) = (f (g b))`
        let mut g = EGraph::new();
        let int_to_int = Type::fun(int_(), int_()).unwrap();
        let g_fn = Term::const_("g", int_to_int.clone());
        let f = Term::const_("f", int_to_int);
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let a_id = g.add(&a);
        let b_id = g.add(&b);
        let ga = Term::app(g_fn.clone(), a).unwrap();
        let gb = Term::app(g_fn, b).unwrap();
        let fga = g.add(&Term::app(f.clone(), ga).unwrap());
        let fgb = g.add(&Term::app(f, gb).unwrap());
        assert!(!g.equivalent(fga, fgb));
        g.merge(a_id, b_id);
        assert!(g.equivalent(fga, fgb), "two-hop cascade");
    }

    // === Stage 3 — TermUniverse / EMatcher integration ===

    #[test]
    fn terms_in_class_returns_every_member_after_merges() {
        let mut g = EGraph::new();
        let a = g.add(&Term::var("a", int_()));
        let b = g.add(&Term::var("b", int_()));
        let c = g.add(&Term::var("c", int_()));
        g.merge(a, b);
        g.merge(b, c);
        let members = g.terms_in_class(a);
        assert_eq!(members.len(), 3);
    }

    #[test]
    fn as_universe_seeds_a_matcher_run() {
        // Add `P a`, `P b` to the graph; obtain the universe;
        // run the existing EMatcher on it.
        use crate::ematch::EMatcher;
        use crate::trigger::Trigger;
        let mut g = EGraph::new();
        let int_ty = int_();
        let p_const =
            Term::const_("P", Type::fun(int_ty.clone(), Type::bool_()).unwrap());
        let a = Term::const_("a", int_ty.clone());
        let b = Term::const_("b", int_ty.clone());
        g.add(&Term::app(p_const.clone(), a).unwrap());
        g.add(&Term::app(p_const.clone(), b).unwrap());

        let universe = g.as_universe();
        // Pattern: P x with x flex.
        let x = std::sync::Arc::new(adsmt_core::Var {
            name: "x".into(),
            ty: int_ty,
        });
        let pattern = Term::app(p_const, Term::Var(x.clone())).unwrap();
        let trig = Trigger::single(pattern, vec![x]);
        let matcher = EMatcher::new(&universe);
        let insts = matcher.match_trigger(&trig);
        assert_eq!(insts.len(), 2, "P a and P b both match");
    }

    // === Stage 4 — push/pop scope ===

    #[test]
    fn push_pop_round_trips_an_inserted_node() {
        let mut g = EGraph::new();
        let a_id = g.add(&Term::var("a", int_()));
        g.push();
        let b_id = g.add(&Term::var("b", int_()));
        g.merge(a_id, b_id);
        assert!(g.equivalent(a_id, b_id));
        g.pop(1);
        // After pop, the b insertion + merge are undone.
        // a's class membership: just `a` again.
        let members = g.terms_in_class(a_id);
        assert_eq!(members.len(), 1);
        assert_eq!(g.scope_depth(), 0);
    }

    #[test]
    fn nested_push_pop_restores_each_level() {
        // Snapshot semantics: `push` captures the *current*
        // state, `pop` rolls back to that snapshot. Set the
        // intended state, then push, then mutate.
        let mut g = EGraph::new();
        let a = g.add(&Term::var("a", int_()));
        // Snapshot 1 — { a alone }
        g.push();
        let b = g.add(&Term::var("b", int_()));
        g.merge(a, b);
        // Snapshot 2 — { a, b merged }
        g.push();
        let c = g.add(&Term::var("c", int_()));
        g.merge(a, c);
        // Now a+b+c.
        assert_eq!(g.terms_in_class(a).len(), 3);
        g.pop(1);
        // Restored to snapshot 2: a+b merged, no c.
        assert_eq!(g.terms_in_class(a).len(), 2);
        g.pop(1);
        // Restored to snapshot 1: only a.
        assert_eq!(g.terms_in_class(a).len(), 1);
        assert_eq!(g.scope_depth(), 0);
    }

    #[test]
    fn pop_more_than_pushed_is_silent_no_op() {
        let mut g = EGraph::new();
        let _ = g.add(&Term::var("a", int_()));
        // No push has been issued.
        g.pop(5);
        // Graph still holds the original insert.
        assert_eq!(g.len(), 1);
    }

    #[test]
    fn congruence_cascade_does_not_overmerge_different_heads() {
        // `(f a)` vs `(g a)` — same child class, different
        // head ⇒ stay distinct after merging a = anything else.
        let mut g = EGraph::new();
        let int_to_int = Type::fun(int_(), int_()).unwrap();
        let f = Term::const_("f", int_to_int.clone());
        let g_fn = Term::const_("g", int_to_int);
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let a_id = g.add(&a);
        let b_id = g.add(&b);
        let fa = g.add(&Term::app(f, a).unwrap());
        let ga = g.add(&Term::app(g_fn, b).unwrap());
        g.merge(a_id, b_id);
        assert!(!g.equivalent(fa, ga), "different heads must not merge");
    }
}
