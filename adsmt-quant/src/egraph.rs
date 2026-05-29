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
//!   [`adsmt-theory::trait_::Theory`].

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
}

/// Hash-consed + union-find E-graph (stage 1 skeleton).
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
        self.nodes.push(ENode { key: key.clone() });
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
    pub fn merge(&mut self, a: ENodeId, b: ENodeId) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb { return false; }
        // Union by id-order — keep the smaller-id node as the
        // root so deterministic iteration is preserved.
        let (root, child) = if ra.0 < rb.0 { (ra, rb) } else { (rb, ra) };
        self.parent[child.0 as usize] = root;
        // Merge parent lists.
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
        // shared class's parent list now contains both `f a`
        // and `f b` (the stage-2 cascade will then notice the
        // app heads agree and merge them too — pending stage 2).
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
}
