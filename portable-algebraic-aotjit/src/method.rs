//! §Phase3 — the "meta-method" half of the hybrid algebraic JIT.
//!
//! Where a [`crate::event::CdclTraceEvent`] stream is a META-TRACING
//! artifact (one linear solve path), a [`Method`] is a META-METHOD
//! artifact (a reusable compiled unit invoked across many queries),
//! after BacCaml's meta-hybrid model. The SMT mapping: the PRELUDE is
//! the stable "method" — its forced level-0 unit-propagation backbone
//! is goal-independent (appending a query goal can only *add* level-0
//! implications, never retract one — the monotonicity license), so the
//! prelude's clause-fold + its handle→atom resolver are compiled ONCE
//! and reused; the per-query GOAL is the "trace" layered on top.
//!
//! ## Honest scope
//!
//! Per the 2026-06-13 profile (`aot-jit-profile-finding` memory) the
//! production verdict path is already an O(1) digest compare, so this
//! carries **no wall-clock win on that path** today. Its value is:
//! (1) [`compose_digest`] is the SINGLE fold expression both the
//! region key and the verdict digest flow through — so a stale method
//! can never silently match a trace it should not (the split-fold
//! soundness footgun is structurally absent); (2) it is the additive
//! BacCaml-interop architecture (`MethodInvoke` + [`crate::replay::replay_hybrid`])
//! a second consumer (e.g. OxiZ) or a future frozen-state warm-start
//! can activate without a wire/contract change. The frozen-state
//! reuse, a `HybridPlan` dispatcher, and a `.method` sidecar are
//! deliberately deferred (YAGNI until a real second resolver shape).

use std::collections::HashMap;

use crate::digest::{combine_fold, fold_to_digest, ClauseFold};

/// The single source of truth for the §3.5.J exact-match digest: fold
/// the prelude half with the per-query delta half, then collapse.
///
/// Because [`combine_fold`] is an exact multiset homomorphism
/// (`combine(fold(P), fold(Q)) == fold(P ⊎ Q)`), this equals a
/// from-scratch `fold_to_digest(clause_set_fold(P ⊎ Q))`. Routing both
/// the host's live digest AND a [`Method::region_key`] through this one
/// expression is what makes the prelude/query split exist in exactly
/// ONE place — the soundness discipline the design rests on.
pub fn compose_digest(prelude_fold: ClauseFold, query_delta_fold: ClauseFold) -> [u8; 32] {
    fold_to_digest(combine_fold(prelude_fold, query_delta_fold))
}

/// A precompiled, reusable prelude unit — the meta-method.
///
/// Generic over the host's atom type `A` (e.g. the engine's hash-consed
/// term), so the crate stays solver-independent; the host builds the
/// resolver map once and hands it in.
#[derive(Clone, Debug)]
pub struct Method<A> {
    /// The prelude's clause-fold — the half [`compose_digest`] combines
    /// with the per-query delta. The method's IDENTITY.
    clause_fold: ClauseFold,
    /// Recorded-handle → atom resolver for the prelude's atoms (the
    /// rc.34.5 precomputed base, now owned by the method).
    atom_map: HashMap<u32, A>,
    /// `true` iff `atom_map` was built without a handle-hash collision
    /// in the prelude's atom domain (gates any term-dependent backstop,
    /// mirroring the engine's existing `atom_map_collision` discipline).
    collision: bool,
}

impl<A> Method<A> {
    /// Compile a method from its prelude clause-fold + handle resolver.
    pub fn new(clause_fold: ClauseFold, atom_map: HashMap<u32, A>, collision: bool) -> Self {
        Self {
            clause_fold,
            atom_map,
            collision,
        }
    }

    /// The region key: the prelude-only digest. Two methods are the
    /// same region iff this matches. Derived from `clause_fold` through
    /// the SAME [`compose_digest`] (with an empty delta) the verdict
    /// digest uses, so region and verdict can never disagree on what
    /// "the prelude" is.
    pub fn region_key(&self) -> [u8; 32] {
        compose_digest(self.clause_fold, crate::digest::EMPTY_FOLD)
    }

    /// The prelude clause-fold half — the host combines its per-query
    /// delta with this via [`compose_digest`] for the live digest.
    pub fn clause_fold(&self) -> ClauseFold {
        self.clause_fold
    }

    /// `true` iff the prelude atom domain was collision-free.
    pub fn is_collision_free(&self) -> bool {
        !self.collision
    }

    /// Resolve a recorded prelude-atom handle.
    pub fn resolve(&self, handle: u32) -> Option<&A> {
        self.atom_map.get(&handle)
    }

    /// Number of prelude atoms the method resolves.
    pub fn atom_count(&self) -> usize {
        self.atom_map.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::digest::{clause_set_fold, EMPTY_FOLD};

    fn clause(lits: &[(&'static str, bool)]) -> Vec<(&'static str, bool)> {
        lits.to_vec()
    }

    #[test]
    fn compose_digest_equals_whole_formula_digest() {
        // The homomorphism: compose(prelude, delta) == digest(prelude ⊎ delta).
        let prelude = vec![clause(&[("p", true)]), clause(&[("q", false)])];
        let query = vec![clause(&[("r", true)])];
        let pf = clause_set_fold(prelude.clone());
        let qf = clause_set_fold(query.clone());
        let whole: Vec<_> = prelude.into_iter().chain(query).collect();
        assert_eq!(compose_digest(pf, qf), fold_to_digest(clause_set_fold(whole)));
    }

    #[test]
    fn region_key_is_prelude_only_digest() {
        let prelude = vec![clause(&[("p", true)]), clause(&[("q", false)])];
        let pf = clause_set_fold(prelude.clone());
        let m: Method<u32> = Method::new(pf, HashMap::new(), false);
        // region_key == compose(prelude, empty) == digest(prelude).
        assert_eq!(m.region_key(), fold_to_digest(clause_set_fold(prelude)));
        // ...and composing an empty delta against the method reproduces it.
        assert_eq!(m.region_key(), compose_digest(m.clause_fold(), EMPTY_FOLD));
    }

    #[test]
    fn distinct_preludes_have_distinct_region_keys() {
        let a: Method<u32> = Method::new(clause_set_fold(vec![clause(&[("p", true)])]), HashMap::new(), false);
        let b: Method<u32> = Method::new(clause_set_fold(vec![clause(&[("p", false)])]), HashMap::new(), false);
        assert_ne!(a.region_key(), b.region_key());
    }

    #[test]
    fn resolve_returns_mapped_atom() {
        let mut map = HashMap::new();
        map.insert(7u32, "seven".to_string());
        let m = Method::new(EMPTY_FOLD, map, false);
        assert_eq!(m.resolve(7).map(String::as_str), Some("seven"));
        assert_eq!(m.resolve(9), None);
        assert_eq!(m.atom_count(), 1);
    }
}
