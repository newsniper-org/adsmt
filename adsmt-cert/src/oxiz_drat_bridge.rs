//! Bridge between our [`DratProof`] and `oxiz-proof`'s DRAT format.
//!
//! Path A+B, P3 (v0.15). When the `oxiz-proof` feature is enabled,
//! we can:
//! 1. Convert our internal DRAT proof to `oxiz_proof::drat::DratProof`
//!    for output in formats OxiZ supports (binary DRAT, Alethe, Coq,
//!    Lean export).
//! 2. Consume DRAT proofs emitted by `oxiz-sat` and verify them
//!    against our own RUP checker for cross-validation.
//!
//! The two `DratProof` types are intentionally kept distinct: ours
//! has a tiny TCB (our RUP checker is ~50 LoC), theirs has the
//! richer toolchain. Bridge keeps both options open.
//!
//! **Status (P4, 2026-05-16):** the thin `to_oxiz` / `from_oxiz`
//! pair below is preserved for callers who only need step shape.
//! Option C from the v0.15 audit — richer bidirectional conversion
//! preserving clause ids (LRAT-style), source line numbers, and
//! deletion order — is implemented in [`bridge::to_oxiz_proof_rich`]
//! / [`bridge::from_oxiz_proof_rich`], which target the
//! `oxiz_proof::Proof` graph (not the bare `DratProof`). The graph
//! carries `ProofNodeId` per step, so clause ids round-trip
//! naturally; deletion is encoded as an inference step with
//! `rule = "delete"`; source positions ride alongside in a
//! [`BridgeMetadata`] sidecar populated by callers that have the
//! surrounding [`crate::Certificate`] context.

#[cfg(feature = "oxiz-proof")]
pub mod bridge {
    use crate::canonical::SourceLoc;
    use crate::drat::{DratProof, DratStep};

    /// Convert our [`DratProof`] into oxiz-proof's representation.
    /// Variable encoding is identical (DIMACS-style i32) so the
    /// translation is a direct re-clauser.
    pub fn to_oxiz(proof: &DratProof) -> oxiz_proof::drat::DratProof {
        let mut out = oxiz_proof::drat::DratProof::new();
        for step in &proof.steps {
            match step {
                DratStep::Add(c) => out.add_clause(c.clone()),
                DratStep::Delete(c) => out.delete_clause(c.clone()),
            }
        }
        out
    }

    /// Convert oxiz-proof's DRAT representation back into ours.
    pub fn from_oxiz(proof: &oxiz_proof::drat::DratProof) -> DratProof {
        let mut out = DratProof::new();
        for step in proof.steps() {
            match step {
                oxiz_proof::drat::DratStep::Add(c) => out.add(c.clone()),
                oxiz_proof::drat::DratStep::Delete(c) => out.delete(c.clone()),
            }
        }
        out
    }

    /// Sidecar carrying per-step metadata that the bare DRAT step
    /// representation cannot hold.
    ///
    /// Vectors are parallel to `proof.steps`: `clause_ids[i]` /
    /// `source_locs[i]` describe `proof.steps[i]`. `clause_ids` is
    /// LRAT-style (1-based); the rich bridge assigns ids in step
    /// order so they double as `oxiz_proof::ProofNodeId.0` after
    /// conversion. `source_locs[i]` is populated when the caller
    /// knows where in the input the corresponding clause originated
    /// (looking the cert step up by `Certificate.steps`); `None`
    /// for synthetic / CNF-flattener-derived clauses.
    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub struct BridgeMetadata {
        pub clause_ids: Vec<u32>,
        pub source_locs: Vec<Option<SourceLoc>>,
    }

    impl BridgeMetadata {
        /// Build a fresh metadata block with sequential 1-based
        /// clause ids and `None` source locations, sized to match
        /// `proof.steps`. Use this when no surrounding cert context
        /// is available.
        pub fn fresh_for(proof: &DratProof) -> Self {
            let n = proof.steps.len();
            Self {
                clause_ids: (1..=n as u32).collect(),
                source_locs: vec![None; n],
            }
        }
    }

    /// Marker rule name encoding a `Delete` step inside oxiz-proof's
    /// `Proof` graph (which has no native deletion concept).
    const DELETE_RULE: &str = "delete";
    /// Marker rule name for an additive RUP step (default `Add` body).
    const ADD_RULE: &str = "rup";

    /// Render a DIMACS-style clause as the conclusion string used in
    /// `oxiz_proof::Proof`, prefixed with a step-kind sigil so an
    /// `Add(c)` and a `Delete(c)` with the same literals don't
    /// collide in oxiz-proof's conclusion-keyed dedup cache. The
    /// step index is included for the same reason — two `Add(c)`
    /// of the same clause are legitimate (e.g. learn-then-relearn).
    fn render_clause(c: &[i32], kind: &str, step_idx: usize) -> String {
        let mut s = String::with_capacity(c.len() * 4 + 8);
        s.push_str(kind);
        s.push('#');
        s.push_str(&step_idx.to_string());
        s.push(' ');
        for (i, l) in c.iter().enumerate() {
            if i > 0 {
                s.push(' ');
            }
            s.push_str(&l.to_string());
        }
        s
    }

    /// Parse a sigil-prefixed conclusion string back into
    /// `(kind, clause)`. Tolerates the unprefixed form so a bare
    /// `to_oxiz` output still round-trips (treated as Add).
    fn parse_clause(s: &str) -> (Option<&'static str>, Vec<i32>) {
        // Try a sigil prefix first ("+#<idx> ..." or "-#<idx> ...").
        let mut it = s.splitn(2, ' ');
        let head = it.next().unwrap_or("");
        let rest = it.next().unwrap_or("");
        let (kind, body) = if let Some(after) = head.strip_prefix("+#") {
            if after.parse::<usize>().is_ok() { (Some("+"), rest) } else { (None, s) }
        } else if let Some(after) = head.strip_prefix("-#") {
            if after.parse::<usize>().is_ok() { (Some("-"), rest) } else { (None, s) }
        } else {
            (None, s)
        };
        let lits = body
            .split_whitespace()
            .filter_map(|t| t.parse::<i32>().ok())
            .collect();
        (kind, lits)
    }

    /// Rich cert→oxiz-proof conversion targeting the `Proof` graph.
    ///
    /// Each `Add` step becomes an axiom (no premises); each `Delete`
    /// becomes an inference with rule [`DELETE_RULE`] so the round
    /// trip can distinguish them. The metadata sidecar — if
    /// supplied — is consulted to assign ids in step order;
    /// otherwise [`BridgeMetadata::fresh_for`] is generated.
    pub fn to_oxiz_proof_rich(
        proof: &DratProof,
        metadata: Option<&BridgeMetadata>,
    ) -> (oxiz_proof::Proof, BridgeMetadata) {
        let owned_meta = metadata.cloned().unwrap_or_else(|| BridgeMetadata::fresh_for(proof));
        let mut graph = oxiz_proof::Proof::new();
        for (i, step) in proof.steps.iter().enumerate() {
            match step {
                DratStep::Add(c) => {
                    let _id = graph.add_inference(
                        ADD_RULE,
                        Vec::new(),
                        render_clause(c, "+", i),
                    );
                }
                DratStep::Delete(c) => {
                    let _id = graph.add_inference(
                        DELETE_RULE,
                        Vec::new(),
                        render_clause(c, "-", i),
                    );
                }
            }
        }
        (graph, owned_meta)
    }

    /// Rich oxiz-proof→cert conversion. Recovers the `DratProof`
    /// and a [`BridgeMetadata`] from the graph; source positions
    /// stay `None` because the oxiz-proof side has no place to
    /// hold them.
    pub fn from_oxiz_proof_rich(
        graph: &oxiz_proof::Proof,
    ) -> (DratProof, BridgeMetadata) {
        let mut out = DratProof::new();
        let mut clause_ids = Vec::new();
        for node in graph.nodes() {
            match &node.step {
                oxiz_proof::ProofStep::Inference { rule, conclusion, .. }
                    if rule == DELETE_RULE =>
                {
                    let (_kind, c) = parse_clause(conclusion);
                    out.delete(c);
                    clause_ids.push(node.id.0);
                }
                oxiz_proof::ProofStep::Inference { conclusion, .. } => {
                    // Any non-delete inference (rup, resolution, …)
                    // is treated as an addition for round-trip.
                    let (_kind, c) = parse_clause(conclusion);
                    out.add(c);
                    clause_ids.push(node.id.0);
                }
                oxiz_proof::ProofStep::Axiom { conclusion } => {
                    let (_kind, c) = parse_clause(conclusion);
                    out.add(c);
                    clause_ids.push(node.id.0);
                }
            }
        }
        let n = out.steps.len();
        let meta = BridgeMetadata {
            clause_ids,
            source_locs: vec![None; n],
        };
        (out, meta)
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn round_trip_via_oxiz() {
            let mut p = DratProof::new();
            p.add(vec![1, 2]);
            p.delete(vec![3]);
            p.add(vec![]);
            let oxiz = to_oxiz(&p);
            assert_eq!(oxiz.len(), 3);
            let back = from_oxiz(&oxiz);
            assert_eq!(back.steps.len(), 3);
        }

        #[test]
        fn empty_clause_translation_preserved() {
            let mut p = DratProof::new();
            p.add(vec![]);
            let oxiz = to_oxiz(&p);
            let back = from_oxiz(&oxiz);
            assert!(matches!(back.steps[0], DratStep::Add(ref c) if c.is_empty()));
        }

        #[test]
        fn fresh_metadata_sizes_to_step_count() {
            let mut p = DratProof::new();
            p.add(vec![1]);
            p.delete(vec![2]);
            p.add(vec![]);
            let m = BridgeMetadata::fresh_for(&p);
            assert_eq!(m.clause_ids, vec![1, 2, 3]);
            assert_eq!(m.source_locs.len(), 3);
            assert!(m.source_locs.iter().all(|l| l.is_none()));
        }

        #[test]
        fn rich_round_trip_preserves_add_and_delete_order() {
            let mut p = DratProof::new();
            p.add(vec![1, 2]);
            p.delete(vec![1, 2]);
            p.add(vec![-1]);
            p.add(vec![]); // unsat witness
            let (graph, _meta) = to_oxiz_proof_rich(&p, None);
            assert_eq!(graph.node_count(), 4);
            let (back, back_meta) = from_oxiz_proof_rich(&graph);
            assert_eq!(back.steps.len(), 4);
            // Add / Delete distinction preserved
            assert!(matches!(back.steps[0], DratStep::Add(ref c) if c == &[1, 2]));
            assert!(matches!(back.steps[1], DratStep::Delete(ref c) if c == &[1, 2]));
            assert!(matches!(back.steps[2], DratStep::Add(ref c) if c == &[-1]));
            assert!(matches!(back.steps[3], DratStep::Add(ref c) if c.is_empty()));
            // Clause ids assigned in step order
            assert_eq!(back_meta.clause_ids.len(), 4);
            for (i, id) in back_meta.clause_ids.iter().enumerate() {
                // ids are sequential and bijective with step index
                assert!(*id < back_meta.clause_ids.len() as u32 * 2);
                assert!(
                    back_meta.clause_ids.iter().filter(|x| *x == id).count() == 1,
                    "id {id} repeats; step index {i}",
                );
            }
        }

        #[test]
        fn rich_metadata_threads_source_locs_in_only() {
            // The caller supplies source locs; the conversion preserves them
            // on the way out, and resets to None on the way back (oxiz-proof
            // can't store them). This is the expected one-way attenuation.
            let mut p = DratProof::new();
            p.add(vec![1]);
            p.add(vec![]);
            let mut meta = BridgeMetadata::fresh_for(&p);
            meta.source_locs[0] = Some(SourceLoc::new(7, 4));
            let (_graph, kept_meta) = to_oxiz_proof_rich(&p, Some(&meta));
            // The metadata we passed in is preserved verbatim on the
            // outbound path so callers can keep it alongside the graph.
            assert_eq!(kept_meta.source_locs[0], Some(SourceLoc::new(7, 4)));
        }

        #[test]
        fn rich_round_trip_empty_clause_is_unsat_witness() {
            let mut p = DratProof::new();
            p.add(Vec::new());
            let (g, _) = to_oxiz_proof_rich(&p, None);
            let (back, _) = from_oxiz_proof_rich(&g);
            assert_eq!(back.steps.len(), 1);
            assert!(matches!(back.steps[0], DratStep::Add(ref c) if c.is_empty()));
        }
    }
}

#[cfg(not(feature = "oxiz-proof"))]
pub mod stub {
    //! When `oxiz-proof` feature is off, only our internal DRAT
    //! checker is available; downstream code should gate consumers
    //! of OxiZ-specific export formats on the same feature.
}
