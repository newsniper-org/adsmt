//! `.luart-cdcl` v1 CDCL section — the §3.5.A layer of the
//! verus-fork JIT-on-AOT-prelude pipeline.
//!
//! v0 `.luart` ends at the assertion list (per `pool.rs` /
//! `writer.rs`).  v1 extends it with a *post-flatten* snapshot of
//! the CDCL scope-0 state CDCL would arrive at right after
//! asserting every prelude clause and running BCP to fixpoint
//! without ever making a decision.  Reloading the artefact
//! restores that state directly so the per-query `(check-sat)`
//! skips the prelude's flatten + initial BCP work entirely.
//!
//! ## v1 layout
//!
//! All multi-byte fields are little-endian; the section sits
//! immediately after the v0 assertion-list bytes.  v0 readers
//! that stop at the v0 boundary ignore the v1 bytes silently
//! (the cursor never reads past the v0 `assert_len` count).
//!
//! ```text
//! ┌─ v1 CDCL section ──────────────────────────────────────────┐
//! │ binary_sha256  : [u8; 32]    ← SHA-256 of the lu-smt       │
//! │                                binary that produced the    │
//! │                                artefact.  Catches silent   │
//! │                                tooling drift the           │
//! │                                source-level                │
//! │                                `flatten_version` knob      │
//! │                                misses (toolchain bump,     │
//! │                                `-C target-feature`,        │
//! │                                feature-flag shift inside   │
//! │                                adsmt-engine).              │
//! │ flatten_version: u32 LE      ← bumped on any breaking      │
//! │                                change to                   │
//! │                                `flatten_to_clauses`        │
//! │                                semantics                   │
//! │ clauses_len    : u64 LE                                    │
//! │ ── clause entries ───────────────────────────────────────  │
//! │ each: lit_count:u32 + (atom_pool_idx:u32 polarity:u8)*    │
//! │ trail_len      : u64 LE                                    │
//! │ ── trail entries ───────────────────────────────────────── │
//! │ each: atom_pool_idx:u32 + polarity:u8 +                   │
//! │       reason_clause_idx:i64  (-1 = derived from prelude    │
//! │                               only, no per-query           │
//! │                               antecedent)                  │
//! │ watch_count    : u64 LE                                    │
//! │ ── watch entries ───────────────────────────────────────── │
//! │ each: atom_pool_idx:u32 + polarity:u8 +                   │
//! │       watching_clauses_len:u32 + clauses:Vec<u32>          │
//! │ vsids_count    : u64 LE                                    │
//! │ ── vsids entries ───────────────────────────────────────── │
//! │ each: atom_pool_idx:u32 + activity:f64                    │
//! │ saved_phase_count : u64 LE                                 │
//! │ ── saved-phase entries ─────────────────────────────────── │
//! │ each: atom_pool_idx:u32 + polarity:u8                     │
//! └────────────────────────────────────────────────────────────┘
//! ```
//!
//! Per the verus-fork §3.5 counter-ack §(b): `watch_count` is
//! `u64` (matching v0 `pool_len` / `assert_len`); inner
//! `watching_clauses` element type is fixed-`u32`.  v2 (if
//! prelude sizes ever exceed `2³² ≈ 4 × 10⁹` clauses) bumps the
//! format-version rather than introducing a permanent gate byte.

use std::io::Write;

/// On-disk format version for the CDCL section.  Separate from
/// `LUART_VERSION` (which gates the v0 pool / assertion shape)
/// so the two can evolve independently — a v0 artefact without
/// the CDCL extension stays version 0, and a v1 artefact may or
/// may not carry the CDCL section depending on whether the bake
/// side passed `--aot-include-cdcl`.
pub const LUART_CDCL_VERSION: u32 = 1;

/// Decoded clause entry: a CNF clause whose literals reference
/// atoms by their v0 pool index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CdclClause {
    /// Each entry is `(atom_pool_idx, polarity)`.  `polarity =
    /// true` for a positive literal, `false` for negative.
    pub lits: Vec<(u32, bool)>,
}

/// Decoded trail entry — one assignment on the prelude-only
/// BCP fixpoint that the bake side captured.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrailEntry {
    pub atom_pool_idx: u32,
    pub polarity: bool,
    /// `-1` marks an entry derived purely from prelude clauses
    /// with no per-query antecedent dependency.  Other values
    /// reference a clause in `CdclSection::clauses` by index.
    pub reason_clause_idx: i64,
}

/// Decoded watch-set entry — for a given `(atom, polarity)`
/// slot, the list of clause indices currently watching it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WatchEntry {
    pub atom_pool_idx: u32,
    pub polarity: bool,
    pub watching_clauses: Vec<u32>,
}

/// Decoded VSIDS-activity entry.  `f64` is the in-engine
/// activity scalar; the bake side captures it verbatim so the
/// per-query CDCL inherits the prelude's prioritisation.
#[derive(Clone, Debug, PartialEq)]
pub struct VsidsEntry {
    pub atom_pool_idx: u32,
    pub activity: f64,
}

/// Decoded phase-saving entry — the polarity the prelude's
/// CDCL saw the atom take at its last assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SavedPhaseEntry {
    pub atom_pool_idx: u32,
    pub polarity: bool,
}

/// §3.3 / §3.5.A v1.1 — one directed implication edge of the
/// Stålmarck-saturated propositional skeleton baked into the
/// `.luart-cdcl` v1 artefact.  An edge `(from, to)` records
/// the implication
/// `(from_atom_pool_idx, from_polarity) ⇒ (to_atom_pool_idx,
///  to_polarity)`.  CDCL replays the saturated graph as a
/// head-start clause set on every per-query `(check-sat)`.
///
/// The graph is appended *after* the v1 phase-save section so
/// readers built for the v1.0 layout (no Stålmarck section)
/// silently ignore the trailing bytes; readers built for v1.1
/// pick the section up by reading the trailing
/// `stalmarck_edges_len: u64` slot when the cursor has not
/// reached the buffer's end.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StalmarckEdge {
    pub from_atom_pool_idx: u32,
    pub from_polarity: bool,
    pub to_atom_pool_idx: u32,
    pub to_polarity: bool,
}

/// Full decoded CDCL section.
#[derive(Clone, Debug)]
pub struct CdclSection {
    /// SHA-256 of the `lu-smt` binary that baked this section.
    pub binary_sha256: [u8; 32],
    /// `flatten_to_clauses` semantic version; engine bumps on
    /// any breaking change to the flattener.
    pub flatten_version: u32,
    pub clauses: Vec<CdclClause>,
    pub trail: Vec<TrailEntry>,
    pub watches: Vec<WatchEntry>,
    pub vsids: Vec<VsidsEntry>,
    pub saved_phase: Vec<SavedPhaseEntry>,
    /// §3.3 / §3.5.A v1.1 — Stålmarck-saturated propositional
    /// implication graph baked alongside the CDCL state.  The
    /// CDCL fast path consumes the edges as a head-start
    /// implication set on every per-query `(check-sat)`.
    /// Empty for v1.0 bakers and for v1.1 bakers that did not
    /// run [`adsmt_stalmarck`-style saturation].
    pub stalmarck_edges: Vec<StalmarckEdge>,
    /// rc.28 (S.1-AOT) — set when *any* prelude assertion was
    /// un-encodable by `flatten_to_clauses` at bake time (a
    /// nested OR-of-AND etc.) and therefore dropped from the
    /// baked clause set.  Mirrors the baseline `check_ground`
    /// `had_opaque` flag: on load it forces a `Sat` verdict to
    /// downgrade to `Unknown` (we cannot claim satisfiability
    /// while ignoring an assertion we could not bake), while an
    /// `Unsat` from the baked flattenable subset stays sound.
    /// Trailing v1.2 field — v1.0/v1.1 readers stop before it
    /// and default it to `false`.
    pub had_opaque: bool,
    /// rc.34.4 — the prelude's precomputed order-independent
    /// clause-fold `(sum, count)`: a 256-bit AdHash accumulator
    /// over the per-clause KangarooTwelve-256 hashes plus the
    /// clause count.  The §3.5.J `--jit-trace-load` consult folds
    /// this **once** (prelude is fixed across a session) and
    /// `combine`s it with only the per-query delta each
    /// `(check-sat)`, so the exact-match digest is `O(#query
    /// clauses)` rather than re-canonicalising the whole
    /// prelude∪query formula.  Trailing v1.3 field — v1.0–v1.2
    /// readers stop before it (`None`); a `None`-loading engine
    /// recomputes the fold once at load instead.
    pub prelude_clause_fold: Option<([u8; 32], u64)>,
}

impl CdclSection {
    /// Empty section — zero clauses / trail / watches / VSIDS /
    /// saved-phase / Stålmarck entries — for the degenerate
    /// AOT bake where the prelude is empty or the bake side
    /// decided to skip the CDCL extension.  Useful as a fresh
    /// start for the bake path's incremental population.
    pub fn empty(binary_sha256: [u8; 32], flatten_version: u32) -> Self {
        Self {
            binary_sha256,
            flatten_version,
            clauses: Vec::new(),
            trail: Vec::new(),
            watches: Vec::new(),
            vsids: Vec::new(),
            saved_phase: Vec::new(),
            stalmarck_edges: Vec::new(),
            had_opaque: false,
            prelude_clause_fold: None,
        }
    }
}

/// Write a CDCL section to `out`.  Caller is responsible for
/// having written the v0 sections (header + pool + assertion
/// list) immediately before; the byte cursor must already sit
/// at the v0/v1 boundary.
pub fn write_cdcl_section<W: Write>(
    out: &mut W,
    section: &CdclSection,
) -> Result<(), crate::writer::WriteError> {
    out.write_all(&section.binary_sha256)?;
    out.write_all(&section.flatten_version.to_le_bytes())?;
    out.write_all(&(section.clauses.len() as u64).to_le_bytes())?;
    for clause in &section.clauses {
        let len: u32 = clause
            .lits
            .len()
            .try_into()
            .expect("clause with more than 2^32 literals is implausible");
        out.write_all(&len.to_le_bytes())?;
        for (atom, polarity) in &clause.lits {
            out.write_all(&atom.to_le_bytes())?;
            out.write_all(&[if *polarity { 1u8 } else { 0u8 }])?;
        }
    }
    out.write_all(&(section.trail.len() as u64).to_le_bytes())?;
    for entry in &section.trail {
        out.write_all(&entry.atom_pool_idx.to_le_bytes())?;
        out.write_all(&[if entry.polarity { 1u8 } else { 0u8 }])?;
        out.write_all(&entry.reason_clause_idx.to_le_bytes())?;
    }
    out.write_all(&(section.watches.len() as u64).to_le_bytes())?;
    for entry in &section.watches {
        out.write_all(&entry.atom_pool_idx.to_le_bytes())?;
        out.write_all(&[if entry.polarity { 1u8 } else { 0u8 }])?;
        let wlen: u32 = entry
            .watching_clauses
            .len()
            .try_into()
            .expect("watching_clauses count > 2^32 is implausible");
        out.write_all(&wlen.to_le_bytes())?;
        for c in &entry.watching_clauses {
            out.write_all(&c.to_le_bytes())?;
        }
    }
    out.write_all(&(section.vsids.len() as u64).to_le_bytes())?;
    for entry in &section.vsids {
        out.write_all(&entry.atom_pool_idx.to_le_bytes())?;
        out.write_all(&entry.activity.to_le_bytes())?;
    }
    out.write_all(&(section.saved_phase.len() as u64).to_le_bytes())?;
    for entry in &section.saved_phase {
        out.write_all(&entry.atom_pool_idx.to_le_bytes())?;
        out.write_all(&[if entry.polarity { 1u8 } else { 0u8 }])?;
    }
    // §3.3 / §3.5.A v1.1 trailing Stålmarck section.  v1.0
    // readers stop at the saved-phase section and silently
    // ignore the trailing bytes; v1.1 readers pick them up
    // when the buffer has not reached its end.
    out.write_all(&(section.stalmarck_edges.len() as u64).to_le_bytes())?;
    for edge in &section.stalmarck_edges {
        out.write_all(&edge.from_atom_pool_idx.to_le_bytes())?;
        out.write_all(&[if edge.from_polarity { 1u8 } else { 0u8 }])?;
        out.write_all(&edge.to_atom_pool_idx.to_le_bytes())?;
        out.write_all(&[if edge.to_polarity { 1u8 } else { 0u8 }])?;
    }
    // rc.28 (S.1-AOT) v1.2 trailing soundness flag.  v1.0/v1.1
    // readers stop after the Stålmarck section and default this
    // to `false`; v1.2 readers pick it up when the cursor has
    // not reached the buffer's end.
    out.write_all(&[if section.had_opaque { 1u8 } else { 0u8 }])?;
    // rc.34.4 v1.3 trailing precomputed prelude clause-fold.
    // v1.0–v1.2 readers stop after the `had_opaque` byte and
    // default this to `None`; v1.3 readers pick it up when the
    // cursor has not reached the buffer's end.  Written only when
    // present, so absence is byte-for-byte the v1.2 layout.
    if let Some((sum, count)) = &section.prelude_clause_fold {
        out.write_all(&[1u8])?; // presence
        out.write_all(sum)?; // 32-byte AdHash sum
        out.write_all(&count.to_le_bytes())?; // u64 clause count
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sha32() -> [u8; 32] {
        let mut s = [0u8; 32];
        for (i, b) in s.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(7);
        }
        s
    }

    #[test]
    fn empty_section_writes_only_header_and_zero_counts() {
        let s = CdclSection::empty(sha32(), 0xdead_beef);
        let mut buf: Vec<u8> = Vec::new();
        write_cdcl_section(&mut buf, &s).unwrap();
        // 32 (sha) + 4 (flatten) + 5 * 8 (each v1.0 Vec
        // len = 0u64) + 8 (v1.1 Stålmarck Vec len = 0u64)
        // + 1 (rc.28 v1.2 `had_opaque` flag byte).
        assert_eq!(buf.len(), 32 + 4 + 6 * 8 + 1);
        // The trailing v1.2 byte is the `had_opaque` flag, 0 here.
        assert_eq!(buf[32 + 4 + 6 * 8], 0u8);
        assert_eq!(&buf[..32], &sha32());
        assert_eq!(
            u32::from_le_bytes(buf[32..36].try_into().unwrap()),
            0xdead_beef,
        );
        // All six `_len` slots are 0.
        for i in 0..6 {
            let off = 36 + 8 * i;
            assert_eq!(
                u64::from_le_bytes(buf[off..off + 8].try_into().unwrap()),
                0,
            );
        }
    }

    #[test]
    fn stalmarck_section_round_trips_through_bytes() {
        let mut s = CdclSection::empty(sha32(), 0);
        s.stalmarck_edges.push(StalmarckEdge {
            from_atom_pool_idx: 3,
            from_polarity: false,
            to_atom_pool_idx: 7,
            to_polarity: true,
        });
        let mut buf: Vec<u8> = Vec::new();
        write_cdcl_section(&mut buf, &s).unwrap();
        // Locate the Stålmarck section: after sha+flatten +
        // 5 zero counts (v1.0) + 1 stalmarck_count slot.
        let stalmarck_off = 32 + 4 + 5 * 8;
        assert_eq!(
            u64::from_le_bytes(
                buf[stalmarck_off..stalmarck_off + 8].try_into().unwrap()
            ),
            1,
        );
        let entry_off = stalmarck_off + 8;
        assert_eq!(
            u32::from_le_bytes(
                buf[entry_off..entry_off + 4].try_into().unwrap()
            ),
            3,
        );
        assert_eq!(buf[entry_off + 4], 0);
        assert_eq!(
            u32::from_le_bytes(
                buf[entry_off + 5..entry_off + 9].try_into().unwrap()
            ),
            7,
        );
        assert_eq!(buf[entry_off + 9], 1);
    }

    #[test]
    fn clause_with_two_lits_round_trips_through_bytes() {
        let mut s = CdclSection::empty(sha32(), 0);
        s.clauses.push(CdclClause {
            lits: vec![(3, true), (7, false)],
        });
        let mut buf: Vec<u8> = Vec::new();
        write_cdcl_section(&mut buf, &s).unwrap();
        // Layout: 32 sha + 4 flatten + 8 clauses_len + clause
        // payload.  Clause payload = 4 (lit_count=2) + 2 * (4 + 1).
        // Then 4 zero count slots (8 bytes each).
        let off_after_clauses = 32 + 4 + 8 + 4 + 2 * 5;
        // trail_len = 0
        assert_eq!(
            u64::from_le_bytes(
                buf[off_after_clauses..off_after_clauses + 8]
                    .try_into()
                    .unwrap()
            ),
            0,
        );
    }

    #[test]
    fn trail_entry_with_no_antecedent_encodes_minus_one() {
        let mut s = CdclSection::empty(sha32(), 0);
        s.trail.push(TrailEntry {
            atom_pool_idx: 5,
            polarity: true,
            reason_clause_idx: -1,
        });
        let mut buf: Vec<u8> = Vec::new();
        write_cdcl_section(&mut buf, &s).unwrap();
        // Skip to trail section: 32 sha + 4 flatten + 8 clauses_len
        // (with 0 clauses).
        let trail_count_off = 32 + 4 + 8;
        assert_eq!(
            u64::from_le_bytes(
                buf[trail_count_off..trail_count_off + 8]
                    .try_into()
                    .unwrap()
            ),
            1,
        );
        let entry_off = trail_count_off + 8;
        // atom_pool_idx = 5
        assert_eq!(
            u32::from_le_bytes(buf[entry_off..entry_off + 4].try_into().unwrap()),
            5,
        );
        // polarity = true (1)
        assert_eq!(buf[entry_off + 4], 1);
        // reason_clause_idx = -1 (i64::MAX-like bit pattern via two's complement)
        assert_eq!(
            i64::from_le_bytes(
                buf[entry_off + 5..entry_off + 13].try_into().unwrap()
            ),
            -1,
        );
    }

    #[test]
    fn vsids_activity_round_trips_f64_bits() {
        let mut s = CdclSection::empty(sha32(), 0);
        s.vsids.push(VsidsEntry {
            atom_pool_idx: 9,
            activity: 0.125_f64,
        });
        let mut buf: Vec<u8> = Vec::new();
        write_cdcl_section(&mut buf, &s).unwrap();
        // Locate the vsids section: after sha+flatten+clauses+trail+watches
        // counts, all zero except vsids = 1.
        let vsids_count_off = 32 + 4 + 8 * 3;
        assert_eq!(
            u64::from_le_bytes(
                buf[vsids_count_off..vsids_count_off + 8]
                    .try_into()
                    .unwrap()
            ),
            1,
        );
        let entry_off = vsids_count_off + 8;
        assert_eq!(
            u32::from_le_bytes(buf[entry_off..entry_off + 4].try_into().unwrap()),
            9,
        );
        let act =
            f64::from_le_bytes(buf[entry_off + 4..entry_off + 12].try_into().unwrap());
        assert_eq!(act, 0.125_f64);
    }
}
