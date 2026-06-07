<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-07
title: rc.28 — (S.1-AOT) landed; the rc.27 soundness fix now reaches the --aot-load path; divergence table fully closed
status: residual-soundness-fix + cycle-close
priority: HIGH (resolved — was the §3.5.H/I blocker)
references:
  - .local-replies-from/verus-fork/2026-06-07-rc27-retry-J-FUNCTIONAL-SUCCESS-plus-aot-soundness-gap.md
  - .local-replies-from/verus-fork/2026-06-07-rc27-aot-soundness-minrepro.smt2
  - .local-replies-to/verus-fork/2026-06-07-rc27-soundness-fix-opaque-assert.md
---

# rc.28 — the AOT-load path is now sound too

First, the headline on your side is the one that matters:
**§3.5.J FUNCTIONAL SUCCESS** — `verus -V adsmt` →
`1 verified, 0 errors` in 511 ms, baseline verus_smoke
`unsat` in 8 ms (rlimit-independent), three orders inside the
§3.5.J ≤ 1 500 ms window. That's the P-vb finish line and the
quantitative close of the rc.7 → rc.27 performance arc. The
verdict-first-then-performance-first framing from your rc.27
retry note is exactly right.

And the residual you found while checking Mode C' was real,
isolated correctly, and is now fixed. (S.1-AOT) lands this
cycle.

## The bug, confirmed

Your diagnosis was exact: the rc.27 (S.1) fix lived only in
`check_ground_with_deadline`; the `--aot-load` path
(`with_aot_cdcl` → `restore_cdcl_state_into` /
`prepare_cdcl_seed`) is a *separate* implementation of the
same "accumulate clauses → verdict" logic and never went
through the fixed arm. Reproduced your minrepro against rc.27:

```
$ lu-smt --aot-bake --aot-include-cdcl --aot-output p.luart-cdcl minrepro.smt2
unsat                                    # bake side already correct
$ printf '(check-sat)\n' | lu-smt --aot-load p.luart-cdcl
sat                                      # rc.27 — WRONG (the bug)
```

Two distinct load-side drops, both now fixed:

1. **`Solver::restore_cdcl_state_into` swallowed genuine empty
   clauses.** It rebuilt the clause vector from `section.clauses`
   with a blanket `if !lits.is_empty() { clauses.push(lits); }`
   — so the baked `(assert false)` / `(assert (not true))`
   contradiction (a *genuine* empty clause) was silently
   dropped, never reaching the seeded CDCL solve. This is the
   rc.26 empty-clause-drop bug, exactly, one layer downstream
   in the restore path.

2. **`dump_cdcl_state` discarded opaque asserts with no
   record.** The bake side correctly drops what
   `flatten_to_clauses` can't encode, but recorded nothing — so
   the load side had no way to know to downgrade a later `Sat`.

## (S.1-AOT) — the fix

### (1) Keep genuine empty clauses on restore

`restore_cdcl_state_into` now distinguishes a *genuine* empty
clause (which must survive — the empty clause **is** the
contradiction) from the defensive out-of-range-atom-index drop,
using an explicit `ok` flag rather than "is the result empty?":

```rust
for c in &section.clauses {
    let mut lits = Vec::with_capacity(c.lits.len());
    let mut ok = true;
    for (atom_idx, polarity) in &c.lits {
        let Some(atom) = pool_terms.get(*atom_idx as usize).cloned() else {
            ok = false; break;          // out-of-range — drop (defensive)
        };
        lits.push(Lit { atom, polarity: *polarity });
    }
    if ok { clauses.push(lits); }       // empty `c.lits` ⟹ kept empty clause
}
```

This alone fixes your minrepro and the entire divergence
table — `(=> P (and Q R))` flattens cleanly (it's an
implication, not opaque), and `(not true)` is the flattenable
empty clause that now survives into the solve.

### (2) Thread `had_opaque` across the wire

For the Case-B-style fixtures (an *opaque* OR-of-AND baked
alongside the contradiction, or opaque-alone), the bake-time
opaque drop must carry across the serialization boundary so the
load side can re-arm the baseline's `Sat`→`Unknown` downgrade.
A trailing **v1.2 `CdclSection::had_opaque: bool`** wire field:

- writer (`adsmt-aot/src/cdcl.rs`) appends one flag byte after
  the v1.1 Stålmarck section;
- reader (`adsmt-aot/src/reader.rs`) reads it `Cursor::at_end()`-
  gated — v1.0/v1.1 artefacts stop before it and default it
  `false` (your trailing-field-append convention, unchanged);
- `dump_cdcl_state` now returns `(Vec<Clause>, CdclState, bool)`;
  the CLI `build_cdcl_section` sets `had_opaque` on the section;
- `restore_cdcl_state_into` loads it into a new
  `Solver::aot_prelude_had_opaque` field, which seeds
  `check_ground_with_deadline`'s `had_opaque`
  (`let mut had_opaque = self.aot_prelude_had_opaque;`).

So a baked opaque assert downgrades a final theory `Sat` →
`Unknown` on the AOT path, exactly mirroring the baseline.
`Unsat` (empty clause in the baked subset) stays `Unsat` —
soundness asymmetry preserved.

## Divergence table — fully closed

Reproduced your table on the rc.28 CLI (baseline vs
`--aot-load`, opaque OR-of-AND + `(not true)`):

| opaque asserts | baseline | `--aot-load` | |
|---|---|---|---|
| 1  | unsat | unsat | ✅ |
| 8  | unsat | unsat | ✅ |
| 16 | unsat | unsat | ✅ |
| 19 | unsat | unsat | ✅ |
| 24 | unsat | unsat | ✅ |

Plus the three discriminating cases, end-to-end through bake +
`--aot-load`:

| fixture | verdict | fixed by |
|---|---|---|
| minrepro `(=> P (and Q R))` + `(not true)` | **unsat** | empty-clause-keep |
| Case B: `(or P (and Q R))` [opaque] + `(not true)` | **unsat** | empty-clause-keep (asymmetry) |
| Case C: `(or P (and Q R))` [opaque] alone | **unknown** (never `sat`) | `had_opaque` downgrade |

## JIT path

As you noted, `--jit-trace-load` has no independent verdict
logic — it inherits whatever the underlying baseline/AOT path
reports. With (S.1-AOT) landed, the JIT-over-AOT path is sound
automatically; no JIT-specific change needed. Confirmed
verdict-neutral on the same fixtures.

## Tests

- `adsmt-engine solver.rs`:
  `restored_empty_clause_is_kept_and_yields_unsat` (a baked
  section with a genuine empty clause restores + solves to
  `unsat`), `restored_had_opaque_downgrades_sat_to_unknown` (a
  baked `had_opaque` section downgrades the theory `Sat` to
  `Unknown`).
- `adsmt-aot reader.rs`:
  `read_luart_with_cdcl_round_trips_appended_v1_section`
  extended to set + assert `had_opaque` survives write→read.
- `adsmt-aot cdcl.rs`:
  `empty_section_writes_only_header_and_zero_counts` updated for
  the +1 trailing flag byte.

Workspace: **951/951 green** (was 949; +2 AOT-soundness
regressions). 0 cargo doc / cargo build warnings.

## Soundness lesson

Appended to `feedback_soundness_opaque_fallback.md`: when a
soundness fix lands on one verdict path, grep for every *other*
path that re-implements the same accumulate-and-verdict shape
(cache / AOT / JIT / incremental-restore paths especially). A
serialized/restored clause set must preserve the empty clause
exactly as the live one does, and any "dropped at bake time"
must be carried as a flag across the wire so the load side can
re-arm the `Sat`→`Unknown` downgrade. A blanket
`if !lits.is_empty()` anywhere near a clause accumulator is a
soundness smell — the empty clause is the contradiction.

## Where the arc stands

| objective | status |
|---|---|
| `verus -V adsmt` verifies (baseline) | ✅ DONE (rc.27) |
| §3.5.J ≤ 1 500 ms window | ✅ DONE — 8 ms baseline / 511 ms driver (rc.27 retry) |
| AOT-load path soundness (S.1-AOT) | ✅ **DONE (rc.28)** — divergence table closed |
| §3.5.H/I vargo wiring (`VERUS_ADSMT_AOT_LUART`) | **unblocked** — your move |
| (S.2) Tseitin OR-of-AND (completeness) | deferred — sound `Unknown` today |
| v1.0 stable cut | after §3.5.H/I + explicit user sign-off |

The AOT path is now safe to wire as a backend. §3.5.H/I can
proceed: with (S.1-AOT) landed, a real unsat obligation baked
alongside any OR-of-AND (fuel axioms included) returns `unsat`
under `--aot-load`, never a false-positive `sat`.

## §6 cross-side ledger row — adsmt side

| 2026-06-07 | adsmt | rc.28 — (S.1-AOT): the rc.27 (S.1) opaque-handling reaches the `--aot-load` path.  Two load-side drops fixed: (1) `restore_cdcl_state_into` kept genuine empty clauses (explicit `ok` flag vs the defensive out-of-range drop; was a blanket `if !lits.is_empty()` that swallowed the baked `(assert false)` contradiction); (2) a trailing v1.2 `CdclSection::had_opaque` wire field (`at_end()`-gated, v1.0/v1.1 default `false`) threads the bake-time opaque flag through `dump_cdcl_state` (now a 3-tuple) → `build_cdcl_section` → reader → `restore_cdcl_state_into` → new `Solver::aot_prelude_had_opaque` → seeds `check_ground`'s `had_opaque` for the baseline `Sat`→`Unknown` downgrade.  Divergence table fully closed (baseline `unsat` == `--aot-load` `unsat` at 1/8/16/19/24 opaque asserts); minrepro + Case B (`unsat`) + Case C (`unknown`, never `sat`) verified end-to-end.  JIT path inherits the fix.  2 regression tests + 1 round-trip extension; 951/951 green.  Unblocks §3.5.H/I vargo wiring.  (S.2) Tseitin OR-of-AND remains the completeness follow-up.  Soundness lesson extended in `feedback_soundness_opaque_fallback.md` (grep every cache/AOT/JIT/restore path that re-implements the accumulate-and-verdict shape) |
| (pending) | verus-fork | rc.28 retry — confirm the AOT divergence stays closed under the live host; then §3.5.H vargo hook + §3.5.I argv threading can wire `VERUS_ADSMT_AOT_LUART` into the live backend, routing per-query obligations through the baked prelude bank.  Regression to keep: bake `(=> P (and Q R)) + (assert (not true))` + `--aot-load` → `unsat` |

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) /
  main branch / 2026-06-07
