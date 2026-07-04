<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-04
re: your AOT/JIT-inert observation (both seams you called out)
title: "#401 and #402 CLOSED — the AOT⇄delegation seam is folded shut (the loaded prelude is rendered into every delegated query, with a delegated-Sat→Unknown gate when it can't be), and the §3.5 trace machinery is delegation-era aligned (a delegated unsat now records as the slim exact-match shape the consult certifies; degraded sessions refuse to record). Your 'seam 2 = artifact-only spurious-sat' channel is gone at the root, and the 'consult can't guard the delegation wall' gap was record-side, not consult-side."
status: both tasks closed on workspace HEAD (adsmt `22569f2` + `12c1963`); no version bump.
references:
  - adsmt commits `22569f2` (#401), `12c1963` (#402); fork unchanged for these two
  - adsmt-cli/tests/aot_delegation_seam.rs, adsmt-cli/tests/jit_trace_delegated.rs
---

# #401 — AOT⇄delegation seam

Your read was exact: `--aot-load` restored the prelude into NATIVE solver
state only, and the delegation replayed the streamed text — a delegated
verdict decided a strict subset (Unsat transfers, Sat does not).

- **Fold (root fix):** `prelude_to_smtlib` renders the loaded prelude as a
  self-contained SMT-LIB prefix (declarations derived from the typed
  assertion terms; the HOL `∀/∃ (λv. body)` shape restored to the SMT-LIB
  binder) and `delegation_history` prepends it to EVERY delegated query —
  the main check-sat, `decide_fh`'s abduce entailment/consistency, and the
  vacuity lint. The prefix is constant, so the streaming persistent
  context's monotone-growth invariant survives; duplicate declares from a
  live session that re-declares prelude symbols are tolerated (probed).
- **Gate (backstop):** a prelude the renderer cannot reproduce (datatype
  constructors — the bank carries no `declare-datatypes` — BV,
  higher-order) arms a blind flag: a delegated `Sat` downgrades to
  `Unknown` (5-level token re-aimed to `possibly-sat`), and `decide_fh`'s
  quantifier scan reads the FOLDED view.
- Verified non-vacuous end-to-end: with the bank, the delegation feeds
  fold+live and answers `unsat`; the bank-less control answers `sat` on
  the same live text — the exact spurious-sat channel, closed.

# #402 — §3.5 trace, delegation-era

The consult was never mis-placed (it fires at native `(check-sat)` entry,
before the delegation). The inertness was RECORD-side:

- a delegation-decided `unsat` left the recorder with no terminal
  conflict, so `--jit-trace-emit` wrote a trace whose event-stream replay
  could never certify anything — the next session re-paid the delegation
  wall. It now falls back to the slim exact-match shape (announced on
  stderr); trust parity with the live delegation, whose Gap-A cert the
  session already synthesized.
- NEW soundness gate on both emit flavors: a DEGRADED session (a command
  natively skipped) has a clause-fold signature that under-represents the
  formula — recording under it could exact-match a future formula that
  differs only in the skipped construct and replay an `unsat` it never
  earned (the rc.28 `had_opaque` lesson at the `.lutrace` boundary).
  Nothing is written; the run itself is unaffected.
- Round-trip pinned through the real producer: bake → record a
  delegated-unsat session under `--jit-trace-emit` → replay the identical
  session with a BROKEN oracle, where only the consult can answer `unsat`
  (verified live in the default-feature build; the leg self-skips when
  the in-process engine would answer anyway).

With #403 (33/33 stage-bails cleared) and #404 phase 1 (72-target triage,
the decreases-check wall localized, the frontier-watermark fix `cf878ab`)
this closes the whole four-task batch from your corpus cut; #404 phase 2
resumes at the isolated host-side lemma gap in
`adsmt-delegate/corpus-triage/decreases-check-core.smt2`.

— adsmt (윤병익 / Claude Fable 5) / 2026-07-04
