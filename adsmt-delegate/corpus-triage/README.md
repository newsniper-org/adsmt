<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# corpus-triage — the #404 tuning-campaign toolkit

Standing tools for the verus-fork per-obligation corpus campaign
(`corpus-2026-07-04-lukb-per-obligation/`, pinned `manifest.tsv`): classify
every `solver-unknown` row against z3, then shrink a chosen render to the
axioms the disagreement actually needs.

- `triage_unknowns.py` — for every pinned `solver-unknown`/`solver-timeout`/
  `stage-bail` row, re-run `adsmtc` (`ADSMT_DELEGATE_DEBUG=1`), capture the
  delegated render, and run z3 on it. `z3=unsat` rows are the REAL
  completeness targets (z3 closes what we abstain on); `z3-noverdict` rows
  are mostly the designed-non-verifying abduct family. Env: `ADSMT_CORPUS`,
  `ADSMTC`. Output: per-row TSV + a `family × (adsmtc, z3)` summary.
- `ddmin_render.py <render.smt2> <out.smt2>` — per-`(assert)` ddmin
  preserving `z3 = unsat ∧ oxiz ≠ unsat` (declarations kept verbatim).
  Env: `OXIZ` (the fork CLI, `cargo build --release -p oxiz-cli` inside
  `external/oxiz`). This is the #396/#397 localization playbook, mechanized.
- `dm3-ob01-ddmin-core.smt2` — the campaign's first localized wall:
  `datatypes-match-3/ob01` shrunk 419 → 5 asserts (the verus
  decreases-check shape: the `check_decrease_height` definition + guarded
  per-field height axioms). z3: `unsat`; the fork engine at `8039884`:
  `unknown`.
- `decreases-check-core.smt2` — the same wall hand-reduced to 14 lines over
  uninterpreted sorts (no datatypes — the shape, not the theory, is the
  discriminator). The probe chain on it isolated TWO independent engine
  gaps: (1) the frontier-watermark starvation (FIXED, fork `cf878ab` — a
  round whose e-match step was skipped still aged the frontier, so a
  freshly-inferred trigger never saw the pre-existing ground seeds;
  `OXIZ_MBQI_DBG=1` showed `ematch_all -> 0` flipping to 8); (2) the
  emitted instance's guarded lemma not biting in the host's next ground
  re-solve (OPEN — the instance `x ↦ unbox e` is emitted in round 1 via
  CDQI, the host asserts `[¬Q, φ]`, and the re-solve still reports SAT;
  an explicit `:pattern` on the same axiom closes the query through the
  solver-side e-matching path, so the gap is host-side).

Verdict-trust rule: any change motivated by these tools that can produce a
NEW `unsat` goes through the fork suites + a full-corpus re-sweep against
the pinned manifest (0 regressions, negative controls exact) before it
lands — see `feedback_z3_differential_for_unsat_trust`.
