<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# Repro — equality-goal `(abduce)` hangs on the prelude (regression since `605f175`)

Companion to `.local-requests-to/adsmt/2026-06-21-rc392-eqvars-abduce-hang-regression.md`.

## Files
- `eqvars-abduce-fullprelude.smt2` — the exact stream `lu-smt` receives (teed off
  the binary's stdin) during `verus -V adsmt -V request-abductive-on-unknown` on
  `source-fixture.rs`: full prelude `F` + one abductive block whose goal is
  `(abduce (= (Sub x! y!) 0))` and whose abducibles include `(= x! y!)`.
- `eqvars-main-session-only.smt2` — the SAME stream truncated to just before the
  abductive block + a terminal `(check-sat)`. This is the control: it finishes in
  **~1 s → `unknown`**, proving the hang is the abduce, not the verification.
- `source-fixture.rs` — `proof fn p(x: int, y: int) ensures x - y == 0 {}`.

## Reproduce (lu-smt built from ~/AD1, `--features adsmt-cli/oxiz`)

```
lu-smt eqvars-main-session-only.smt2   # ~1 s → unknown          (verification: fine)
lu-smt eqvars-abduce-fullprelude.smt2  # HANG > 300 s (100% CPU) (the abduce: regressed)
```

Same hang on a native-only build (no `oxiz`), so it is the **native** engine
churning, not OxiZ.

## Bisection

| lu-smt HEAD | result |
|---|---|
| `c9ed6e1` (rc.39.1 + abduce OxiZ-deferral) | finishes, surfaces `(= x! y!)` |
| `605f175` (rc.39.2, native Bool-eq fix)    | HANG |
| `7fe44d5` (rc.39.3, CCFV)                  | HANG |

Removing the equality *abducibles* from `eqvars-abduce-fullprelude.smt2` does
NOT stop the hang — it is the equality **goal** `(= (Sub x! y!) 0)` under the
abduce per-subset search, interacting with the `605f175` native Bool-eq→iff CNF
rewrite over the prelude's `Sub` `:pattern` axioms.
