<!-- SPDX-License-Identifier: Apache-2.0 -->

# `oxiz-cli` + theory fixes: stream stdin, multi-datatype parse, defensive simplex bounds — `0.2.4-feat/streaming-stdin`

> Draft PR for posting at <https://github.com/cool-japan/oxiz/pulls>.
> Branch: `Honey-Be/oxiz:0.2.4-feat/streaming-stdin` (based on
> upstream `cool-japan/oxiz:0.2.4`).

---

**Title (suggested):**
`oxiz-cli: stream stdin (no buffer-to-EOF) + parser/simplex robustness fixes (adsmt downstream)`

**Labels (suggested):** `enhancement`, `oxiz-cli`, `parser`, `theory`

---

## Plan change (2026-06-09) — why this is now a *0.2.4* branch, and the simplex soundness fix is dropped

This MR was previously planned as `0.2.3-feat/streaming-stdin` and was
to *include* a simplex pop/tableau soundness fix (adsmt-side commit
`102e377`): `Simplex::pop` did not restore the tableau/basis pivoted by
`check()`'s `make_feasible` at a higher decision level, so the
backtracking cycle `decide → conflict → pop → decide` lost lower-level
bounds and `(or (< x 0) (> x 0)) ∧ (= x 0)` returned a spurious `sat`.

While re-basing onto upstream `0.2.4` we found **`0.2.4` had already
fixed that exact bug, with the identical approach** — snapshot the
tableau + `basic` on `push`, restore on `pop` (upstream's
`saved_tableaux` is the same construction as our `cached_tableaus` /
`cached_basic`). Independent convergence on the same fix. So:

- The branch is rebuilt as **`0.2.4-feat/streaming-stdin`** (upstream
  `0.2.4` + the streaming-stdin work, merged up to `5286e29`).
- The `102e377` pop/tableau fix is **omitted** — it is redundant on
  `0.2.4`. Verified on this branch: the four repro cases
  (`(or (< x 0) (> x 0)) ∧ (= x 0)`, the `(>= …) (<= …)` bound form,
  `(or (< x 1) (> x 1)) ∧ (= x 1)`, the two-variable form) all resolve
  to the correct `unsat`/`sat`; oxiz-theories + oxiz-solver = 2098
  tests green.
- adsmt's `external/oxiz` submodule now tracks this branch.

## What this MR carries (over upstream `0.2.4`)

- **`oxiz-cli`: stream stdin instead of buffering to EOF** (`e3103b1`) —
  the headline change; lets a long-running SMT-LIB session be fed
  command-by-command without buffering the whole script.
- **parser: `declare-datatypes` multi-datatype form** (`b0de8e2`) —
  parse all groups of the multi-datatype declaration (previously only
  the first group was parsed → `expected ')', found LParen` on
  field-bearing record datatypes).
- **simplex: defensive bounds on `can_increase`/`can_decrease`**
  (`56b1bf8`) — a *separate* robustness fix from the pop/tableau one
  above; guards an out-of-bounds access in the bound-vector lookup.
- **`enable_writer`** (`1297944`, `f279812`, `45f3057`) — already
  merged upstream as PR #9 / the `DratWriter`/`LratWriter` rename; carried
  here only as the branch ancestry, not re-proposed.
- minor: `oxiarc` dep bump, wasm target hygiene.

## Provenance

These changes were driven by **adsmt** (a Pure-Rust abductive +
Lean4/Rocq SMT layer that adopts `oxiz-sat`/`oxiz-solver` as its solving
backend; see the introduction issue draft). Each is a strict
robustness/feature addition with no behavioural change to existing
upstream APIs.
