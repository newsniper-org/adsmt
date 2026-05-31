# contributions/ + ~/adsmt-contrib/ audit

**Status**: v1.0.0-rc.2 RC2.7 — re-done 2026-05-31 per user
clarification: audit must surface **missing/stale items**, not
just confirm builds + tests pass.

## Build/test status (baseline)

| Location | Crates | Build | Tests |
|---|---|---|---|
| `contributions/oxiz/abduction/` | `oxiz-contrib-abduction` | ✅ | 14 pass |
| `contributions/oxiz/bindings/` | `oxiz-binding-lean4` + contrib-abduction sibling | ✅ | 9 pass |
| `~/adsmt-contrib/` | `adsmt-emit-rocq`, `adsmt-emit-isabelle` | ✅ | 26 pass (11+15) |

## Findings — missing / stale items

### `~/adsmt-contrib/` (out-of-tree)

| # | Item | Severity | Detail |
|---|---|---|---|
| 1 | README status table cites only v0.19 | medium | "v0.19: Trans + EqMp emit real proof terms (Rocq side K landed); two-pass scan=true wiring (A.5)" — v0.21 cycle's K-full (Deduct/Abs/Beta/Inst/InstType emit real proof terms across all three backends, per memory `project_layout.md` "K-full compound-rule proof terms (Lean+Rocq+Isabelle)") is not reflected. The README still talks about `sorry` / `Admitted.` stubs for compound rules. |
| 2 | README "Compound kernel rules currently emit … sorry / Admitted. stub" | medium | Code-level audit (`StepBody::{Deduct, Abs, Beta, Inst, InstType}` arms in both backends) shows real proof terms emitted since v0.19 cycle close per memory; the README claim is stale by ~2 cycles. |
| 3 | No v0.23 phase 1 freeze acknowledgement | medium | The contrib backends consume `adsmt-cert` which is now under the v0.23 phase 1 freeze (`CERT_POLICY.md`). README doesn't mention the lockstep implication on contrib emit shapes. |
| 4 | No v1.0 transition note | medium | 21E.1 option 5 (bidirectional embed) was decided 2026-05-30; the contrib repo's "v1.0 of adsmt will revisit the boundary" line in §Versioning is outdated — the boundary was already revisited and codified. README should reflect option 5: contrib stays out-of-tree, lockstep rule continues, Apache-2 contribution path opens via OxiZ-side upstreaming. |
| 5 | `Cargo.toml [workspace.package] version = "0.1.0"` | low | v1.0.0 of adsmt cuts soon; contrib's 0.1.0 carries no compatibility marker. Independent semver is fine, but a 0.x → 1.x bump aligned with adsmt v1.0 would be a clearer compatibility signal. |
| 6 | `rust-version = "1.75"` mismatch | medium | adsmt main requires Rust 1.88+ for stable `proc_macro::Span::file` (per `adsmt-heuristic-checker-macros::doc`); `~/adsmt-contrib`'s 1.75 floor is too low — builds happen to work today because the contrib backends don't pull in the proc-macro crate, but the floor is misleading and would fail if any deeper dep needed 1.88. |
| 7 | `edition = "2021"` vs adsmt main `edition = "2024"` | low | Inconsistent edition choices; functional builds today, but a stylistic mismatch. |
| 8 | Published-form git rev pin `91e614a` | high | The commented-out git-rev fallback (`adsmt-cert = { git = "...", rev = "91e614a" }`) points at the v0.15 / v0.17 cycle boundary — ~7 cycles stale. If a published build is ever cut, this pin must be refreshed to a current adsmt commit (e.g. the v1.0.0 cut SHA once it lands). |

### `contributions/oxiz/abduction/`

| # | Item | Severity | Detail |
|---|---|---|---|
| 9 | README "API may evolve before a 1.0 promotion" | low | v1.0.0-rc.2 ships with this trait crate at 0.1.x; either commit to a 1.0 promotion path or document the current semver intent. As-is the sentence is informational only. |
| 10 | No version pin against adsmt | low | The crate is Apache-2 / solver-agnostic; doesn't depend on adsmt directly. But the README mentions "the use cases adsmt drives" — a one-line note about which adsmt cycle this trait shape was last verified against would help auditors. |

### `contributions/oxiz/bindings/`

| # | Item | Severity | Detail |
|---|---|---|---|
| 11 | **No frozen-until-`leo4`-v1.0 notice in README** | **high** | Memory `oxiz_relationship.md` § "Deferred: ALL language bindings until `leo4` v1.0" mandates that this exact crate set is frozen. The repository README + each member's Cargo.toml description carry no indication. External contributors discovering the repo would not know the freeze is in effect. |
| 12 | No freeze date or thaw condition | high | Same as #11 — the policy itself, even if added, should record when the freeze started (post-v0.18) and the explicit thaw condition (`leo4` v1.0 release). |
| 13 | core/contrib-* split per `feedback_oxiz_bindings_split.md` documented in README | OK | The split is correctly explained in the README; no missing item here. |

## Severity legend

- **high** — blocks v1.0.0 stable (mismatch with adsmt-side
  binding contract, or directly contradicts an existing
  memory policy)
- **medium** — non-blocking for the cut itself but creates
  user confusion or maintenance debt
- **low** — cosmetic / nice-to-have

## Decision for v1.0.0 stable cut

- **Item 11 (high)** must land *before or during* the v1.0.0
  cut window: add the freeze notice to
  `contributions/oxiz/bindings/README.md` (and ideally each
  member's `[package.description]`).
- **Item 8 (high)** must land before the v1.0.0 cut commit
  itself goes to the published form: refresh the git rev
  pin to the v1.0.0 SHA after the cut.
- **Items 1, 2, 3, 4 (medium)** should land alongside the
  v1.0.0 cut to keep the out-of-tree contrib repo aligned
  with the in-tree freeze; tracked as immediate v1.0
  follow-up.
- **Items 6, 7 (medium)**: bump `rust-version` + `edition`
  to match adsmt main. Mechanical edit.
- **Items 5, 9, 10 (low)** can land in v1.0.1+.

## Re-verification

```bash
set -e
for d in contributions/oxiz/abduction contributions/oxiz/bindings; do
  (cd "$d" && cargo test --quiet)
done
(cd ~/adsmt-contrib && cargo test --quiet)

# Doc check after fixes land:
grep -q "frozen.*leo4" ~/oxiz-contrib-bindings/README.md
grep -q "v0.21" ~/adsmt-contrib/README.md  # at minimum mention v0.21 K-full
grep -q "v1.0" ~/adsmt-contrib/README.md   # mention v1.0 transition
```
