# contributions/ + ~/adsmt-contrib/ audit

**Status**: v1.0.0-rc.2 RC2.7 — **all 13 findings resolved**
2026-05-31 per user instruction to fix every severity tier
in parallel.

## Build/test status (baseline, unchanged)

| Location | Crates | Build | Tests |
|---|---|---|---|
| `contributions/oxiz/abduction/` | `oxiz-contrib-abduction` | ✅ | 14 pass |
| `contributions/oxiz/bindings/` | `oxiz-binding-lean4` + contrib-abduction sibling | ✅ | 9 pass |
| `~/adsmt-contrib/` | `adsmt-emit-rocq`, `adsmt-emit-isabelle` | ✅ | 26 pass (11+15) — pending re-test post adsmt-main v1.0.0 push + tag (user instruction) |

## Findings — every item now addressed

### `~/adsmt-contrib/` (out-of-tree)

| # | Item | Severity | Status | Fix |
|---|---|---|---|---|
| 1 | README cites only v0.19 | medium | ✅ resolved | README rewritten — v0.21 K-full + v0.23 phase 1 freeze + v1.0 transition all referenced; adsmt-contrib commit `0b07370` |
| 2 | Stale "compound rules emit sorry/Admitted." claim | medium | ✅ resolved | Status table updated to reflect real proof-term emit on every backend; same commit |
| 3 | No v0.23 phase 1 freeze acknowledgement | medium | ✅ resolved | New §"v0.23 phase 1 freeze implications" added |
| 4 | No 21E.1 option 5 transition note | medium | ✅ resolved | New §"21E.1 outcome — bidirectional embed" added |
| 5 | adsmt-contrib workspace `version = "0.1.0"` | low | ✅ resolved | Bumped to `1.0.0` per user instruction (track adsmt main directly) |
| 6 | `rust-version = "1.75"` mismatch | medium | ✅ resolved | Raised to `1.88` (matches adsmt main floor) |
| 7 | `edition = "2021"` vs adsmt main `2024` | low | ✅ resolved | Bumped to `2024` |
| 8 | Published-form git rev pin `91e614a` | high | ✅ resolved | Replaced with `tag = "v1.0.0"`; per user instruction, test against this happens *after* adsmt main pushes its v1.0.0 commit + sets the tag (both manual) |

### `contributions/oxiz/abduction/` (newsniper-org repo via submodule)

| # | Item | Severity | Status | Fix |
|---|---|---|---|---|
| 9 | "API may evolve before 1.0 promotion" non-commitment | low | ✅ resolved | Rewritten to explicit "no breaking-change queued for 0.1.x; 1.0 promotion coordinated with OxiZ-side first-party promotion decision"; commit `0500518` |
| 10 | No adsmt-cycle verification anchor | low | ✅ resolved | Added "Trait surface verified against adsmt v1.0.0-rc.2 (2026-05-31)" line |

### `contributions/oxiz/bindings/` (newsniper-org repo via submodule)

| # | Item | Severity | Status | Fix |
|---|---|---|---|---|
| 11 | No frozen-until-leo4-v1.0 notice in README | high | ✅ resolved | Top-of-page warning box + new §"Freeze status" section recording freeze date, rationale, scope, thaw condition, bug-fix exception; commit `8818277` |
| 12 | No freeze date or thaw condition | high | ✅ resolved | Same commit — §Freeze status records both |
| 13 | bindings README split-explanation | OK | n/a | (was already correct; logged for completeness) |

## Cargo.toml `[package.description]` markers

Per the freeze-policy surfacing principle, the two binding
crates also carry an inline `[FROZEN until leo4 v1.0 — see
repo README §Freeze status]` suffix in their `description`
field so the marker appears on `cargo search` / crates.io
listing without requiring a click-through.

## Version-line invariant (user instruction 2026-05-31)

- `~/adsmt-contrib/` workspace version tracks adsmt main:
  currently `1.0.0`. Future cycles bump in lockstep.
- `contributions/oxiz/*` submodule versions stay
  **independent** of adsmt main. Currently `0.1.0` (oxiz-side
  community contributions follow OxiZ's own version line
  decisions). Not touched by this commit.

## Re-verification

```bash
# Build + test sanity (run post-v1.0.0-tag-set for ~/adsmt-contrib):
for d in contributions/oxiz/abduction contributions/oxiz/bindings; do
  (cd "$d" && cargo test --quiet)
done
# Post-tag re-test:
# (cd ~/adsmt-contrib && cargo test --quiet)

# Doc surface check:
grep -q "v0.21 K-full" ~/adsmt-contrib/README.md
grep -q "v0.23 phase 1 freeze" ~/adsmt-contrib/README.md
grep -q "21E.1" ~/adsmt-contrib/README.md
grep -q "FROZEN" contributions/oxiz/bindings/README.md
grep -q "Freeze status" contributions/oxiz/bindings/README.md
grep -q "verified against adsmt" contributions/oxiz/abduction/README.md
```

## ~/adsmt-contrib/ deep audit — 2026-06-01 (post-D1)

Follow-up to the RC2.7 pass, now that the channel model has
been introduced (commits `4fbde87` on main / `8c5c1f0` on
testing) and the v1.0.0 scope has expanded (option A, memory
`v1_0_0_scope_expansion.md`).

### Status (post-fix)

| Check | main | testing |
|---|---|---|
| `cargo check --workspace` | ✓ | ✓ |
| `cargo test --workspace` | 26 / 26 pass | (same fixture) |
| `cargo clippy --workspace -- -D warnings` | ✓ (post-fix) | (cherry-pick pending) |
| `cargo doc --workspace --no-deps` | 0 warnings (post-fix) | (cherry-pick pending) |
| `cargo publish -p <crate> --dry-run` | ❌ (see F3) | ❌ (same) |
| Channel-pin discipline | ✓ `branch="main"` | ✓ `branch="testing"` |

### Findings

**F1 — Clippy `if_same_then_else` in
`adsmt-emit-rocq/src/lib.rs:140-144`.** Both `if` arms
pushed `'\n'`. Severity: medium. Fix: unconditional
`out.push('\n')` after the import loop — the intent was
always to terminate the imports block with a blank line
regardless of contents. Lands on `main` only; testing
gets the fix via cherry-pick when ready.

**F2 — Rustdoc `redundant_explicit_links` in
`adsmt-emit-{rocq,isabelle}/src/lib.rs:4`.** The
`[`Certificate`](adsmt_cert::Certificate)` form was redundant
because the label alone resolves through the workspace dep.
Fix: drop the explicit target. Both crates updated.

**F3 — `cargo publish --dry-run` fails identically to adsmt
main `PUBLISH_AUDIT.md` issue 1.** `adsmt-cert` /
`adsmt-core` are declared as `git = "..."` with no
`version` field, so cargo refuses to verify the manifest
for publication. **Not a blocker until adsmt main publishes
v1.0.0 to crates.io**; the fix at that point is shaped as:

```toml
adsmt-cert = { git = "...", branch = "main", version = "=1.0.0" }
```

This needs to land on BOTH branches with the appropriate
channel-pin discipline preserved (`branch="main"` on main,
`branch="testing"` on testing).

### Resolution

F1 + F2 fixed at adsmt-contrib `main` HEAD by a single
combined commit. Testing branch receives the cherry-pick
when we're ready to promote. F3 stays deferred until adsmt
main's v1.0.0 crates.io push.

### Re-verification (post-fix)

```bash
cd ~/adsmt-contrib
cargo check --workspace
cargo clippy --workspace -- -D warnings    # expect: clean
cargo doc --workspace --no-deps 2>&1 | grep -c "^warning"  # expect: 0
cargo test --workspace                     # expect: 26 / 26
```
