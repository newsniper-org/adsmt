---
name: adsmt release channel model
description: Debian-style channel model. Development tiers are single branches (unstable=main, testing=testing, both rolling). The RELEASED tier is split by cadence (decided 2026-06-07): `stable` branch = rolling latest-stable across all majors; `stable-v<major>` branch (stable-v1, stable-v2…) = semi-rolling LTS within one major; `v<major>.<minor>.<patch>` tags = immutable point releases. adsmt-contrib mirrors this in lockstep.
type: project
---

# adsmt release channel model

Debian-style channels. **Development tiers are single rolling
branches; the released tier is split by release cadence** so a
consumer can pin exactly the stability they want.

| Channel | Git ref | Cadence | Tracks |
|---|---|---|---|
| `unstable` (sid) | `main` branch | rolling | every new commit (current dev) |
| `testing` | `testing` branch | rolling | stabilisation candidates promoted from `main` |
| `stable` | `stable` branch | rolling | the latest stable release across **all** majors — advances through major bumps |
| `stable-v<major>` | `stable-v1`, `stable-v2`, … | semi-rolling | the latest stable **within one major** — `stable-v1` follows every `1.x` but never advances to `2.0` (the LTS line) |
| point release | `v<major>.<minor>.<patch>` tag | immutable | one frozen release; never moves |

**Why (2026-06-07 user decision):** the earlier model had a
single `stable` = `v1.0.0` tag.  That conflates three different
consumer intents.  The refinement splits the released tier:

- **`stable` branch** — "always newest stable, I'll take major
  bumps."  Rolling; moves forward across `1.x → 2.0 → …`.
- **`stable-v<major>` branch** — "newest within my major, don't
  break me with a major bump."  Semi-rolling LTS; `stable-v1`
  tracks `1.x` only.
- **`v<major>.<minor>.<patch>` tag** — "exact reproducible
  build."  Immutable point release.

**How to apply:**

- The **first stable cut** (gated on the `feedback_stable_signoff_user_approval.md`
  sign-off + the (S.2)+audit gate in `verus_fork_integration.md`)
  places the `v1.0.0` tag and forks **both** the `stable` and
  `stable-v1` branches from that commit.
- Each subsequent release: tag `v<major>.<minor>.<patch>`, then
  fast-forward `stable` (always) and the matching
  `stable-v<major>` branch (if the release is within that major).
  A new major `2.0.0` advances `stable` and forks a fresh
  `stable-v2`; it does **not** touch `stable-v1`.
- The pre-stable testing channel (`testing` branch) and dev
  channel (`main`) are unchanged — still single rolling branches.
- **adsmt-contrib** (`~/adsmt-contrib`, see [[adsmt_contrib_repo]])
  mirrors this model in lockstep: its `stable` / `stable-v<major>`
  branches + tags are cut *after* adsmt main's, against the matching
  adsmt git ref.

Consumer pin examples:

```toml
# always newest stable (accepts major bumps)
adsmt-meta = { git = "…/adsmt", branch = "stable" }
# semi-rolling LTS within 1.x
adsmt-meta = { git = "…/adsmt", branch = "stable-v1" }
# exact frozen release
adsmt-meta = { git = "…/adsmt", tag = "v1.0.0" }
```
