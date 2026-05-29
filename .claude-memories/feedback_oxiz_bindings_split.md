---
name: Split oxiz bindings by surface
description: All language bindings for the oxiz ecosystem must be split into "oxiz proper" vs "our contribution crates" sub-bindings
type: feedback
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
Every language binding for the oxiz ecosystem (Lean4, Rocq,
Python, etc.) must be implemented as **two or more sibling
crates** inside `contributions/oxiz/bindings/`:

1. A crate binding **oxiz proper** (`oxiz-sat`, `oxiz-proof`,
   `oxiz-math`, …). Example names: `oxiz-binding-lean4`,
   `oxiz-binding-rocq`.
2. One crate per **contribution surface** we own (`oxiz-contrib-
   abduction`, future contrib crates). Example names:
   `oxiz-binding-lean4-contrib-abduction`,
   `oxiz-binding-rocq-contrib-abduction`.

**Note (2026-05-28 — supersedes the 2026-05-27 framing):**
ITP integration architecture narrowed:

- **OxiLean + Lean4** are kept as sibling projects of adsmt
  (co-equal first-class).
- **Rocq and other ITPs (Isabelle, HOL-Light, Agda, …)** become
  **out-of-tree** projects, not sibling crates.
- The user is developing **`leo4`** (local repo `~/leo4/`) — a
  single Rust binding library targeting OxiLean and Lean4
  simultaneously. All adsmt-side binding work pauses until
  `leo4` v1.0.
- The split-pattern convention here still applies whenever a
  binding crate is created (core ↔ contrib-*), but the *which
  ITPs* sub-question is now answered by the sibling-vs-out-of-
  tree decision above.

**Why:** Confirmed on 2026-05-16 by the user as an architectural
directive. The split keeps the layering clean:
- promotion of any contribution crate to a first-party oxiz crate
  doesn't drag its language bindings with it
- bindings for oxiz proper can be released independently of our
  contributions' API stability
- consumers can pick exactly the binding surface they need

**How to apply:**
- When adding a new language binding (Lean4 + Rocq are the
  current targets; Python / WASM / Lua etc. follow later),
  always create at least the `core` crate per language; add
  `contrib-<name>` crates for each contribution surface that
  needs language binding coverage.
- Names: prefix everything in the `bindings/` repo with
  `oxiz-binding-<lang>` followed by either nothing (= core) or
  `-contrib-<surface>`. Avoid abbreviating "contrib" to keep the
  scope visible in `cargo` output.
- The workspace `Cargo.toml` in `contributions/oxiz/bindings`
  enumerates all binding crates as members; each is independently
  publishable on crates.io.
- Cross-crate dependencies: the contrib-binding depends on the
  core binding only when it needs to (e.g. shared FFI helpers).
  Default to keeping them independent.
