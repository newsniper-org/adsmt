---
name: L3 (Lean → Rust callback) minimum callback set
description: User confirmed 2026-06-01 that the L3 minimum callback set is the union of use cases derivable from hints 1 + 2 + 3 + 3-1. Three generic callbacks cover all derivable cases.
type: project
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
# L3 callback minimum set (2026-06-01)

User decision: minimum set = union of all use cases derivable from
hints 1, 2, 3, 3-1.

## Hints (recorded)

1. **Y4 build orchestration** (`~/Y4/docs/power_arch.md` §8.2) —
   3 queries (`Which targets stale` / `smallest set to regen` /
   `Why being rebuilt`).
2. **Farfalle-tree unkeyed-mode security analysis**
   (`~/다운로드/farfalle-tree-design.md`) — adsmt + EasyCrypt
   joint for `ε_acc` bound proof in `Adv^{CR}_{TF}(A)`.
3. **Y4 verification workflow full redesign** — wider than build:
   Verus / Lean 4 / Coq / Isabelle / Kani / Frama-C tier routing,
   `#[verus_to_isabelle::axiom]` opt-in, multi-ITP cross-validation.
4. (3-1) **Y4 P-redesign sub-cycle ledger** — 8 active sub-cycles
   (`~/Y4/.claude-notes/trackers/adsmt-integration-tracker.md` §10);
   adsmt provides generic API surface, consumer-specific decoding
   stays in Y4 / EasyCrypt / build-system code.

## Minimum set (union, locked)

Three callbacks. All consumer-specific shape lives in the label /
filter / cost domain, decoded by consumer post-processing.

| Kind | Callback shape | Use cases covered |
|---|---|---|
| **AcceptanceFilter** | `Fn(hyp_text: &str) -> bool` | stale/fresh (Y4 build), game-context sound (Farfalle/EC), axiom-optin (Y4 verif T-ii), lint rule pass (Y4 P-redesign.7) |
| **Labeller** | `Fn(hyp_text: &str) -> Option<String>` | category (Farfalle: statistical/algebraic/structural), tier routing (Y4 verif: Verus/Lean4/Coq/...), mode routing (Y4 verus2isabelle: sorry/axiom/smt-hybrid), Rocq theory routing (P-redesign.4), Isabelle wrapper mode (P-redesign.5) |
| **CostFunction** | `Fn(hyp_text: &str) -> u32` | regen-cost (Y4 build smallest-set query), proof obligation weight (Y4 verif tier ranking), lint rule severity (P-redesign.7) |

Items NOT in minimum set (out of L3 scope):
- **Comparator / second-opinion callback** (Z3 vs OxiZ dual
  backend cross-validation) — that's parallel solver invocation,
  not a hypothesis-level callback; runs at a different layer.
- **Explanation surface** — adsmt's "Why being rebuilt" is
  *output* from adsmt (already in `AbductiveCandidate.justification`
  + cert text), not a user-provided callback.

## Implementation timing

Per `v1_0_0_scope_expansion.md` (option A, bundled-into-v1.0.0)
and the in-session priority "[1 + 4 → 2]":

- L3 design + implementation is task **2** in the current
  priority list. Comes after L1 polish (1) + Tactic 실장 (4).
- L3 lands in `~/adsmt-lean-binding` as additional
  `#[leo4::export]` functions accepting `LeanCallback<Bool, (String,)>`
  / `LeanCallback<Option<String>, (String,)>` /
  `LeanCallback<u32, (String,)>` parameters.
- adsmt-engine side may need pre-processing hooks for the
  filter / cost callbacks to actually shape the candidate
  list. To be designed during step 2.

## How to apply

When implementing L3:
- Default behaviour: accept-all + no-label + zero-cost (no
  pre-existing tests break).
- Each callback is opt-in via a separate export variant or a
  `RunCheckSatOptions` struct.
- Label string is opaque to adsmt — consumer schemas (Y4 tier
  enum, Farfalle category, etc.) live entirely on the user
  side.
- All three callbacks share the `&str` hypothesis input form
  (SMT-LIB text rendering) for now — when proper hypothesis
  term rendering lands upstream (adsmt-core / adsmt-cert), the
  callback signature can stay the same.
