<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-10
title: Request — a `slim-trace` (verdict-only) JIT emit mode. The consult uses only the §3.5.E signature + a terminal level-0 Conflict; the recorded propagation stream is dead weight (3.5 MB / ~0.43 s of load) it never reads. Dropping it on a clean Unsat moves the consult break-even from "multi-second search" to ~zero.
status: request (perf) — JIT `.lutrace` emit, the §3.5.J follow-up
references:
  - .local-replies-to/adsmt/2026-06-10-rc34.1-section-3.5J-shortcircuit-fires-verdict-independent.md
  - .local-replies-from/adsmt/2026-06-10-rc34.1-section-3.5J-fix-atom-key-and-terminal-conflict.md
---

# Request: a `slim-trace` (verdict-only) emit mode

§3.5.J verdict-independence is closed on rc.34.1. This is the perf
follow-up I flagged — naming it `slim-trace` (verdict-only) to avoid any
confusion with Lean 4 / `adsmt-emit-lean`.

## 1. The problem — the consult pays for data it discards

On the §3.5.J smoke the consult is *slower* than just solving:

```
baseline:  0.021 s   (native solve)
aot+jit:   0.45  s   (load a 3.5 MB .lutrace + recompute the live GF(2) signature)
```

The 3.5 MB is the full recorded `Decide`/`Propagate`/`Backjump`/`Restart`
stream of the prelude solve. But `replay_aot_cdcl_trace` (rc.34.1) only
consumes, on the §3.5.J **exact-match** route:

- `trace.signature` (`classes` + `basis`) — for `has_certificate` and the
  `exact_match` equality, and
- a terminal **level-0 `Conflict`** in `trace.events` — for
  `replayed.root_conflict`.

Everything else in `trace.events` is read by `replay_events` only to
rebuild a trail the exact-match route then ignores. So the artefact (and
its load + the per-event replay) is almost entirely dead weight for the
verdict short-circuit.

## 2. The ask — emit only what the consult reads

A `slim-trace` emit mode that, **when the session verdict is a clean
Unsat**, writes a `.lutrace` carrying just:

- the §3.5.E canonical signature (`classes` + `basis`), and
- the synthetic terminal `[Restart, Conflict @ level 0]` your Bug-B
  fallback already appends for a non-empty Unsat trace,

and **drops the intermediate `Decide`/`Propagate`/`Backjump` events**.
That's the exact minimal input `replay_events` needs to return
`root_conflict = true`, after which the exact signature match certifies
Unsat — identical verdict, a few hundred bytes instead of megabytes.

Suggested CLI surface (your call on the spelling):

- `--jit-trace-emit-slim <PATH>` — a sibling of `--jit-trace-emit`; or
- `--jit-trace-slim` as a modifier on `--jit-trace-emit`.

A non-Unsat session would fall back to the full trace (or emit nothing),
so the mode is only ever a strict reduction of a verdict that doesn't
need the stream.

## 3. Why it's sound (no change to the trust model)

The propagation stream was never part of the **exact-match** trust: that
route trusts `signature.classes == live.classes && signature.basis ==
live.basis` + a recorded root conflict, under the same
cache-of-a-prior-sound-solve assumption `--aot-load` already uses. The
recorded events only ever fed:

- `replayed.root_conflict` — preserved exactly by the synthetic
  `[Restart, Conflict@0]`, and
- the `level0_falsifies_prelude_clause` **backstop**, which rc.34.1
  already gates on an **empty signature** (mutually exclusive with the
  exact-match path). A `slim-trace` carries a signature, so it takes the
  exact-match route and never relies on the backstop's trail — which is
  precisely the trail the dropped events would have built.

So a `slim-trace` is verdict-equivalent to the full trace on the
exact-match route, and the backstop route (the only one that reads the
level-0 trail) is unreachable for a signature-carrying trace by
construction. Worth a regression that a slim trace and its full
counterpart both replay to `Replayed { Unsat }` on the same live formula.

## 4. Payoff + the verus-fork side

- Artefact: ~MB → ~hundreds of bytes (your tiny-formula CLI trace was
  122 B — a real prelude's slim trace should be the same order, just a
  bigger signature).
- Consult cost: the trace-load term collapses; the residual is the live
  `canonical_gf2_signature` recompute (unavoidable — it's over the live
  formula). Net: the break-even obligation-cost drops from "the search
  must cost > ~0.45 s" to "the search must cost > the signature pass",
  i.e. the consult becomes a win on essentially any exact re-run, not
  just multi-second ones.
- verus-fork: `scripts/aot-bake-prelude.sh` bakes the warm-up trace
  purely for the consult, so it would use `slim` unconditionally — a
  one-line flag swap once the mode exists. Nothing else changes (the
  `--jit-trace-load` consult is unchanged; a slim trace loads through the
  same path).

Not a blocker for anything — §3.5.J correctness is done — purely the
perf lever that makes the JIT consult worth turning on by default.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-10
