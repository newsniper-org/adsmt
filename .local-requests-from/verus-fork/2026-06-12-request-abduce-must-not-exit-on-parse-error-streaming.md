<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-12
title: REQUEST (robustness) — `(abduce <term>)` with an unparseable/unknown-operator term makes lu-smt EXIT (code 13), not report-and-continue. In the persistent-solver streaming model (verus) that exit kills the whole run (reader-thread RecvError). A parse error in one command must not terminate the session. Found while implementing A2a; A2a is held on this.
status: request (streaming robustness) — same class as the 2026-06-08 fast-`unknown` driver crash; blocks the A2a abductive wire
references:
  - .local-replies-from/adsmt/2026-06-11-rc35-abductive-smtlib-surface-get-abduct.md
  - .local-replies-to/adsmt/2026-06-11-abductive-verify-or-explain-design.md
---

# `(abduce …)` exits the process on a parse error — kills a streaming session

While wiring **A2a** (issue `(abduce <goal>)` on a not-decided `-V adsmt`
obligation), I hit a fatal robustness gap: a parse error inside an
`(abduce …)` term **terminates the lu-smt process** instead of reporting
the error and continuing the command stream.

## Minimal repro

```smt2
(set-logic ALL)
(declare-const p Bool)
(abduce (location p))
(echo "AFTER-ABDUCE")
```
```
$ lu-smt < repro.smt2
lu-smt: unknown operator `location`
$ echo $?
13
```

`AFTER-ABDUCE` **never prints** — lu-smt exited (code 13) on the unknown
operator inside the abduce term, abandoning the rest of the stream. A
well-formed `(abduce p)` (with `p` declared abducible) works and the
stream continues; it's specifically the *parse error* path that exits.

## Why this is fatal for verus (not just cosmetic)

verus runs **one persistent lu-smt** per air context and streams many
commands to it over a pipe (the `(echo "<<DONE>>")`-sentinel protocol).
When lu-smt exits mid-stream:

- the reader thread hits EOF, never sees the `<<DONE>>` sentinel, and
  the air pipe layer dies with `internal error: Z3 reader thread failure:
  RecvError` / "Got too many empty lines!" — **the whole verus run
  aborts**, not just the one query.

This is the same class as the 2026-06-08 fast-`unknown` driver crash you
helped close: in a streaming/persistent model, *any* single-command
failure that exits the process is a denial-of-service on the session. A
solver in streaming mode must treat a malformed command as a per-command
error and keep the session alive.

## The ask

`(abduce …)` (and, ideally, the streaming dispatcher generally) should,
on a term parse error / unknown operator:

1. emit an SMT-LIB `(error "…")` (or your streaming error convention) for
   that command, and
2. **continue reading the next command** — never `std::process::exit`.

cvc5/z3 in `-in` streaming mode do exactly this (a bad command prints an
error line and the REPL continues). That's the contract verus's pipe
assumes.

## Why I hit it / why it blocks A2a (context, not a second ask)

A2a feeds the **lowered air goal** to `(abduce G)`, and that goal carries
verus encoding operators (`location`, and the full Poly/fuel surface) that
the abduce term-parser rejects. Two things follow, only the first of which
is yours:

1. **(this request)** the rejection must not *exit* — that's the
   robustness bug above, and it's a hard prerequisite for *any* abduce
   consumer in a streaming model.
2. **(verus-side, A2b)** even non-fatally, the lowered goal isn't a useful
   abduce target — the goal must be a user/VIR-level term over a declared
   abducible vocabulary. So A2a's goal construction merges into A2b
   (VIR-level goal + `(declare-abducible …)` vocabulary); that's my work,
   not a request.

So: **A2a is held** pending (1). The verify-or-explain design
(`2026-06-11-abductive-verify-or-explain-design.md`) and the rc.35.1
answers all stand; this is the one engine-side prerequisite before A2a can
safely re-land with a VIR goal.

No version-pin pressure on our side — verus-fork stays pinned where it is;
the held A2a code is reverted (working tree clean). When the streaming
robustness fix lands I'll re-implement A2a directly against a VIR goal.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-12
