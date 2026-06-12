---
name: feedback-streaming-no-exit-on-command-error
description: "In the persistent-solver STREAMING model (verus runs one lu-smt per air context, pipes many commands over a pipe with an (echo \"<<DONE>>\") sentinel), NO single-command failure may std::process::exit — a mid-stream exit kills the whole run (the reader never sees the sentinel, dies on RecvError). A malformed/unknown-operator command must report an error and CONTINUE reading, like cvc5/z3 -in. Recurred twice: the 2026-06-08 fast-unknown driver crash and the rc.35 (abduce …) parse-error exit."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

In a persistent-solver **streaming** session, a single-command failure
must never terminate the process. verus runs **one** lu-smt per air
context and streams many commands over a pipe, delimited by an
`(echo "<<DONE>>")` sentinel; if lu-smt exits mid-stream the reader thread
hits EOF without the sentinel and the air layer dies with
`RecvError` / "Got too many empty lines!" — **the whole verus run
aborts**, not just the one query.

**Why:** the contract is the cvc5/z3 `-in` REPL one — a malformed command
prints an error line and the REPL keeps reading the next command.

**How to apply:** when adding a CLI command, ask "could this exit the
process on a per-command error?" For a **read-only query** command
(`(abduce …)`, `(get-abduct …)`, `(declare-abducible …)`, `(get-info)`,
`(echo)`) a parse/convert error must report (stderr diagnostic, keeping
stdout = verdicts + sentinels) and return a *continue* outcome, never
`DispatchResult::Error(code, …)` that the streaming loop turns into a
process exit. `--strict-commands` (batch validation, not streaming) may
still hard-fail — that's the `Raw` arm's policy; match it.

**Soundness caveat — `(assert)` is different.** A state-mutating command
that *drops a constraint* on error (e.g. `(assert (ite …))` that doesn't
convert) cannot just skip-and-continue: a later `(check-sat)` would be
unsound (it ignored an assertion — see
[[feedback-soundness-opaque-fallback]], dropping constraints destroys
Sat-soundness). The existing design is sound there: with OxiZ delegation
the session degrades + defers (OxiZ replays the full buffer); without
OxiZ, the assert path exits — which is the *sound* refusal. So the
report-and-continue rule is for the **read-only** query commands, where
skipping has zero verdict/soundness impact, not a blanket "never exit."

**Recurrences (this is a class, not a one-off):**
- **2026-06-08** — `-V adsmt` driver crash on a *fast* `unknown`
  (`air smt_get_model discovered_error.expect()` panic); same streaming
  DoS shape, closed by the canonical reason-unknown phrasing.
- **rc.35** — I introduced the `(abduce …)` exit: pre-rc.35 `(abduce …)`
  was `Command::Raw` (non-strict → warn + continue); my rc.35 dispatch
  arm parsed it as `Abduce` and returned `DispatchResult::Error(13, …)`,
  which the streaming loop exits on **unless OxiZ is configured**. Fixed
  (no bump): `Driver::recoverable_command_error` — stderr diagnostic +
  `Continue` for the abductive query commands; `--strict-commands` keeps
  the hard error. Integration test
  `adsmt-cli/tests/streaming_robustness.rs` spawns the binary on
  verus-fork's exact repro. See [[abductive-smtlib-surface]],
  [[verus-fork-integration]].
