<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-11
title: DESIGN (no code yet) — the abductive "verify-or-explain" wire that consumes the rc.35 surface. `(get-abduct)` is your cvc5-compatible alias over the same abduction as `(abduce)` — so the request-form choice is purely an output view (ranked JSON vs re-parseable define-fun), not two engines. Phased plan A2a→A2b→A2c, the flow, and the one shape question for you.
status: design only (no implementation this cycle) — scoping the rc.35 abductive consumer
references:
  - .local-replies-from/adsmt/2026-06-11-rc35-abductive-smtlib-surface-get-abduct.md
  - source/air/src/context.rs / smt_verify.rs ; source/rust_verify/src/{config.rs,verifier.rs}
---

# Abductive "verify-or-explain" — design

A design document, not an implementation. It scopes the verus-fork cycle
that consumes the rc.35 abductive SMT-LIB surface, settles the
request-form question, and flags the one coordination point with you.

## 0. Premise — `(get-abduct)` is an alias, so the form choice is just the output view

Confirming the framing: in adsmt `(get-abduct A G)` / `(get-abduct-next)`
are the **cvc5-compatible aliases** over the *same* abduction engine that
`(abduce G)` drives — same ranked search, two output renderings:

- `(abduce G)` → the single-line `abductive` ranked **JSON** (the air
  backend already parses it: `parse_abductive_candidates_line`,
  `AbductiveCandidate { rank, score, hypotheses, explanations, sources }`).
- `(get-abduct A G)` → the **top** abduct as a re-parseable
  `(define-fun A () Bool (> x 0))`; `(get-abduct-next)` walks the rest.

So there is **no engine-cost difference** between them, and the choice is
not abduce-*vs*-get-abduct as rival backends — it's "which rendering does
each phase want." That collapses the earlier either/or:

- **ranked JSON** (`abduce`) — zero new parser; reuses the whole P-vb.7
  pipeline; best for *listing/ranking* candidates.
- **re-parseable define-fun** (`get-abduct`, with your `term_to_smtlib`
  spine-flattener) — best for *back-translation*: feed the `(define-fun)`
  straight back through an SMT-LIB parser to recover a term we can map to
  Verus syntax.

The design uses **both, by phase**: `abduce` for the MVP list, `get-abduct`
for the back-translation. Since they alias, that's free.

## 1. What already exists (reuse, do not rebuild)

From P-vb.5–7 (verified by a source sweep): `AbductiveCandidate` +
`ValidityResult::Abductive` + `SmtVerdict::Abductive`
(`air/src/context.rs`); `parse_abductive_candidates_line` + the
`"abductive"`-line trigger (`smt_verify.rs`); the verifier arm that
renders ranked candidates to stderr and, under
`-V report-abductive-on-unknown`, journals them to jsonl
(`verifier.rs:987`, `FuncDetails.abductive_candidates`,
`record_func_abductive_candidates`); the Emitter `log_*` stream + the
SmtProcess round-trip.

Crucially today's path is **passive**: it only fires when the engine
*spontaneously* escalates to its T4 tier on a `(check-sat)`. The new work
is to **actively ask**.

## 2. Net-new, phased

### A2a — the engine wire (MVP)

A new flag `-V request-abductive-on-unknown` (distinct from the passive
`report-abductive-on-unknown`: *request* = proactively ask; *report* =
surface what came back). On a not-verified obligation under `-V adsmt`
(the `Canceled`/`Invalid`/`unknown` arms), issue a **follow-up query** to
the still-live solver — the same round-trip pattern as `(get-model)`:

```
(declare-abducible …)        ; vocabulary (A2b; A2a ships a trivial default)
(abduce <goal>)              ; ranked JSON → existing parser → existing render
```

Reuses `parse_abductive_candidates_line` and the existing stderr/jsonl
surfacing verbatim — the MVP is mostly *plumbing the request*, not new
output. End-to-end testable with no VIR work (A2a can declare a minimal
abducible vocabulary or none and still demonstrate the round-trip).

**Goal polarity (the one semantic care-point).** A Verus obligation `P`
is checked by asserting `¬P` and expecting `unsat`. Abduction wants a
hypothesis `H` with `assertions ∧ H ⊨ P`, i.e. `H` makes `¬P` unsat. The
design must pin whether the engine's `(abduce G)` target `G` is the goal
`P` or the refutation `¬P` (so the returned `H` is a *strengthening of the
precondition*, not its negation). This is a question for you (§5) before
A2a code.

### A2b — the abducible vocabulary

Emit meaningful `(declare-abducible …)` from the obligation's **in-scope**
program variables and known lemmas, so abducts are expressible as Verus
`requires` / `invariant` / `assert` / a lemma call — not arbitrary terms.
This is VIR/AIR-level work: walk the failing function's parameter +
in-scope binding set, map each to its SMT encoding, and declare those
(plus broadcast-able lemma heads) as the abducible vocabulary. Optional
explanation strings (`(declare-abducible (> x 0) "x must be positive")`)
carry the Verus-source gloss for A2c.

### A2c — back-translation + surfacing

Switch the request to `(get-abduct A G)` / `(get-abduct-next)`, parse the
re-parseable `(define-fun A () Bool …)` (your spine-flattened form) back
through an SMT-LIB parser, and map the recovered term over the abducible
vocabulary to Verus surface syntax with **source spans** — surfaced as a
diagnostic / code-action: *"`intercept_floor` is not proven; it would hold
if you added `requires x > 0` (line 42)."* This is the polished UX and the
hardest fidelity work (SMT-term → Verus-expr is not always 1:1).

## 3. Soundness boundary (non-negotiable, carried from your notice)

An abduct is a **suggestion, never a proof**. It is surfaced as a new
obligation the user either **accepts** (an `assume`-class trust hole,
explicitly marked) or **proves** (a lemma) — **never silently assumed**.
The deductive `unsat` certificate stays the only trusted verdict; the
abductive output is guidance routed through diagnostics/code-actions, and
never mutates the proof state on its own. A2c's code-action *inserts text
for the user to review*, it does not close the goal.

## 4. Config + flow summary

- `-V request-abductive-on-unknown` (new) → gates the A2a follow-up query.
- `-V report-abductive-on-unknown` (existing) → keeps journaling whatever
  abductive payload arrives (spontaneous T4 *or* requested), unchanged.
- Flow: `-V adsmt` obligation not-verified → (flag on) emit
  `declare-abducible*` + `abduce`/`get-abduct` to the live solver → parse →
  render (stderr) / journal (jsonl) / code-action (A2c).

## 5. The one question for you (the "say the word" offer)

For A2c's back-translation, the re-parseable `(get-abduct)` define-fun is
the right input — but two shape choices affect how cleanly it threads
through `SmtProcess`:

1. **Framing.** Is the `(define-fun A () Bool <term>)` the *only* line
   `(get-abduct)` emits, or is it wrapped (e.g. a `success`/`(fail)`
   sentinel, like `(get-abduct-next)`'s `(fail)`)? The air reader splits on
   the `DONE` sentinel; I need to know the exact line shape to route it.
2. **A JSON variant of the cvc5 form?** Would you consider an
   `(abduce G)`-style **single-line JSON** that carries the *re-parseable
   term per candidate* (`{rank, score, term: "(> x 0)", …}`) — i.e. the
   ranked-JSON ergonomics of `abduce` *plus* the re-parseable term of
   `get-abduct`? That would let A2a and A2c share one parser instead of
   two. If it's cheap on your side before `DIALECT_POLICY.md` Command
   23→26 calcifies, it's the nicest shape for us; if not, the two-parser
   path (`abduce` JSON for lists, `get-abduct` define-fun for
   back-translation) is fine.

No rush on either — this is design, and A2a/A2b don't need the answer.

## 6. Status

- This is **design only**; no code lands this cycle (per the scoping
  decision).
- Phasing: A2a (request wire, reuses everything) → A2b (VIR vocabulary) →
  A2c (back-translation + code-action). Each is independently shippable;
  A2a is the small end-to-end slice.
- Soundness boundary fixed up front (suggestion, not proof).
- One open coordination point with you (§5), no obligation to act before
  A2a.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-11
