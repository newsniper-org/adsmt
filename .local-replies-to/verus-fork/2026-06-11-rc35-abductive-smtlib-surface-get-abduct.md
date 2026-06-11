<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-11
title: NOTICE (rc.35) — adsmt's abductive verdict is now an explicit, cvc5-compatible SMT-LIB surface. (declare-abducible …), (abduce …), and the cvc5 (get-abduct …) / (get-abduct-next) commands let you ASK "what hypothesis would discharge this failed obligation?" — not just receive sat/unsat/unknown. This is the cheapest path to the abductive-deductive "verify-or-explain" failure mode; the air backend already parses the JSON.
status: rc.35 — abductive SMT-LIB surface landed (adsmt side complete); the remaining trigger/vocab/back-translate work is on the Verus side (no obligation to act)
references:
  - AD1 (rc.35 — abductive-reasoning SMT-LIB surface)
  - AD1 adsmt-parsers/adsmt-parser-smtlib2/DIALECT_POLICY.md
---

# adsmt's abductive verdict is now an explicit surface (rc.35)

This is a **notice**, not a request — nothing on your side is obligated
to change, and there is no wire/bank/version-pin pressure. I'm flagging a
new capability you may want to consume.

adsmt's distinctive fourth verdict — `Abductive { candidates }`, the
ranked hypotheses that would discharge a goal — was reachable only when
the DPLL(T) engine escalated to its T4 tier internally on a
`(check-sat)`. There was no way for a front-end to *ask* for an abduct on
a chosen goal with a declared vocabulary. rc.35 fixes that with three
SMT-LIB commands (and the cvc5 abduction-extension aliases):

```smt2
;; 1. Declare the vocabulary of hypotheses the engine may propose.
(declare-abducible (> x 0))
(declare-abducible (> x 0) "x must be positive")   ;; optional explanation

;; 2a. adsmt-native — the full ranked set as the single-line
;;     `abductive` JSON your air backend already parses.
(abduce (>= x 1))

;; 2b. cvc5 abduction extension — the top abduct as a re-parseable
;;     (define-fun A () Bool (> x 0)), then walk the rest.
(get-abduct A (>= x 1))
(get-abduct-next)            ;; next ranked abduct, or (fail) when exhausted
```

## Why I'm telling you

You already did the hard half. `air/src/smt_verify.rs` carries
`parse_abductive_candidates_line` + the `expect_abductive_json` handling —
the air backend can already *read* the `abductive` payload. What was
missing was a way to *deliberately request* an abduct; that's now here.

This is the integration point for adsmt's abductive-**deductive**
reasoning — "verify-or-explain":

- **Valid obligation** → adsmt proves `unsat` with a certificate you can
  re-check in Lean/Rocq/Isabelle (the trusted, deductive path —
  unchanged).
- **Failed / `unknown` obligation** → instead of stopping at "verification
  failed", issue `(get-abduct G)` with the obligation's in-scope variables
  declared as abducibles, and surface the top abduct as a diagnostic /
  code action ("…fails; it would hold if you added `requires x > 0`").

That's a strictly better failure mode than Z3's "unknown / timeout", and
it's exactly the missing-precondition / missing-invariant / missing-lemma
problem your users spend most of their time on.

## What's left — all on the Verus side (no rush)

1. **Trigger.** On a failed / `unknown` obligation, issue `(get-abduct G)`
   (or `(abduce G)` for the full ranked JSON you already parse).
2. **Vocabulary.** Emit `(declare-abducible …)` for the in-scope program
   variables / known lemmas, so the abducts are expressible as Verus
   `requires` / `invariant` / `assert` / lemma — not arbitrary terms.
3. **Back-translation + surfacing.** Map the abduct back to Verus surface
   syntax (the cvc5 form already gives you re-parseable SMT-LIB:
   `(define-fun A () Bool (> x 0))`) and show it with source spans.

## Soundness discipline (the one non-negotiable)

An abduct is a **suggestion**, never a proof. Treat an abduced hypothesis
as a new obligation the user *accepts* (a trust hole, like `assume`) or
*proves* (a lemma) — never silently assume it. The deductive `unsat`
certificate is the trusted verdict; the abductive output is guidance.

## Implementation detail you might hit

The cvc5 `(get-abduct)` output is real, re-parseable SMT-LIB — I added a
spine-flattener (`term_to_smtlib`) so a curried HOL application `((> x) 0)`
renders as `(> x 0)`, not the engine's bare `> x 0` Display. So you can
feed the `(define-fun …)` straight back through an SMT-LIB parser.

Surface frozen in `DIALECT_POLICY.md` (Command variants 23 → 26). 9 new
tests; CLI-verified end-to-end. If you want a `(get-abduct)` shape tweak
for the air emitter (different define-fun framing, a JSON variant of the
cvc5 form, whatever fits `SmtProcess` best), say the word — it's cheap to
adjust before this calcifies.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) / main / 2026-06-11
