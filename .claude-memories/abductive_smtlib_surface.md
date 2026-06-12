---
name: abductive-smtlib-surface
description: "rc.35 exposed adsmt's `Abductive` verdict as explicit cvc5-compatible SMT-LIB commands — `(declare-abducible)`, `(abduce)`, `(get-abduct)`, `(get-abduct-next)` — so a verifier (Verus) can ASK what hypothesis would discharge a goal. Before rc.35 abduction was reachable only via the engine's internal `(check-sat)` T4 escalation; `(abduce …)` parsed but fell to `Command::Raw` and was ignored. This is the integration surface for adsmt's abductive-DEDUCTIVE value: prove-when-valid (deductive, certified) + say-what's-missing-when-not (abductive, ranked)."
metadata: 
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

# Abductive-reasoning SMT-LIB surface (rc.35)

adsmt's fourth verdict — `SatResult::Abductive { candidates }` (ranked
hypotheses that would discharge a goal) — is the project's headline
differentiator over Z3/cvc5-as-oracle. rc.35 made it an **explicit,
cvc5-compatible SMT-LIB surface** so a front-end can *request* an abduct
rather than only receive one when the engine happens to escalate to its
T4 tier on a `(check-sat)`.

## The commands (parser → CLI → `Solver`)

- `(declare-abducible <pattern> [<explanation-string>])` →
  `Solver::register_abducible(Abducible::new(term, "declared")[.with_explanation])`.
  Declares the **vocabulary** of hypotheses the engine may propose. With
  no declared abducibles the engine abduces over an empty vocabulary, so
  the caller (Verus, Lean) declares the in-scope program variables /
  lemmas it would accept as a fix.
- `(abduce <goal>)` — **adsmt-native**; emits the full ranked candidate
  set as the single-line `abductive` JSON (the same shape the
  `(check-sat)` abductive verdict emits, so the Verus jsonl reporter +
  Lean `smt_abduce` parse it with the existing path).
- `(get-abduct <name> <goal> [<grammar>])` — the **cvc5 SMT-LIB
  abduction extension**; emits the top-ranked abduct as a re-parseable
  `(define-fun <name> () Bool <body>)` and arms the cursor. The optional
  grammar arg is accepted and ignored (adsmt abduces over the declared
  abducibles).
- `(get-abduct-next)` — cvc5 incremental form; emits the next ranked
  abduct (adsmt already ranks the whole set → just a cursor over it),
  `(fail)` when exhausted or with no prior `(get-abduct …)`.

## Implementation notes

- Parser `Command` enum +3: `DeclareAbducible { pattern, explanation }`,
  `Abduce { name: Option<String>, goal }` (both `(abduce)` and
  `(get-abduct)` route here; the cvc5 form sets `name`), `GetAbductNext`.
  `FROZEN_VARIANTS` 23 → 26; `DIALECT_POLICY.md` + `tests/dialect_surface.rs`
  updated in lockstep (the variant set is freeze-enforced).
- CLI `term_to_smtlib(&Term)` flattens the curried HOL application spine
  `((> x) 0)` → `(> x 0)`. **Why it's needed:** the engine's `Term`
  Display prints `> x 0` (space-separated, NO outer parens — HOL curried
  app), which cvc5 / Verus cannot re-parse. The spine-flattener walks
  left through `App` heads collecting args, then prints
  `(head arg1 arg2 …)`. `render_abduct_body` conjoins a candidate's
  hypotheses (`(and …)`, lone hyp verbatim, empty → `true`).
- CLI `AbductCursor { name, candidates: Vec<RankedCandidate>, next }`
  driver state; reset on `(reset)` / `(reset-assertions)`.

## Why this matters — the abductive-deductive integration for Verus

This is the cheapest path for a verifier to benefit from adsmt's
abductive-**deductive** reasoning ("verify-or-explain"):

1. **Deductive (trusted):** when an obligation is valid, adsmt proves
   `unsat` with a certificate re-checkable in Lean/Rocq/Isabelle.
2. **Abductive (advisory):** when it is *not*, Verus asks `(get-abduct)`
   with the obligation's in-scope variables declared as abducibles, and
   surfaces the top abduct as a diagnostic / code action ("fails; would
   hold if you added `requires x > 0`"). A strictly better failure mode
   than "unknown / timeout".

**Soundness discipline (non-negotiable):** an abduct is a *suggestion*.
Verus must treat an abduced hypothesis as a new obligation the user
accepts (a trust hole like `assume`) or must prove (a lemma) — **never
silently assume it**. The deductive `unsat` is the trusted verdict; the
abductive is guidance.

## rc.35.1 — re-parseable `term` in the ranked JSON + design answers

verus-fork's "verify-or-explain" design (phased A2a request-wire → A2b
VIR abducible vocabulary → A2c back-translation+code-action) surfaced
that the `(abduce)` JSON's `hypotheses` were the engine's curried-HOL
`Term` Display (`> x 0`, no outer parens) — **not re-parseable**, so A2c
couldn't recover the term. rc.35.1 routes `hypotheses` AND a new
top-level **`term`** field (the conjoined abduct, byte-identical to
`(get-abduct)`'s define-fun body) through `term_to_smtlib`. So the ranked
JSON now carries `{rank, score, term:"(> x 0)", hypotheses:["(> x 0)"], …}`
and A2a (list) + A2c (back-translate) share **one** parser. Additive
field; Command enum unchanged (wire-compatible).

**Three coordination answers locked (durable facts about the surface):**

1. **Goal polarity.** `(abduce G)` / `(get-abduct A G)` take `G` = the
   **goal P itself** (NOT its refutation `¬P`). The SLD
   `candidates(goal)` finds hypothesis sets `H` with `H ⊢ goal` (direct
   abducible match α-equiv to the goal, or Horn-rule head resolution), so
   the returned `H` is a **strengthening of the precondition** — exactly
   cvc5's `(get-abduct A φ)` where `φ` is the conjecture. A Verus
   obligation `P` (checked as `¬P` → expect unsat): abduce on `P`, not
   `¬P`.
   - **Nuance:** adsmt's abduce is **derivation-based** — `H ⊢ G` over the
     declared abducible vocabulary + Horn rules; it does NOT check
     `(F ∧ H)` consistency against the current assertion stack `F` the way
     cvc5 does (the SLD engine sees only `&self.abducibles`, not the
     asserted formula). So an abduct **must be re-checked** (re-verify `P`
     under `H`) — which aligns with the soundness discipline (the abduct
     is a suggestion the user justifies) anyway.

2. **`(get-abduct)` framing.** Emits **exactly one line** —
   `(define-fun <name> () Bool <term>)` on success, or `(fail)` on
   no-abduct / exhausted / no prior `(get-abduct)`. No success wrapper /
   sentinel; splits cleanly on the consumer's own `DONE` echo sentinel.

3. **JSON variant** — done (the `term` field above).

## Consistency-enforced abduction (`:abduct-consistency`)

verus-fork's verify-or-explain design surfaced that the `H ⊢ G` re-check
is **necessary but not sufficient**: if `H` is *inconsistent with the
assertions* `F`, then `F ∧ H` is unsat and `F ∧ H ⊨ P` holds **vacuously**
— so a contradictory abduct (`requires x > 0 ∧ x < 0`) passes the
downstream re-check and gets surfaced as a real suggestion (the function
becomes vacuously verified / uncallable, and the user can't tell). The
pipeline stays *sound* (H is never auto-assumed) but the UX is misleading.

Fix (opt-in): **`(set-option :abduct-consistency true)`** → the full cvc5
`(get-abduct)` semantics, `F ∧ H ⊨ G` **AND** `SAT(F ∧ H)`. The CLI
`Driver::abduct_is_consistent(hyps)` checks `SAT(F ∧ H)` **engine-side** —
push a scope, assert each hypothesis, `check-sat` (honouring the session
`:rlimit`/`:timeout` deadline), pop — and returns `false` only when
**proven `Unsat`** (an `Unknown` is treated as possibly-consistent, so a
real strengthening is never falsely dropped). Engine-side beats the
consumer self-filtering: no N `SmtProcess` round-trips per failed
obligation, no assertion-stack re-serialisation, and the *ranking*
reflects only useful abducts.

Two surfaces, by their nature:
- `(abduce …)` (JSON) — keeps every candidate but adds a **`consistent`**
  boolean per candidate (present only when the flag ran; absent = "not
  checked", distinct from `false` = "proven inconsistent"). The consumer
  filters / dims the vacuous ones.
- `(get-abduct …)` / `(get-abduct-next)` (the `(define-fun …)` form, no
  field slot) — **drop** the inconsistent abducts outright (true cvc5
  `(get-abduct)` behaviour).

Default off keeps the cheap derivation-only mode. CLI-verified: `F: x<0`,
abduct `x>0` → `(get-abduct)` `(fail)` + `(abduce)` `consistent:false`;
`F: x>5`, abduct `x>0` → survives + `consistent:true`. Landed as a
follow-up commit on rc.35.1 (NO version bump — additive option + JSON
field, wire-compatible). 2 regressions
(`abductive_json_carries_consistent_field_when_checked` + the
absent-by-default assertion).

## Theory-aware abductive SEARCH (`:abduct-theory`)

verus-fork found (wiring A2) that the abduce **search** is purely
syntactic — SLD / α-match + a Horn rule base — and **not theory-aware**:
`(abduce (> (+ x y) 0))` with abducibles `x>0`, `y>0` returns `[]`
(`x>0 ∧ y>0 ⊬ x+y>0`), `(abduce (>= x 1))` with `x>0` returns `[]` (no
int reasoning). It returns a candidate only when the goal is itself a
declared abducible (or Horn-resolves to one). Verus obligations are all
theory/arithmetic/quantifier-shaped, so SLD abduce is empty on
essentially all of them. (The `:abduct-consistency` *check* was
theory-aware via `SAT(F ∧ H)`; the *search* that proposes `H` was not.)

Fix (opt-in): **`(set-option :abduct-theory true)`** runs a
theory-entailment search. `Driver::abduce_theory` does a bounded
**minimal-subset** search over the **declared abducibles** (kept CLI-side
in `Driver::declared_abducibles`, since `Solver`'s `AbducibleSet` has no
public iterator): for each subset `H`, keep it iff `F ∧ H ⊨ G`
(`Driver::entails_under_theory`: `F ∧ H ∧ ¬G` UNSAT — the **dual** of the
`:abduct-consistency` `SAT(F ∧ H)` check; `¬G` built as a `(not goal)`
SExpr → `convert_expr`) **and** `SAT(F ∧ H)` (an inconsistent `H` entails
`G` vacuously). So `:abduct-theory` ALONE is the full cvc5
`(get-abduct A φ)` contract — `F ∧ H ⊨ G` AND `SAT(F ∧ H)`, theory-aware
on both halves.

- BFS by subset size (0..=MAX_ABDUCT_SIZE=3), **pruning any superset of an
  already-found minimal abduct**, capped at 32 results / 512 subsets. The
  empty subset is tried first: if `F ⊨ G` already, the trivial `true`
  abduct is the single minimal answer (and prunes every non-empty subset,
  which would otherwise *all* spuriously "entail" `G`). Ranked by
  minimality (subset size). Entailment checked first (rejects the common
  non-entailing subset in one `check-sat`), consistency only for the
  entailing ones. Each `check-sat` honours `:rlimit`/`:timeout`.
- Closed-vocabulary, not open synthesis (not cvc5's hard part).

**Why OPT-IN, not opt-out/always (compared all three):** SLD and theory
are **complementary, not nested** — SLD uses a separate
`HornRuleBase`/`SchematicHornRuleBase` (declarative, F-independent) the
theory search (reasoning only over `F`) can't reproduce, so theory as the
default would silently DROP the SLD Horn/α-match candidates the
declarative consumers (Lean `smt_abduce`, T4 escalation) rely on. Plus
theory pays a `check-sat` per subset (vs SLD's zero) → always-on would
tax every cheap declarative abduce. opt-in is symmetric with the
already-opt-in `:abduct-consistency` (together = full cvc5). Only pull
toward default-on is cvc5 `(get-abduct)` being theory-by-default — left as
a possible future *per-surface* default (get-abduct only). **Type-system
note (user asked):** typing CAN'T rescue opt-out/always — the regression
is a *runtime semantic* coverage gap (F doesn't contain the Horn rules) +
*runtime cost*, neither addressable by a compile-time type. What typing
CAN do is make the mode/invariant total: encode the search strategy as an
enum/typestate (not a stringly `set-option` bool) and make "a theory
abduct that wasn't consistency-filtered" unrepresentable. Orthogonal to
the opt-in default. **LANDED (user asked for both, no bump):** (a) the
search strategy is derived once into a total `AbductMode` enum
(`Sld`/`SldConsistent`/`Theory`; `Options::abduct_mode`) so the dispatch
is one exhaustive `match` and "theory subsumes consistency" lives in
exactly one place — replacing the `if abduct_theory … else …` +
`check = consistency && !theory` bool gates. (b) `mod abduct`'s
`TheoryAbduct` newtype (private fields; sole constructor `verified` runs
BOTH `entails_under_theory` + `abduct_is_consistent`) makes an unverified
theory abduct **unrepresentable** — `abduce_theory` can only push a
`TheoryAbduct`, so the vacuous-abduct hazard is a compile-time
impossibility on that path. The submodule reaches `Driver`'s private
checks as a descendant of the crate root. Pure refactor (behaviour
unchanged); 1100 → **1101** green. Mirrors adsmt's own kernel discipline
(`Theorem` constructible only via the 12 rules, not deserializable).

CLI-verified: `x>0 ∧ y>0 ⊨ x+y>0` → `(and (> x 0) (> y 0))`; `x>0 ⊨ x≥1`;
vacuous (F: x<0) → dropped; `F ⊨ G` → `true`; default (no flag) → SLD `[]`.
6 integration regressions (`adsmt-cli/tests/theory_abduction.rs`). Landed
on rc.35.1 (NO bump — additive option). 1094 → **1100** green. Reply:
`.local-replies-to/verus-fork/2026-06-12-theory-aware-abductive-search-landed.md`.

## Gaps still on the Verus side (the wire is now adsmt-complete)

- **Trigger:** Verus's air backend already *parses* the `abductive` JSON
  (`air/src/smt_verify.rs::parse_abductive_candidates_line`); what's left
  is to *issue* `(get-abduct …)` on a failed/`unknown` obligation.
- **Vocabulary:** Verus must emit `(declare-abducible …)` for the
  in-scope vars / lemmas so the abducts are actionable.
- **Back-translation + surfacing:** map the abduct `Term`s back to Verus
  surface syntax / spans for the diagnostic or code action.

See [[verus_fork_integration]] (the §3.x arc), [[nbg-fol-hol-challenge]]
(another abductive self-challenge). rc.35 reply/notice:
`.local-replies-to/verus-fork/2026-06-11-rc35-abductive-smtlib-surface-get-abduct.md`.
