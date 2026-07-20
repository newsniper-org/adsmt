# adsmt-ir-asp — the typed-ASP face

The closed-world / least-model / **stable-model** sibling of the SMT-LIB face
(`adsmt-ir-smtlib`). Both are 1:1 subsets of the unified surface, elaborating to
the *same* typed CIC kernel (`adsmt-ir`); the kernel's **`def`** (closed-world)
vs **`open`** (classical/theory) modality is the hook. Rules become `def` atoms;
SMT theory atoms are `open`; they cooperate. This crate is a **frontend, not the
trusted core** — everything it elaborates is re-checked by the kernel admitters,
so a face bug yields only a `FaceError`, never a trusted ill-typed term.

This design is the converged output of two design workflows (2026-06-25) plus the
user's decisions; see the memory `asp-face-design.md` for the full record.

## 0. Thesis — theory-first + abduction-native

Plain typed-Datalog would be "a worse Datalog". What this substrate uniquely
offers, and what we design around:

1. **Theory interior** — an ASP rule body can carry `open` SMT theory atoms
   (Int / EUF / datatype) decided by the *same* engine. The ASP⊕SMT seam.
2. **Abduction is the exact DUAL of a rule** — fully merged, not bolted on. An
   **abducible is a `def`-completion-*less* `Open` atom** (the opposite of a
   `def` atom, whose Clark completion `p ↔ body` forces it false-by-default).
   The dormant abductive-engine rule base becomes *the* ASP rule base — **one
   rule IR, two evaluation directions** (forward least-fixpoint for answer-set
   membership; backward SLD for abduction). **Deduction = empty-abducible
   abduction** (`entailed(G) ⟺ abduce(G) = {}`).

## 1. The surface — a negation ladder

The elaborator *infers* a program's level and **structurally refuses to outrun**
the rung whose gate exists (parses-but-abstains above it — never approximates).
The ordering deliberately puts the theory interior (L1) *before* negation,
because it is the differentiator and is sound at the definite level for free.

| Level | Adds | Gate | Kernel carrier |
|---|---|---|---|
| **L0** | typed sorts/preds, facts, **definite** rules, ground queries | Horn least-fixpoint | `Inductive` (rec) / `Def`-completion (non-rec) |
| **L1** | **theory interior**: `open` SMT atoms in bodies | least-fixpoint **⊳ θ** | + `Open` leaves |
| L2 | **stratified** `not`, integrity constraints `:- B` | perfect / stratified | `Def`-completion |
| **L3** | **stable models** (non-stratified `not`), `#external` | GL reduct ⊳ θ (bounded sweep now; + loop gate later) | + loop gate |
| L4 | choice `{…}` + disjunctive heads | model + minimality | |
| **L5** | aggregates + **weak constraints** / optimization | bounded fixpoint + opt | `Open` arith |
| **L6** | **first-class abduction** | merged ALP | abducible ⇒ `Open` choice atom |

## 2. The spine (built first; both workflows converged on it)

- **def/open modality boundary** — `not p` is legal only on a stratified `def`
  predicate (closed-world = "not derivable"); on an `open` predicate `not`
  routes to classical theory negation. The elaborator rejects wrong-modality
  `not`. This *makes* soundness; it does not threaten it.
- **verified-θ as a type** — the GL reduct can only be *applied* once the G-SAT
  checker has produced a verified θ (the "naive AND of two gates" is made
  inexpressible). Undecided `open` atoms are Kleene-`undefined` → `Unknown`.
- **sort inference + `CanEq` typed equality** — the first-order fragment needs
  no annotations (constraint-gen + first-order unification over kernel `Type`);
  ambiguity is *rejected, not guessed*. Every surface `=` routes via a
  `CanEq[σ,τ]` instance to the right kernel equality (EUF / arith / convertibility)
  — killing the recurring EUF↔arith cross-sort bug class at elaboration time.

## 3. The closed-world vs constructive-kernel resolution

They do **not** unify. Same generate-and-check firewall as the SMT face,
specialized to answer sets:

- **The kernel certifies typing + POSITIVE derivations only.** A membership
  `p(c) ∈ M` is a constructive proof object (literal under the `Inductive`
  carrier). The kernel never derives `¬p(c)` from failure-to-prove.
- **An untrusted solver + a re-checkable stability gate** (`lfp`-of-reduct ⊳ θ)
  certify closed-world negation + stability. Negative information is a
  side-condition on the external model `M`, discharged by the gate, never a
  kernel theorem.
- **Clark completion is the only sanctioned closed-world step** into the kernel
  (an explicit iff-definition the face commits to, total + explicit ⇒ δ-sound).
- **The MVP sidesteps the tension entirely**: definite Datalog has no negation,
  so the least model *is* the stable model *is* the completion — all re-checkable
  by one fixpoint.

**Per-predicate carrier**: a predicate-as-atom is `postulate`d `Open` (truth
decided downstream); a positive *recursive* predicate lowers to `Inductive` (a
definite recursive predicate *is* an inductive relation — the strict-positivity
gate is a free well-foundedness proof); a non-recursive predicate gets a
`Def`-completion body over lower strata. No new `Modality` variant.

## 4. The abductive merge

- **abducible → `Open` atom with no completion clause** (solver-side metadata
  marks it as a projection target). Zero new kernel variant, zero gate change.
- **`abduce(P, A, G) ≡ answer_sets(P ∪ {choice A} ∪ {:- not G})` projected onto
  `A`, ⊆-minimized.** The completion-clause-present-vs-absent distinction *is*
  the entire encoding of "assumable".
- **One rule IR, two directions.** The abductive engine's `HornRule` /
  `SchematicHornRule` is re-homed here as the ASP rule type; `Solver` switches
  `SldEngine::new(&abducibles)` → `::with_all(&abducibles, &rules)`. SLD =
  goal-directed relevance grounder (front half); the new forward `lfp` =
  answer-set membership (back half). `minimize` / `rank` / `dedup` / cycle-guard
  reused verbatim. The SLD cycle-guard's "back at a goal I'm expanding" event
  *is* the positive-loop (SCC) discovery the L3 stability gate needs.
- The SMT-LIB `(abduce)` / `(get-abduct)` wire stays compatible (Verus / cvc5).

## 5. lu-kb

**lu-kb becomes the shared live KB substrate both halves read from** — `rule` /
`abduce` / `constraint` / `enum` / `data` as item kinds in one typed file (the
literal realization of "merge the abductive engine entirely"). The face's surface
is a **successor version of the current lu-kb grammar** (per the user). The MVP
fragment-restricts (admits `fact/rule/abduce/constraint/enum/data/sort/pred`,
rejects the larger lu-kb language — `relation/instance/fn`/HKT — with a typed
`Unsupported`; sound-by-omission). How much pulled-in sugar (`def rec` blocks,
comprehensions, AQL-style fuel bands) to surface is **a deeper discussion still
open**. (Runner-up role — lu-kb as the AOT-banked compiled-KB artifact — is
deferred.)

## 6. Cross-language feature menu (the "beyond plain typed-ASP" answer)

Highest-leverage picks (mined from AQL / SQL / Haskell / Scala 3), each paired
with a modality gate so the closed-world verdict is never silently weakened:

- **First-order matching over kernel datatypes** (Haskell ADT-match / Scala
  extractor) — the biggest expressiveness jump (flat tuples → structured
  inductive values), consumes idle kernel datatypes; `fix`-guard-gated. **In the
  MVP.**
- **`summon`-with-holes** unified abductive engine (Scala given-resolution) — a
  hole's expected sort pre-filters the `2^n` subset search; the derivation is a
  re-checkable `Derivation` inductive (a cert into `adsmt-cert`). Near-term.
- **Stratified aggregates + comprehension surface** (SQL `GROUP BY` / AQL
  `COLLECT`) — aggregate value = a LIA theory term = a second ASP⊕SMT seam.
  *Only* the non-recursive monotone slice. Near-term.
- **`def rec` named scoped recursion + AQL fuel band** (SQL `WITH RECURSIVE`) —
  bound-exhaustion → `Unknown`, never "no". Near-term.

Tempting-but-dangerous (deferred / hard-gated): choice/cardinality → multiple
stable models (enumerate or `Unknown`, never collapse — the pigeonhole honesty
lesson); recursive/non-monotone aggregates (the SQL-borrowed restrictions *are*
the sound slice); full dependent inference (undecidable → bidirectional only).

## 7. MVP (user decision A) and build order

**MVP = modality + verified-θ + CanEq + L1 theory interior + forward `lfp` +
definite abduction + first-order datatype matching.** Ship the one fragment
where soundness is unconditional.

The one genuinely new runtime primitive is **`program.rs`: a semi-naïve forward
Horn least-fixpoint evaluator** — it is the solver *and* the answer re-check gate
*and* the abductive forward-chainer. (The existing abductive SLD engine is
*backward* — wrong direction.) Everything else is *connection* (wire the dormant
rule base) and *reuse* (kernel admitters, the `Prop` gate, the `Modality` tags,
the abductive post-processing, OxiZ delegation).

**Build order**: (1) crate skeleton + the `lfp` primitive; (2) the
elaborator (sorts→`Inductive`, preds→`Open`, recursion→`Inductive`/non-rec→
`Def`-completion, rules→checked-`Prop` Π-implications, queries→checked-`Prop`
goals); (3) a finite grounder over `enum`/`data` → `GroundProgram` (abstain on
infinite domains); (4) the `lfp ⊳ θ` gate; (5) wire abduction for `?- abduce`;
(6) first-order matching. Then L2 → L4 → L5, with **L3 (the big lift: a
clasp-style unfounded-set propagator + a no-answer-set loop-formula certificate
checker — neither exists in the workspace yet; hard-gated, parses-but-abstains
until both land)** as the research-grade deliverable. Each slice strictly *grows
the checkable fragment*.

### Implementation status (landed, `main`)

Steps (1)–(6) are **landed end to end**, plus **L1 CanEq typed (dis)equality**,
**L2 stratified negation + integrity constraints**, the first **generous
Category-A surface sugars** (the lu-kb-successor parser, anonymous `_`, pooling
`;` + integer intervals `..` expanding a whole fact / rule / constraint over
their cartesian product, and body `let V = t` parse-time substitution), and the
**L3 first slice — bounded stable-model semantics**:

| Module | Covers |
|---|---|
| `lexer.rs` / `parser.rs` | the lu-kb-successor surface (recursive-descent, `MAX_DEPTH` guard); pooling / interval / anonymous-`_` desugaring |
| `ast.rs` | `Item` / `Atom` / `Term` / `Literal` (`Pos`/`Neg`/`Theory`) / `Expr` |
| `elab.rs` | declarations through checked admitters; rule Π-carriers; CanEq routing (`#int.*` / `#eq.S` / `#ne.S`); `#not`; `compute_strata` now a **classifier** (`Stratification::{Stratified, NonStratified}` — a negative cycle routes to L3 instead of erroring) |
| `program.rs` | the semi-naïve forward Horn **least-fixpoint** (solver + re-check gate + abductive forward-chainer); the **GL reduct + `is_stable` gate** (`GroundNProgram`), reusing the `lfp` verbatim |
| `solve.rs` | finite grounder + matching filter; theory/CanEq guard eval; **stratified perfect model** (L2) + the **bounded stable-model gate** (L3) — the **well-founded bracket** `L* ⊆ M ⊆ U*` (alternating fixpoint) narrows the guess to the undefined atoms, and **connected-component decomposition** solves independent loop-clusters separately and cartesian-combines (the splitting-theorem base case; improvement-only — taken only when the monolithic sweep is infeasible); query answering (membership / cautious `∩`); ⊆-minimal abduction |
| `lint.rs` | the **advisory unsoundness/vacuity linter** (a pure observer behind the firewall — no write path to a verdict): `asp-unsafe` / `asp-nonstratified` / `asp-vacuity` (the dual of the SMT-LIB vacuous-context lint), all `Info`/soft |

**Advisory linter (ASP face, `lint.rs`).** The unsoundness/vacuity linter
([the user-proposed feature] — a pre-catcher for unsound argumentation in
user/ITP input) is the **dual of the abductive surface**: abduction finds
hypotheses that *make* a goal hold; the linter finds when the program is
*self-defeating*. It is a **pure OBSERVER behind the soundness firewall** —
`lint(program)` runs the trusted `elaborate → solve` pipeline and reports
`AspDiagnostic`s on a side channel, with **no write path to a verdict** (a lint
bug yields only a missing/spurious advisory line). The ASP MVP rules are all
`Info`/soft (intentional vacuity — an over-tight constraint, a `requires
false`-style dead branch — is common, so the keystone is a neutral note, never a
hard "your program is broken" claim): `asp-unsafe` (surfaces the elaborator's
`FaceError::Unsafe`), `asp-nonstratified` (a negative cycle — stable-model
semantics, not the perfect model), and `asp-vacuity` (no answer set — the dual
of the SMT-LIB face's vacuous-context keystone). The SMT-LIB-side wire (the
`adsmt-lints` `DiagnosticsDocument`, the `--lint` / `(get-lints)` plumbing, and
the solve-based vacuity lint via `decide_fh`) is the next slice in the AD1
workspace; the whole feature is default-off and parallel to / independent of L3.

**L3 first slice (the GL reduct gate).** A non-stratified program (a negative
cycle) now *elaborates* and routes to a re-checkable stable-model gate that
**reuses the trusted `lfp` verbatim** — no new trusted fixpoint code:

- `GroundNProgram` (in `program.rs`) is a ground normal program that **retains
  each rule's negative body** (`{head, pos, neg}`) — the one piece of state the
  L2 grounder folds away. `reduct(M)` keeps each rule whose `neg ∩ M = ∅` and
  deletes its `not` literals (a positive `GroundProgram`); `is_stable(M) ≡
  reduct(M).least_model() == M` is the whole new trusted surface (a syntactic
  filter + the existing `lfp` + a `BTreeSet ==`).
- The **firewall is identical to abduction's**, lifted to whole-model equality:
  the candidate enumerator is *untrusted*; a bug can only propose a non-stable
  `M` (rejected — certification *is* the recompute) or skip one (a sound
  under-report), never certify a non-stable model.
- Enumeration is a **bounded guess-and-check** bracketed by `L ⊆ M ⊆ U`
  (`L = lfp(reduct(B))`, `U = lfp(reduct(∅))`, both via the trusted `lfp`;
  `B` = heads), gating each subset of the free atoms `U \ L` through `is_stable`
  then discarding constraint-violating answer sets. Two loud, sound abstains
  guard it — a grounding-count cap *during* the pass and a **work-aware**
  `2^|FREE| · |rules|` budget (a count-only cap on `|FREE|` would soft-hang on a
  large rule set) — never a hang, never a silent/partial "no answer set".
  Queries are answered **cautiously** (`∩` over the stable models); the full L3
  solver (clasp-style unfounded-set propagation + a loop-formula certificate,
  replacing the bounded sweep) is the next slice. Verified by a 70K-trial
  in-crate differential against exhaustive brute force over the whole Herbrand
  base (`solve.rs` `mod l3_tests`).

**L5 first slice (weak constraints, single-level).** `:~ B. [weight@level]`
(`ast::Item::WeakConstraint`, `lexer`/`parser`) elaborates through the SAME
body-check as an integrity constraint (`elab::Elaborator::check_constraint_body`,
extracted so neither duplicates the other's safety/scoping/theory-binding
checks) but is tagged with its `(weight, level)` and never joins the hard-
constraint set. `solve::solve_weak_optimal` does not add a new search
procedure: it reuses the SAME trusted, GL-reduct-gated candidate set `solve`
already enumerates (stratified ⇒ the one perfect model; non-stratified ⇒ every
constraint-consistent stable model) and picks the cost-minimal one(s) by plain
evaluation (`ground_weak_constraints` + `weak_cost`) — a full weight-aware
stable-model search is out of scope for this slice. Two design points were
resolved by consulting real ASP-Core-2/clingo semantics rather than guessing:

- **Polarity**: a weak constraint "costs" its weight when its body **holds**
  (ASP-Core-2's "violated" = "body holds", the dual reading of a strong
  constraint's body holding making the program inconsistent) — verified
  against clingo 5.8.0 (`a. :~ a. [1@0]` ⇒ optimal cost `1`).
- **Counting**: ASP-Core-2 identifies a ground weak-constraint instance by the
  tuple `(weight, level, terms)`; this surface has no `terms` clause, so
  `terms` is always empty, and instances sharing an identical `(weight,
  level)` pair — even from *different* weak-constraint declarations — are
  counted **once**, not summed. Re-verified three independent ways against
  clingo 5.8.0 (`solve.rs`'s L5 module comment has the exact programs/costs).
  A caller wanting independent counting must give each instance a distinct
  weight (clingo's `[w@l, terms…]` disambiguator is itself out of scope).

`adsmt-delegate::asp` (adsmt-delegate's `asp` feature) wraps this for external
callers, converting the `i64` cost into `oxiz-opt`'s own `Weight` type for
arithmetic-type parity with the rest of the delegation stack — without
re-invoking a MaxSAT solver (there is nothing left to search once the
candidate set is in hand). **Single-level-only**: a program mixing more than
one `level` value is refused (`FaceError::Unsupported`), not approximated.
Aggregates and full lexicographic multi-level stratification remain
unimplemented (the rest of L5).

Pending: **the full L3 stable-model solver** (the unfounded-set propagator + the
loop-formula certificate checker, lifting the work-budget abstain); **brave**
queries; **L4** choice / disjunctive heads; the **rest of L5** — aggregates and
full lexicographic multi-level weak constraints (see the post-L3 feature
decisions: stratified `#count`/`#sum`/`#min`/`#max`, `#avg`, pluggable-metric
Fréchet medoid/variance over a finite group; weighted-abduction MPE;
module/import reuse). **Non-ground abductive
goals** (`?- abduce p(X)`, enumerated per binding) and the **native backward-SLD
relevance grounder** (the adsmt-abduce algorithm ported onto the face's own u32
ground atom ids — no `adsmt-core` dependency — replacing the bounded exhaustive
subset search, re-verified by the forward gate) are landed. (`def rec` + fuel and
comprehensions do not fit the finite, no-term-growth universe / are
L5-aggregate-coupled, so they fold into later work.)

## 8. Soundness firewall (preserved)

Every returned answer/explanation is independently re-checked by recomputing
`lfp` + confirming membership (and, for L3, by recomputing the GL reduct's least
model and the exact-equality gate); the kernel re-checks types. A buggy grounder
or heuristic can only **shrink** the answer set or yield `Unknown` / `FaceError`
— never manufacture a false entailment or a false answer set. A L3 **"no answer
set"** verdict is now *sound within the bound*: the bracketed sweep is exhaustive
over `L ⊆ M ⊆ U` (which provably contains every stable model) and re-checkable by
re-running — so the empty result is a genuine refutation, not an abstain. Beyond
the work budget it abstains **loudly** (`FaceError::Unsupported`), never a partial
"these are the answer sets". Sound-by-omission abstain boundary: NAF over an
`open` predicate / disjunction / aggregates / unsafe rules (unbound vars) /
**infinite domains** (partial grounding drops instances = soundness-fatal) /
**stable-model search past the work budget** (the unfounded-set + loop-formula
checker is a later slice) → `FaceError` or `Unknown`, **never** approximate. The
elaborator either fully elaborates a construct (kernel + gate re-check it) or
refuses the whole program — the IR-level instance of "dropping a constraint
preserves `Unsat` but destroys `Sat`".

## 9. Release

User decision D: this whole face is **in the v1.0.0 cut** (even at large plan
change); develop on the `main` branch only for the time being. Overrides the
pre-stable feature freeze for this feature.
