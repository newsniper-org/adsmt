# adsmt-ir — the typed CIC kernel IR

The **language-agnostic core lingua franca** of adsmt's multi-paradigm
substrate. This document pins the kernel's design and its roadmap.

## 0. Where this sits

```
  surface syntax  ──parse──▶  surface AST  ──elaborate+typecheck──▶  ┌──────────────┐
   · SMT-LIB-3.0 face                                                │  CIC kernel  │  ← THIS CRATE
   · typed Datalog/ASP face                                         │     IR       │
   · unified superset interior                                      └──────┬───────┘
                                                                           │ lower
                                                                           ▼
                                              solver working rep (adsmt-core Term + clauses + propagators)
                                                       on the one CDCL(T)/MCSAT trail
```

The kernel is the typed form **before** recursion / definitions / higher-
order structure are flattened into quantified axioms. That flattening is
exactly what plain SMT-LIB throws away — and the lost structure is the
source of the MBQI / trigger instantiation hell the verus backend fights.
Keeping it in the IR is the whole reason the multi-paradigm superset is a
*strictly better IR* for all three co-#1 use cases (verus, Verilog,
Sledgehammer). See the memory topic `multi-paradigm-hybridization` and
`AD1/docs/design/UNIFIED_VERIFICATION_GATE.md`.

This crate is the **trusted core**: small, dependency-free, auditable. The
type checker is the IR-level instance of the project's verdict-
verification gate — an unverifiable term is *rejected* (⇒ `Unknown`
downstream), never silently trusted. The prime directive (`FALSE_UNSAT=0`,
`FALSE_SAT=0`) is upheld here as **subject reduction**: a term the checker
accepts is well-typed, so its lowering cannot manufacture a wrong verdict.

## 1. Why CIC, why these sorts

SMT-LIB 3.0 (preliminary) is *already* a CIC-inspired dependent, higher-
order, typed λ-calculus: kinds give HKT for free (`List : Type → Type`),
sorts are dependent (`BitVec n`), everything is a term (a formula is a
`Bool` term, a quantifier is a higher-order function), and it has modules
and `define-const-rec` + datatypes/recursors. Adopting its kernel
*subsumes* the HKT / higher-order requirements of the unified surface
language. So the kernel is the **λΠ core of CIC**:

- **`Prop`** — impredicative. Every paradigm's *propositions* live here:
  SMT-LIB `Bool`, ASP atoms, CP literals. Impredicativity is what lets a
  quantifier be an ordinary `Π` term (`∀x:A. P x : Prop` for *any* `A`,
  even `A : Type`) — the "formula = Bool term, quantifier = HO function"
  shape.
- **`Type(n)`** — a predicative tower; `Type(0)` is the data universe
  (where `Nat`, `BitVec 8`, user datatypes live).

Sort typing: `Prop : Type(0)`, `Type(n) : Type(n+1)`.

Product rule (`Π(_:A). B`, with `A : s1`, `B : s2`):

| `s1` \ `s2` | `Prop`  | `Type(j)`        |
|-------------|---------|------------------|
| `Prop`      | `Prop`  | `Type(j)`        |
| `Type(i)`   | `Prop`  | `Type(max i j)`  |

The `Prop` column is impredicative (any product *into* a proposition is a
proposition); the `Type` column is the predicative `max`.

## 2. The def / open modality — the multi-paradigm hook

A global declaration carries a `Modality`:

- **`Def(body)`** — the surface `def`. A **closed-world** definition that
  **δ-unfolds** during conversion: the constant *is* its body. Ownership
  tag for defined / inductive / ASP atoms (rule-defined, least-model
  semantics downstream).
- **`Open`** — the surface `open`. A **classical / theory** parameter,
  **opaque** to the kernel (never δ-unfolds), because its meaning comes
  from the theory or the open-world reading, not from a definition.
  Ownership tag for theory atoms / uninterpreted symbols.

Reduction reads this flag, so convertibility — hence type-checking — is
modality-aware. **Paradigm ownership is structural in the kernel**, not a
side table the lowering has to re-derive. This is the kernel-level seed of
the trail/explain ownership the Unified Gate relies on (`def` atoms get
the stable-model gate; `open` atoms get the theory/G-SAT gate).

## 3. M1 — the dependent λΠ core (this crate)

Grammar (`term.rs`), de Bruijn-indexed and nameless so α-equivalence is
structural `==`:

```
t, A, B ::= Sort(u)            -- a universe as a term
          | Bound(k)           -- de Bruijn index, 0 = innermost
          | Const(c)           -- global reference, resolved in Env
          | App(t, t)          -- application
          | Lam(A, t)          -- λ(_:A). t
          | Pi(A, B)           -- Π(_:A). B   (A → B when B ignores the binder)
          | Let(A, t, t)       -- let _ : A := t in t
u       ::= Prop | Type(n)
```

- **Substitution** (`term.rs`): `shift` (lift free indices) and `inst`
  (β/ζ instantiation with correct decrement + lifting under crossed
  binders). `subst_top(body, arg)` is the workhorse.
- **Reduction** (`reduce.rs`): `whnf` does β (apply a λ), ζ (unfold a
  `let`), and head-δ (unfold a `def` const; never an `open` one).
  Termination of head-δ in M1: `def` bodies are non-recursive (admission
  checks the body *before* the constant is inserted, so it cannot mention
  itself); recursion arrives with guarded `fix` in M2.
- **Convertibility** (`reduce.rs`): `is_def_eq` compares WHNFs
  congruently. After WHNF a `def` const can never be at the head, so a
  surviving `Const` is `open`/unknown and compares by name — the opaque,
  theory-owned reading.
- **Bidirectional checker** (`check.rs`): `infer` / `check` /
  `infer_univ`, with `define` / `postulate` as the **checked admitters**
  (nothing reaches the `Env` unchecked). Typing rules are the standard PTS
  ones; `Let` is typed as `(λ(_:A). body) val` so the let-value flows into
  the result type.

Conformance tests (`tests/kernel.rs`, 12): sort typing, polymorphic
identity, applied identity, the arrow helper, `def` δ-unfolding, `open`
opacity, the impredicative-`Prop`/predicative-`Type` contrast, dependent
codomain substitution, and **four rejection paths** (non-function
application, type mismatch, ill-typed `def`, unbound index) — the gate
must say *no*.

## 4. M2 — inductive types, constructors, recursors ✅ (landed)

The datatype / ASP-rule layer and the "preserves recursion" payoff. What
landed (`inductive.rs`, `env.rs`, the `Term::Elim` primitive):

- **`Inductive`** declaration ([`declare_inductive`]): a parameter
  telescope, a result sort, and constructors (each an argument telescope
  that may reference the inductive). Covers **parameterized, non-indexed**
  inductives — `Nat`, `Bool`, `List A`, `Tree A`, records, enums, the
  verus `Range` / `Layout` field-bearing datatypes. *Indices* (GADTs,
  `Vec n`, equality) are the next frontier (M2.5).
- **Strict positivity check** — each constructor argument is either
  *recursive* (exactly `I params`) or must not mention `I` at all;
  anything else is *rejected* (`NonPositive`). Conservative-reject is
  sound: a rejected inductive ⇒ `Unknown`, never an inconsistent kernel.
- **Dependent recursor as a kernel primitive** — `Term::Elim(ind, motive,
  minors, major)`, *not* a generated constant. This is how a dependent
  eliminator is expressed **without universe polymorphism**: a typing rule
  (`method_type` builds each minor-premise type, parameters recovered from
  the major) plus ι-reduction in `whnf`
  (`ind.rec P m… (c_j P b…) ⟶ m_j b… (ind.rec P m… b_recᵢ)…`). Resolves
  the "generate vs. primitive" question in favor of the smaller trusted
  surface.
- **Prop large-elimination guard** — eliminating an impredicative-`Prop`
  inductive into `Type` is *rejected*; this is exactly the restriction
  that keeps impredicative `Prop` consistent (Prop + large-elim is the
  known inconsistency). We forgo the singleton/empty exception — a
  completeness loss, never a soundness one.

Tests (`tests/inductive.rs`, 9): `Nat`/`List`/`Bool` constructors + `add`
/ `length` / `ite` by recursion (ι), a dependent eliminator
(`P : Nat → Type`), and four rejection paths (non-positivity, large
Prop-elim, wrong minor count, ex-falso into Prop from the empty inductive).

### M2.5 — indices (GADTs) ✅ (landed)

Inductives gain an **index telescope** ([`declare_inductive_indexed`];
`declare_inductive` is the non-indexed shorthand). Parameters stay uniform;
indices may vary per constructor — `Vec (A:Type0) : Nat → Type0` with
`vnil : Vec A 0`, `vcons : Π(n). A → Vec A n → Vec A (S n)`.

The dependent recursor generalizes: the motive is
`Π(indices). I params indices → Sort`, the result is `motive indices major`
(indices recovered from the major's type), and each recursive argument's IH
is taken at *its own* indices. The construction that keeps this sound and
auditable: each constructor's dependent **method type is built once at
admission as a template** `Π params. Π(motive). MethodType` — all de Bruijn
shifting done a single time, in one uniform context (parameters and motive
as binders) — and `method_type` just *instantiates* it by substitution at
elimination time. ι-reduction is unchanged (indices never appear in a
constructor value, only in its type). Tests (`tests/indexed.rs`, 5):
`Vec` constructors, `vlen` by index-family recursion, a truly dependent
result type (`P : Π(n). Vec Nat n → Type`), the non-indexed path still
working, and a wrong-index-arity motive rejected.

### M2.6 — guarded `fix`, `Match`, mutual induction ✅ (landed)

- **`Match`** (`Term::Match`) — non-recursive case analysis: the recursor
  without induction hypotheses (a per-constructor *match template*, the
  method template with `rec_positions = []`). The case principle a `Fix`
  destructures with, so the only recursion is the explicit, guarded
  self-call.
- **Guarded `fix`** (`Term::Fix { rec_arg, ty, body }`) — μ-reduces only
  when applied with its `rec_arg` in constructor form (whnf gained spine
  collection for this). Admission runs the **structural-decrease guard**
  (`guard.rs`): `f` may be called only as a fully-applied head whose
  `rec_arg`-th argument is a variable that is a *strict structural subterm*
  of the recursive argument (one exposed by a `Match`/`Elim` on it or on an
  already-smaller variable). The guard is **deliberately conservative** —
  it rejects anything it cannot prove decreasing. This is the only safe
  direction: a too-lenient guard would admit a non-terminating term, which
  inhabits every type ⇒ a `False`-proof ⇒ the prime-directive violation.
  Tests cover `plus`/`length` computing and four rejection paths
  (self-call on the same argument, call on a non-subterm, too few
  abstractions, non-inductive recursive argument).
- **Mutual induction** (`declare_mutual` over `MutualMember`s) —
  simultaneous declaration: every type former is registered first, so
  constructors may cross-reference (`Tree`/`Forest`, `Even`/`Odd`).
  Positivity is checked over the whole group (a self-recursive argument
  gets an IH; a cross-reference to another member at the argument's head is
  allowed with **no** IH; any group member elsewhere is rejected). The
  recursors are **independent** (not yet mutual) — sound, with mutual
  recursors a later completeness step.

### M2.7 — mutual recursors ✅ (landed)

A true **mutual recursor** `Term::MutElim(member, motives, minors, major)`: a
`g`-tuple of motives (one per group member), one method per constructor of
*every* member, where a recursive argument of type `I_b` gets an IH at `P_b`
and ι dispatches the sub-call to member `b`'s recursor. The mutual method
type is built once at admission (`build_mut_method_template` — the single-
motive de Bruijn arithmetic generalized to a `g`-wide motive block, conclusion
at `P_{self_b}`, each IH at `P_{rec_member[t]}`); `infer_mut_eliminator`
enforces a shared param telescope (R1), validates every motive at one
elimination universe (R3), and applies the Prop large-elimination guard **per
member** (reject if any group member is `Prop` and the elim sort is `Type`).
`iota_mutelim` dispatches each recursive sub-call to `group[rec_member[t]]`'s
recursor. Restrictions R1–R5 are each sound-by-restriction (DESIGN: shared
params, direct self/cross recursive args only, single elim universe, union
Prop guard, full motive/minor tuple). Tests (`tests/mutual.rs` +5): a tree-
size mutual recursor computing across members (the cross-member IH the
independent recursor cannot express), `Even`/`Odd` indexed Prop small-elim,
and rejections for differing params, large-elim from a Prop member, and a
wrong minor count. The implementation was **adversarially re-reviewed** (4
skeptics, traced probes against the real kernel): 0 soundness holes on the
P0-1/P0-2/P0-3 vectors.

### 후검증 — the kernel metatheory in Verus

The kernel's metatheory is pre-verified in the standalone
[`../adsmt-ir-verification`](../adsmt-ir-verification) (Verus, 38 verified, 5
modules) in the same firewall style as `unified-gate-verification`: **subject
reduction** (type preservation as the congruence-closure of the per-rule
facts; conversion respects typing), **`fix` termination** (the guard admits
only strict-subterm calls ⇒ a strictly-decreasing `nat` measure ⇒ no infinite
descent ⇒ no `False`), **recursor ι-preservation** (discharges the `pres_iota`
hypothesis), and **positivity ⇒ well-founded + mutual independence**. Together:
subject reduction + strong normalization of the accepted fragment — the
metatheory behind `FALSE_UNSAT=0 / FALSE_SAT=0` at the IR.

### M2.8 — guard `let`-aliasing ✅ (landed)

The first *less-conservative guard* slice, chosen by a 4-perspective design/
soundness-assessment workflow as the **one confidently-sound, small,
후검증-able** M2.8 change (the rest deferred — below). `guard.rs`'s `Let` arm
now tracks a **ζ-alias**: `let y := <strict-subterm var> in … f y …` makes `y`
a recognized strict subterm (it ζ-reduces to the subterm *before* μ inspects
the recursive argument, so `f y` reduces identically to `f j`). This only
*grows the recognized-subterm set with an alias of an already-smaller var* —
never `x` itself, never a non-variable — so the call-acceptance rule is
unchanged and over-acceptance is structurally impossible. Tests
(`tests/recursion.rs` +3): a `fix` recursing on a let-bound predecessor now
type-checks and computes; let-aliasing the recursive argument, or a
constructor application (a superterm), are still rejected. 후검증:
`guard_wf::zeta_alias_preserves_subterm` (a ζ-alias of a subterm is a subterm,
so the new `admits` clause stays inside `admits ⟹ subterm`).

### M2.8+ — higher-order / function-typed recursive arguments ✅ (landed)

A constructor argument `Π(z:D). I params idx` with every domain `D`
group-member-free (the inductive **only in the codomain** — the strict-
positive W-type shape) is admitted with a **functorial** induction hypothesis
`Π(z:D'). motive idx' (a_r z)`, and ι threads the recursor *through* the
function: `ind.rec P m… (c … g) ⟶ m… (λz. ind.rec P m… (g z)) …`. The flat
`motive a_r` (a motive applied to a *function*) is the P1-3 ill-typing
landmine; the functorial Π is the only sound form.

- `process_constructor` peels `q` leading function domains (`peel_all_pis`),
  requires them group-free (`domains_clean` — a domain occurrence is a
  *negative* position ⇒ rejected, e.g. `(Bad→Bad)→Bad`), and checks the body
  is a group member at the uniform params with offset `j + q` (params sit
  under `q` extra binders — the soundness-critical de Bruijn point).
- A shared `build_functorial_ih` builds the IH for both templates (motive at
  `+q` depth, value `a_r` applied to the `q` fresh `z`s, domains shifted with
  cutoff `j`/`q`; mutual adds the `g`-block offset). **`q = 0` collapses
  EXACTLY to the first-order code** — the prior tests are the safety net.
- `reduce.rs`: `constructor_split` recovers the params; `rec_subcall` builds
  `λz. Elim(…, (g z))` (lifting motive/minors past the `q` λs). `whnf` does
  **not** reduce under the λ, so the inner recursor fires only when later
  applied, on the structurally smaller `g z` — **termination holds** (the
  W-type argument; the adversarial review confirmed a `fix self := λz. node
  self` infinite-tree generator is rejected by the guard).

Tests (`tests/higher_order.rs`, 3): `Inf` (`node : (Nat→Inf)→Inf`), a depth
recursor computing `0/1/2` via the threaded recursion, and rejection of a
negative function domain. **Adversarially re-reviewed** (4 skeptics, traced
probes): **0 soundness holes** — functorial IH correct (flat-IH rejected 3
ways, `j+q` param-smuggle rejected), ι terminates (no reduce-under-λ, 30-level
tree computes fast), strict positivity rejects every negative domain, mutual/
indexed interactions sound. 후검증:
`positivity_mutual::ho_rec_is_positive_and_wellfounded` +
`eliminator::functorial_ih_uses_genuine_value`. Nested *containers*
(`Rose : List (Tree A) → Tree A`) stay **rejected** (need the container's
functorial map — below).

### M2.8+ — still-deferred frontier (re-reviewed every task from M3 on)

> **Process rule (user):** from M3 onward, **re-review at every task** whether
> these remain deferred — a surface face or the lowering may make one
> tractable/needed; if so, un-defer it via the design → implement →
> adversarial-review → 후검증 pipeline. Deferral is re-evaluated continuously.

- **Nested recursive containers** (`Rose : List (Tree A) → Tree A`) — need the
  container's functorial `map`/`All` (a functor registry + nested-recursion
  ι); the group member nests inside a foreign inductive's parameter.
- **Mutual `fix`** — a block of mutually-recursive functions; the valuable
  cross-call form needs a lexicographic / shared structural measure (a single
  per-function measure is unsound for `f_i` calling `f_j`).
- **Heterogeneous-universe mutual elimination (relax R3)** — **cannot be made
  sound without the cumulativity / product reasoning the kernel deliberately
  omits** (the cross-member IH transport is exactly a `Sort(U_b) →
  Sort(U_self)` coercion). R3 stays verbatim (sound-by-restriction,
  already 후검증'd); do not touch until a cumulativity milestone exists.

## 5. M3 — faces, lowering, 선검증

- **AOT-bank** ✅ (M3-1, landed) — the checked-`Env` **admission journal**
  (`bank.rs`, `bank_encode`/`bank_decode`): bake a prelude once, reload it by
  *re-admission*, check only the query delta. Sound by construction (load =
  re-checking); see §8. The cross-hybridization AOT directive, realized at the
  IR. **Design-reviewed** (the "trust serialized state + digest" alternative
  was found fatally unsound → the journal design) and **adversarially
  re-reviewed** (4 lenses, probes against the real bank): **0 soundness holes**
  — 14/14 wrong-acceptance attacks (ill-typed `def`, non-terminating `fix`,
  non-positive inductive, duplicate/forward-reference, Prop large-elim,
  inhabit-`Empty`) correctly rejected on replay — plus one *totality* fix: a
  forged `Fix.rec_arg` reached `peel_pis`'s speculative `Vec::with_capacity`
  (a pre-existing kernel crash on malformed input, **not** a wrong verdict),
  now bounded + overflow-guarded. The standing **M2.8+ re-review** (below) was
  applied: no deferred item (nested containers, mutual `fix`, relax-R3) is
  needed — the bank serializes the *admissible set*, it does not widen it.
- **Faces**: an SMT-LIB-3.0 elaborator and a typed-Datalog/ASP elaborator,
  each a *1:1 subset* of the unified surface; the organic ASP⊕SMT
  cooperation lives in the **superset interior** (mixed sentences neither
  face expresses), elaborating to the same kernel. The **SMT-LIB-3.0 face
  slice 1** ✅ (M3-4) is landed in the sibling crate `adsmt-ir-smtlib` (a
  *frontend*, not the trusted core — everything it elaborates is re-checked by
  the kernel admitters, so a face bug can only be *rejected*, never trusted):
  `Bool` ↦ `Prop`, the connectives an `open` prelude, `=>` ↦ the arrow,
  `forall` ↦ `Π`; `declare-sort`/`declare-const`/`declare-fun`/`assert` →
  a checked `Env` + `Prop` goals. (`define-fun`/datatypes/arith/`ite`/`let` =
  later slices, rejected sound-by-omission.)
- **Lowering**: kernel → adsmt-core working rep. `def` atoms route to the
  stable-model / least-fixpoint side of the Unified Gate; `open` atoms to
  the theory / G-SAT side. Quantifier `Π`-into-`Prop` lowers to the
  solver's quantifier handling *with the definitional structure intact*
  (the anti-trigger-hell win). **The concrete design is §5.1 below.**
- **선검증**: the kernel's metatheory (subject reduction / progress, and
  the positivity ⇒ consistency argument) is the Verus 선검증 target —
  alongside `unified-gate-verification` and `oxiz-nl2-verification`, the
  same `[선검증 → 구현 → 후검증]` discipline.

### 5.1 Lowering — the concrete design (kernel CIC → adsmt-core HOL)

The pipeline-closing step: translate a checked kernel `Env` + its `Prop` goals
(a face's `Elaborated`) **down** into what the solver consumes — adsmt-core
`Term`s of sort `Bool`, plus the datatype/symbol declarations they need —
then `Solver::assert` + `check_sat`.

**Source** (`TermKind`): `Sort(Univ)` · `Bound(usize)` · `Const(String)` ·
`App` · `Lam(dom,body)` · `Pi(dom,cod)` · `Let(ty,val,body)` ·
`Elim`/`Match`/`Fix`/`MutElim`. **Target** (`adsmt_core`): a *simply-typed*
HOL term `Var | Const | App | Lam` (named vars, hash-consed, type-checked at
construction) over a stratified `Type` (`Var | Const | App` + a `Kind` tower
for HKT), with `Bool` and `->` built in, `mk_forall`/`mk_exists` as HOL
constants, and native datatypes via the adsmt-engine `Datatypes` theory
(`DatatypeDecl` → `declare_datatype`). adsmt-core has **no de Bruijn** (named
+ capture-aware `subst`), **no dependent types**, and **no definitional
layer** (no `def`/`let`).

**THE PRIME DIRECTIVE AT LOWERING — abstain, never mislead.** Lowering is a
*partial* function. On any source construct with **no faithful simply-typed-HOL
image** it returns `Unlowerable`; it must **never** emit a target term whose
denotation differs from the source's. A faithful image preserves truth-value;
an abstention degrades to `Unknown` (sound); a *wrong* image is FALSE_SAT /
FALSE_UNSAT. Lowering sits **downstream of the kernel's checked admitters** —
so it may *assume* its input is well-typed and (for `Fix`) terminating; the
후검증'd guard is exactly what licenses the recursion-axiom form below.

**Type/term stratification.** CIC conflates types and terms (a `Pi` is both);
adsmt-core stratifies them. Lowering classifies each kernel term by its typing
level: type `Prop` → a target **`Bool` formula**; type a lowerable sort `A*`
→ a target **element** of `A*`; the term *is* a type (its type is a `Sort`) →
a target **`Type`**; anything else (a genuinely dependent function, a proof
used as data, a type that depends on a term value) → **abstain**.

**Per-construct map (the lowerable fragment):**

- `Sort(Prop)` → the target type `Bool`. `Sort(Type i)` is a classifier, not a
  lowerable *term* → abstain as a term (it appears only as the kind of a sort
  declaration).
- `Const(c)` by modality (`Env` lookup): **`open c : A`** → the **same target
  leaf the native SMT-LIB parser (`convert_symbol`) produces**, so the
  verdict-differential agrees: a **numeric literal** (a digit-leading name —
  SMT-LIB simple symbols cannot start with a digit, so this never misfires) or a
  datatype **constructor** is a `Const(c, A*)`; every **other** declared `open`
  symbol is a free **`Var(c, A*)`**. The `Var` is **load-bearing**: the arith
  theory's `LinArith::parse_comparison` claims `(< x k)` only when `x` is a
  `Var`, so a declared arithmetic operand must lower to `Var` (a `Const` leaves
  its comparisons uninterpreted → a sound but useless `Unknown`); EUF is
  indifferent (congruence handles either). *Except* the known prelude names map
  to built-ins — `true`/`false`→`Bool` consts, `not`/`and`/`or`/`=>`→ the Bool
  connectives, `=`→ equality, `exists`/`forall`→ `mk_exists`/`mk_forall`,
  `ite`→ the if-then-else, **and the `theory` prelude's `Int.*`/`Real.*`
  operators → the adsmt-core arith-theory operators
  (`+`/`-`/`*`/`div`/`mod`/`/`/`<`/`<=`/`>`/`>=`, unary `-` as `(- 0 x)`, `abs`)
  so the engine's LIA/LRA decides them** (the `Nat`/`WNat` injections, `int2real`,
  and `pow`/`odd`/`prime` stay uninterpreted EUF — sound, incomplete; a later
  slice). **Ground integer arithmetic is constant-folded** (`(+ 2 1)`↦`3`,
  `(= 4 3)`↦`false`, `(< 4 3)`↦`false`, unary `(- 0 2)`↦`-2`): the bare engine
  merges two distinct integer-literal `Const`s in UF (no built-in `4 ≠ 3` —
  `LinArith::assert` `Ignored`s a lit-vs-lit `=`), so the lowering DECIDES a
  literal (dis)equality / comparison itself rather than hand the engine an atom
  it closes unsoundly (the `4 ≠ 3` false-`sat` the #317 three-way differential
  found). This replicates, soundly, the text preprocessing the native CLI does
  but the lowering path bypasses — it only ever replaces an under-determined
  atom with its true value (overflow / `div`/`mod` / Real abstain to the plain
  term). **Dispatch on the resolved decl's identity + prelude
  type, NOT the bare string** (a user `(declare-fun and …)` / a bound var named
  `and` must not be mis-routed), **arity-exactly** (a *partial* application —
  `(and p)`, `(= S)` — abstains, never builds an under-applied target). The
  polymorphic ops carry a leading explicit **`Type0` argument** (`(= S a b)`,
  `(exists S (λ. ·))`, `(ite S c a b)`): for `=`/`ite` it is **dropped** (it is a
  type, not an operand — lowering it as a *term* is the off-by-one that compares
  a type to a value); for `exists`/`forall` it is **consumed as the binder's
  sort**; and that sort must be **first-order data or `Bool`** — a `=`/`exists`/
  `ite` over a *function*- or `Prop`-valued sort (extensional/predicate equality
  the solver cannot do) → **abstain**. **`def c := body`**: non-recursive →
  either δ-unfold inline (sound **only if EVERY occurrence is unfolded** — a
  partial unfold decouples `c`'s readings) or, preferred, declare `c` as a
  target `Const` **and assert `∀x⃗. c x⃗ = body*` once — but ONLY when `body*`
  lowered with ZERO abstains and all arg/result sorts are first-order** (an
  added equation can only make the system *more* unsatisfiable, so a mis-lowered
  `body*` is a direct FALSE_UNSAT; thread a per-axiom fully-faithful flag into
  the whole-query abstain). All-or-nothing **per constant** (inline-everywhere
  XOR axiom-everywhere). Routes to the stable-model / Clark-completion side of
  the Unified Gate. `Inductive` / `Constructor` consts → the datatype's target
  symbols (below).
- `Bound(i)` → the named target `Var` that de Bruijn index `i` resolves to in
  the lowering's **name environment** (a stack of fresh `Var`s pushed per
  binder; `Bound(0)` = innermost = top). **Names must be GLOBALLY fresh (a
  monotonic counter across the whole query), NOT merely in-scope-unique** — the
  target hash-conses a `Var` by `(name, ty)`, so two distinct kernel binders
  that happened to share a name+sort (nested shadowing, or two sibling
  assertions both using `x:Int`) would alias onto **one** `Arc<Var>` and
  `mk_forall` would *capture* across them (FALSE verdict). This is
  [[feedback_hashcons_hot_paths]]'s aliasing hazard in mirror (cf. the rc.29
  content-named-not-counter'd lesson): for *distinct* binders you need
  *guaranteed-distinct* names. Target `subst` is capture-aware, but only *given*
  distinct `Var`s.
- `App(f,a)` → `Term::app(f*, a*)` for an ordinary function/predicate head
  (the target type-checks the application at construction — a mis-lowering is
  *rejected*, defense-in-depth, never silently accepted). A connective /
  quantifier / equality head is dispatched specially.
- `Lam(dom,body)` is faithful **only** in a quantifier-argument or
  defined-function-body position; a free-standing λ of function sort used as
  *data* (extensional reasoning the solver can't do) → abstain.
- `Pi(dom,cod)` — four cases by what `dom`/`cod` are:
  1. `cod : Prop`, `dom : A*` a lowerable sort → the **quantified formula**
     `mk_forall(x:A*, cod*)` (the `Π`-into-`Prop` = the anti-trigger-hell
     `forall`, body lowered with structure intact);
  2. `cod : Prop`, `dom : Prop`, `dom` unused → the **implication**
     `(=> dom* cod*)`;
  3. `cod` a sort, `dom` a sort, `cod` does *not* mention the bound var → a
     target **function type** `Type::fun(dom*, cod*)` (a symbol's signature);
  4. `cod` genuinely depends on the bound **value** (true dependency) → no
     simply-typed image → **abstain**.
- `Let(ty,val,body)` → ζ-inline: `body*[x ↦ val*]` (the target has no `let`;
  inlining is the faithful image; a `Const`+axiom is the sharing-preserving
  alternative).
- `Match(ind,P,minors,major)` → a nested `ite`/tester/selector chain
  `ite (is-C₀ major*) minor₀*[fields ↦ selectors] (ite (is-C₁ …) … )` — **but
  only for a FINITE/enum datatype, and even then the missing-closure axioms must
  be emitted; for an inductive (ω) datatype → abstain.** The engine's
  `Datatypes` theory supplies disjointness + injectivity + selector reduction
  but **NOT exhaustiveness and NOT acyclicity** (the tester `is-C(x)` stays
  *uninterpreted* on a variable `x`). So on a junk model the unguarded chain
  returns the *last* branch unconditionally (FALSE_SAT), and the total `ite`
  diverges from the kernel's *stuck* `Match` on a non-ctor major (FALSE_UNSAT
  vs injectivity). Required: (i) restrict to finite/enum majors; (ii) assert the
  **coverage disjunction** `⋁ᵢ is-Cᵢ(major)` (and guard the *final* branch with
  its own `is-Cₙ`, not a bare else); (iii) a **dependent** motive (branch sorts
  differ) → abstain. A non-dependent motive is necessary (well-typed `ite`) but
  **not sufficient** — the datatype-closure condition is the real one.
- `Elim` / `MutElim` (recursors / induction principles) → **abstain**: a
  general recursor is a second-order object with no first-order datatype-theory
  image. The `Datatypes` theory supplies injectivity / disjointness / selector
  reduction automatically — that is the solver's induction-*free* reasoning;
  the kernel's structural induction does not lower.
- `Fix` (a guarded recursive function) → the **recursion-axiom form**: declare
  a target `Const` and assert its defining equations as `∀`-axioms (the
  recursive case of the `def` handling). The kernel's termination guard makes
  the *kernel's* `f x⃗` convertible to `body`, but a **total HOL equation
  `∀x⃗. f x⃗ = body*` is only sound when the datatype theory is an INITIAL
  ALGEBRA** (closed under exhaustiveness + acyclicity) — which the engine is not
  (same gap as `Match`). On a non-standard model (a junk element the solver
  permits because it never asserts induction) the total equation can manufacture
  either verdict. **Abstain — and the reason is "unsound without an
  initial-algebra datatype theory," NOT merely "awaiting a `define-fun-rec`
  face."** (Inlining a recursive `def` also does not terminate, confirming the
  abstain.)

**Inductive *declarations* (not terms):** a registered kernel `Inductive` /
mutual group → one adsmt-engine `DatatypeDecl` per type (sort name +
constructors + arities + selectors from the ctor telescopes). Lowerable when
**non-indexed** (adsmt-core datatypes carry params but **no GADT indices**) and
every ctor field sort lowers to a first-order target sort. Indexed inductives
(GADTs) → abstain. The **M3-7a monomorphized** datatypes are non-indexed mutual
members → they *declare* cleanly, but a `Match`/recursor *over* them is only
lowerable in the finite/enum case (the closure gap above) — an arity-bearing
recursive member declares but does not support a faithful `Match`. *Coordination
point (a SOUNDNESS one):* the face currently drops selector names (M3-6/7a), so
lowering must either synthesize selectors whose names **match what the
`Match`-chain emits** (else selector reduction silently never fires → §`Match`
hole) or the face is extended to carry them.

**Whole-query, all-or-nothing (the soundness keystone).** Lowering is a
*verdict-affecting* transform: `unsat` on the lowered images means
`G* ⊢ false`, which implies the real `G ⊢ false` only if every asserted image
is meaning-preserving **and no goal that mattered was dropped**. Dropping an
assertion can flip `sat → unsat` (unsound); weakening one can flip
`unsat → sat`. The only regime sound for *both* verdicts at once: **if any
goal or declaration in the query has an unlowerable subterm, abstain on the
WHOLE query** (report `Unknown`) — never assert a strict subset. This is the
IR-level instance of [[feedback_soundness_opaque_fallback]] (dropping a
constraint preserves `Unsat` but destroys `Sat`, so a dropped/abstained goal
must downgrade the verdict, never silently `sat`) and mirrors the face's
whole-goal rejection. Partial lowering is forbidden.

**"Structural success ≠ faithfulness" — the enumerated abstain checklist.** The
keystone above only fires when lowering *raises* `Unlowerable`. The dangerous
class is a term that lowers *without error* to a well-typed but meaning-WRONG
target term (no abstain triggers). An adversarial design review found four such
P0 sites (folded into the per-construct rules above) plus these that must each
carry an explicit abstain:

- **Proof-as-data.** A binder whose domain has sort `Prop` is a *proof*
  variable, not a Bool value. `Π(h:P). Q` with `h` **used** in `Q` (a dependent
  proof term) is neither `Pi` case 1 nor the unused-case implication → abstain.
  Quantifying over a `Sort(_)` itself (incl. `∀(P:Prop). …`, second-order) →
  abstain (the first-order `mk_forall` cannot represent it; any classical
  coincidence is not a guarantee).
- **Reduced occurs-check in `Pi` classification.** The "`cod : Prop`?" and
  "`cod` mentions the bound var?" tests must run on the **whnf/δ-reduced** `cod`
  via the kernel's `infer`/`whnf` (a `def`/`Let` can hide both the sort and an
  occurrence); *undecidable ⇒ case-4 abstain*. A syntactic miss files a
  dependent function type as a plain arrow (wrong signature) or a dependent
  codomain as a universal (wrong quantifier).
- **`App` heads.** A *partially applied* connective/quantifier/equality, a head
  that is a prelude *name shadowed* by a user decl/bound var, and a
  *function-sorted bound-variable* head (HO/extensional reasoning the solver
  lacks) each → abstain.

**Two process/structural invariants.** (1) Lowering runs against an
**immutable, fully-admitted `Env`** — it never admits or mutates mid-lowering
(so the kernel's conversion memo it leans on for `whnf`/`is_def_eq`
classification can never go stale under it). (2) The **end-to-end differential
is a per-slice LANDING GATE, not a closing 후검증** — and it is a **THREE-WAY**
(`z3_differential.py`), not z3-only, because the lowering and the engine share a
trust boundary that z3 alone cannot separate: the lowering's job is to hand the
engine the **same** input the native parser would, so a wrong verdict z3 catches
could be a *lowering* bug OR a shared *engine* bug. Each random script
(`adsmt-ir-smtlib` fragment, run through the **real** face→kernel→lower→solver
pipeline — not unit-built target terms, [[feedback_roundtrip_through_real_producer]])
is decided by THREE engines: **LOWERING** (the subject), **NATIVE** `lu-smt`
(same engine, no lowering — the reference) and **Z3** (oracle). Comparing
LOWERING against NATIVE **cancels the shared engine**: a verdict the native path
gets wrong too (`lowering == native ≠ z3`) is a pre-existing **engine** bug
(quantifier opacity #347 / linear var-cancellation #348 — tracked, NOT a lowering
defect); a verdict ONLY the lowering gets wrong (`native == z3 ≠ lowering`) is
the genuine lowering mistranslation **the gate fails on**. The lowering being
*more* decisive than native and matching z3 (the ground constant-fold deciding
`(= 4 3)` the bare native path merges in UF) is a sound **improvement**. Run
over a **randomized**, multi-seed corpus ([[feedback_z3_differential_for_unsat_trust]]:
a 13/13 battery hid a 119/600 false-unsat) — 0 lowering-attributable verdicts.

**Increment plan (M3-8, slices, each design→impl→adversarial-review→후검증):**
**M3-8a ✅ (landed, `adsmt-ir-lower` crate)** = the first-order / EUF /
quantifier core (`Prop`→`Bool`, open-const → `Const`, prelude
connectives/`=`/`forall`/`exists`, `Pi`-into-`Prop`→`mk_forall`, implication,
structural `App`, `Bound`→**globally-fresh** named-var env, whole-query abstain;
the four P0 guards wired; `ite`/datatypes/`Fix`/dependent/HO/proof-as-data
abstain; a Bool quantifier conservatively abstains — the `Bool`↦`Prop` collapse
makes it indistinguishable from second-order prop quantification) — pairs with
face slices 1–2. 15 tests: `alpha_eq` fidelity vs hand-built target terms +
capture-safety + whole-query abstain + 4 **end-to-end verdicts** through the
real `adsmt-engine::Solver` (the per-slice landing gate), all via the real face
producer (Bool-branch `ite` ✅ lowered as `(c→a)∧(¬c→b)`; non-Bool `ite`
abstains — no solver `ite` term). **M3-8b ✅ (landed)** = datatypes
(`Inductive`/mutual → engine `DatatypeDecl` from the admission journal, in
`Lowered::datatypes`; constructor apps → structural terms over the ctor symbols;
the engine's `Datatypes` theory gives disjointness / injectivity. Indexed /
parametric / `Prop`-sorted inductives + non-first-order fields abstain;
`is_finite` conservative = all-nullary). **`Match`/`Elim`/selectors NOT lowered**
— the face produces none yet (M3-7b); when it does, `Match` is finite/enum-only +
coverage disjunction, inductive-ω `Match`/recursors abstain until the engine's
datatype theory is an initial algebra. M3-8c = defs (non-recursive `def` is
already **δ-inlined** = sound + complete for the face's output; the
structure-preserving `Const`+axiom form is a deferred optimization, and the
recursion-axiom form stays deferred to the initial-algebra theory). **후검증** target = *meaning-preservation*: abstract over the
denotation, prove the lowered image is logically equivalent on the lowerable
fragment and whole-query-abstain ⇒ no false verdict; plus an **end-to-end
three-way differential** (lower a face-elaborated query, solve, cross-check the
verdict against BOTH the native `lu-smt` reference — to cancel shared engine
bugs — and z3 the oracle; see invariant (2) above — the
[[feedback_z3_differential_for_unsat_trust]] discipline). Lowering lives in a
**new sibling crate** (e.g. `adsmt-ir-lower`,
path-dep on both `adsmt-ir` and the frozen `adsmt-core`/engine) so the rc.41
stabilization workspace stays untouched — a downstream *consumer*, not a
workspace edit.

## 6. Relationship to adsmt-core's HOL+HKT `Term`

`adsmt-core::Term` is the *solver's* representation: simply-typed HOL with
HKT in a separate `Type` layer (`Var`/`Const`/`App`/`Lam`), hash-consed
for O(1) equality, tuned for the CDCL(T) hot path. The CIC IR is **richer
and upstream**: dependent types, inductives, recursors, the def/open
modality — the elaboration *target*, lowered *to* the adsmt-core form.
They are not competitors; the IR is where structure is *preserved*, the
core `Term` is where it is *solved*.

## 7. Frontier / deliberate omissions (all sound-by-omission)

Each omission only makes the checker reject more, never accept wrongly —
the right trade under the prime directive. Tracked here, not hidden:

- **Cumulativity** (`Type(i) ≤ Type(j)`): not modeled; some valid terms
  needing subtyping are rejected. Add via a `≤` in conversion later.
- **η-conversion**: omitted; `f` vs `λx. f x` are not yet convertible.
- **Universe polymorphism**: levels are concrete `u32`; no level
  variables. Fine until the prelude needs `Type@{u}` generics.
- **Hash-consing** ✅ (M3-2, landed) — `Term` is now an `Arc`-interned
  **handle**: a global, zero-dependency interner (`term.rs`,
  `LazyLock<Mutex<HashMap<u64, Vec<Term>>>>`) dedups structurally-equal terms
  to one allocation, so `==` is `Arc::ptr_eq` and `Hash` is a cached structural
  hash — both **O(1)**. The interner probes its bucket by *structural* equality
  (collisions cannot cause a false dedup; distinct terms never share an `Arc` —
  the soundness invariant for `is_def_eq`'s `==`); bottom-up interning makes the
  child `ptr_eq`-comparison a faithful structural equality. This is the §8
  conversion/NbE memo's prerequisite (O(1) identity for the memo key + content
  digests). *First-cut policy:* the interner holds strong refs (an arena for the
  process; a `Weak`-GC, as in `adsmt-core`, is a later refinement, not a
  soundness concern). The metatheory 후검증 (44 verified) is **unaffected** — it
  abstracts over term identity / typing, so the representation change sits below
  its firewall; `==`-faithfulness is the implementation obligation, covered by
  `term.rs`'s interner tests + the M3-2 adversarial review.
- **`fix` / general recursion / inductives**: M2 (above).
- **Modules / sections**: a flat `Env` for now; namespacing is M3+.

## 8. Optimization: AOT + algebraic JIT across the hybridization

AOT prelude-banking and the algebraic JIT are **not solver-only**
optimizations — they are a general *"bake the shared prelude once, then
replay/memoize hot work behind an algebraic-digest guard"* pattern, and
they apply at **every layer** of the hybridization, the IR included. The
two existing implementations in `adsmt` are the templates:

- **AOT** (`adsmt-aot`, §3.1): a prelude is type-checked / saturated once
  and serialized to a binary bank; `--aot-load` starts a query from the
  baked state, so per-query cost is O(query delta). The §3.5.5 follow-up
  precomputes the prelude atom map at load so even the replay resolver is
  O(delta).
- **Algebraic JIT** (`adsmt-jit` §3.2 + the §3.5 replay): a hot trace is
  recorded once and **replayed** at re-encounter behind an *algebraic
  invariant guard* — a content digest of the canonical clause set
  (`jit_trace_digest`; the rc.34.4 incremental AdHash clause-fold, the
  rc.34.3 K12 signature digest). A digest hit replays the verdict; a miss
  *falls through to the full computation*.

### How they map onto the IR

- **AOT — an `Env` bank as an *admission journal*** ✅ (M3-1, `bank.rs`). The
  bank stores the [`Env`]'s **admission journal** — the exact ordered sequence
  of *checked-admitter inputs* (`define` / `postulate` /
  `declare_inductive_indexed` / `declare_mutual`), the **inputs** only, never
  the derived recursor bookkeeping (`method_template` / `rec_positions` /
  `ctor_of` …). Loading (`bank_decode`) **replays that journal through the same
  checked admitters**, so a loaded `Env` is type-checked, positivity-checked,
  and template-derived *identically* to the original — and the bank therefore
  adds **no trust** beyond the admitters (themselves 후검증'd). This is the
  strongest possible posture under the prime directive: *a loaded bank can
  never admit a declaration the running kernel would not, because the running
  kernel does admit it, on load.* A corrupt / truncated / kernel-incompatible
  journal fails to decode or fails to re-admit (a `BankError`), and the caller
  **falls through to full elaboration** (`Unknown`-safe). No
  `KERNEL_RULES_VERSION` gate is needed for *soundness* — re-admission
  self-validates against whatever rules the running kernel has. (An earlier
  "serialize the checked `Env` state + trust it behind a digest" design was
  found **fatally unsound** by the M3-1 design-review workflow: a digest +
  re-encode proves codec *self-consistency*, not *type-correctness*, and would
  trust the derived templates verbatim — the rc.28 S.1-AOT shape one level up.
  The admission-journal design dissolves that whole class structurally.)

  What it wins: it skips surface **parse + elaboration** (the journal is ready
  kernel terms) and yields a portable, content-addressed, re-checkable prelude
  artifact, on which the lowering's propositional AOT bank composes. Load still
  re-runs the kernel type-checker over the prelude (correctness-first); the full
  "type-check once, then O(query delta)" win is the **deferred** WHNF/normal-form
  conversion-memo (next bullet), which §7 gates on the hash-consing port.
- **Algebraic JIT — conversion / NbE memoization** ✅ (M3-3, landed). Type-
  checking is dominated by *repeated reduction*: the same prelude lemmas are
  normalized over and over inside `is_def_eq`. The memo records each
  `whnf(env,t)` and `is_def_eq(env,a,b)` verdict once, keyed directly by the
  **hash-consed term handle** — with hash-consing (M3-2) the handle *is* the
  content digest (O(1) identity), so no separate AdHash/K12 encoding is needed
  (simpler than §3.5's clause digests). It lives on the `Env` (`env.rs` `Memo`,
  `reduce.rs`'s memoized `whnf`/`is_def_eq`); `is_def_eq` also gains the
  hash-cons `a == b` ⟹ `true` (α-equivalence) fast-path. **Soundness:**
  `whnf`/`is_def_eq` are pure functions of the env-*state*, so the memo is
  **cleared on every state mutation** (`declare`/`register_inductive`/
  `register_group`) and **reset on clone** — every surviving entry is valid for
  the current state, so a hit equals recompute and the memo is *transparent*
  (no verdict changes). 후검증: `memo_soundness::memoized_equals_uncached`
  (+ `stale_entry_breaks_validity` records that clearing is necessary).

### Soundness discipline (non-negotiable)

Every cache obeys the §3.5 / `--aot-load` rule: **a digest miss must fall
through to full re-checking; a hit must be an exact match, never a stale
trust.** The prime directive holds because the cache can only ever *skip
work it has already verified* — a wrong digest match is impossible by
construction (exact content key), and anything unrecognized is simply
recomputed (⇒ `Unknown`-safe, never a wrong `Sat`/`Unsat`). The rc.34.1
lesson applies verbatim: round-trip every replay/serialize test through the
*real* producer, and ship a CLI/wire end-to-end smoke.

This makes hash-consing (§7) a **prerequisite**, not a nicety: O(1)
identity is what both the normal-form memo table and the incremental digest
need. AOT/JIT-banking the IR is the natural M3+ companion to lowering — and
the same `bake-once + guarded-replay` shape carries on into the ASP
grounder, the propagator bus, and the SMT core, so the *whole* hybrid stack
pays the prelude cost once.
