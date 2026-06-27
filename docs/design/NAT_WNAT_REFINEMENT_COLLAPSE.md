# Nat / WNat refinement-collapse: `Nat = {x:Int | x ≥ 1}`, `WNat = {x:Int | x ≥ 0}`

Status: **design + pre-verification** (implementation gated on the pre-verified
relativization lemma). Realises task #338 (wire lukb type-relation positivity
into the solving path) as the integer-carrier case of the `*Like` family's
`Reduces` spine (see `docs/design` siblings and the `numberlike-family-design`
memory).

## 1. Motivation

The lukb type relation `Nat ⊂ WNat ⊂ Int ⊂ Real` (with **`0 ∉ Nat`**) is
currently TYPECHECK-ONLY: `adsmt-ir-lower` maps the `Nat`/`WNat` sorts to opaque
`CType::const_("Nat"/"WNat")` (uninterpreted), and the injections
`nat2int`/`wnat2int`/`nat2wnat` to EUF functions. So a `Nat` variable reaches the
engine as an opaque EUF element whose defining positivity (`≥ 1`) **never exists
as a constraint**, and `nat2int(x)` is a function application — not a bare `Var`
— so `LinArith` cannot reason about it arithmetically. Two visible consequences:

- the broad Nat/WNat-positivity proof class (Fermat-style `x : Nat ⟹ x ≥ 1`) is
  undecidable on this path;
- order laws over the refinement carriers (`EngineLawProver`) stay
  native-`Unknown` because their `le` routes through `nat2int(x)`.

**The fix (user proposal):** treat `Nat` and `WNat` not as separate domains but
as `Int` carved out by a predicate — the standard refinement-type view
(Liquid Haskell / F\*). `Nat = {x : Int | x ≥ 1}`, `WNat = {x : Int | x ≥ 0}`.
Then a `Nat` variable IS an `Int` variable plus a bound, the injections are the
identity inclusion, and `LinArith` reasons about it directly.

## 2. Scope: types stay distinct, the SOLVER sort collapses

`Nat`/`WNat` remain **distinct types** for type inference and refinement
checking (you still may not pass an `Int` where a `Nat` is required without
discharging `≥ 1`). The collapse happens **only at the lowering boundary** into
the engine — i.e. it is part of `adsmt-ir-lower`, the same place the type
relation is currently dropped. Nothing above the engine boundary changes.

This is exactly the `*Like` family's `Reduces` spine instantiated for the
integer carriers, with **`encode = identity`** (the inclusion `ℕ ↪ ℤ` is not an
abstract function but the literal subset map):

```
Reduces(Nat,  base = LIA, rep = Scalar(Int), encode = id, decode = id, domain = (≥ 1))
Reduces(WNat, base = LIA, rep = Scalar(Int), encode = id, decode = id, domain = (≥ 0))
```

## 3. The encoding `⟦·⟧`

Three coupled rewrites, applied during lowering:

### 3a. Sort collapse
`lower_sort(Nat) = Int`, `lower_sort(WNat) = Int` (was an opaque sort const).

### 3b. Injections → identity
- `nat2int`, `wnat2int`, `nat2wnat` → **erase** (lower `inj(t)` to `lower(t)`):
  under the collapse both source and target are the `Int` sort.
- `nat2real`, `wnat2real` → `int2real` (the Nat/WNat part erases to `Int`, then
  the genuine `Int → Real` coercion remains).
- `int2real` → unchanged (a real coercion, NOT identity).

### 3c. Positivity as a quantifier guard (the soundness crux)
For the carrier predicate `dom_S(x)` (`dom_Nat(x) ≡ x ≥ 1`, `dom_WNat(x) ≡ x ≥ 0`):

```
⟦∀(x : S). P⟧  =  ∀(x : Int). dom_S(x) ⟹ ⟦P⟧
⟦∃(x : S). P⟧  =  ∃(x : Int). dom_S(x) ∧ ⟦P⟧
```

A **free** `S`-typed variable `c` (e.g. a Skolem or a top-level declared
constant) contributes `dom_S(c)` as a top-level **hypothesis** (conjoined into
the asserted formula / asserted as its own fact).

The `⟹` (for `∀`) vs `∧` (for `∃`) polarity is standard quantifier
relativization and is the single most soundness-critical detail.

## 4. Soundness

### Invariant A⟺B — collapse and positivity are atomic
Sort-collapse (3a/3b) **without** the positivity guard (3c) is **unsound**: a
formula that is unsat only because of Nat-positivity (e.g. `∃(x:Nat). x = 0`,
unsat since `0 ∉ Nat`) would become satisfiable over the unconstrained `Int`
domain — a **false-sat**. The lowering MUST therefore emit 3c for every
`Nat`/`WNat` binder and free variable it erases under 3a/3b. (Forgetting a true
fact is the dangerous direction — the dual of `feedback_soundness_opaque_fallback`.)

### The relativization lemma (what pre-verification proves)
Let `M` be an `Int`-interpretation, and let `⊨ᵣ` interpret an `S`-quantifier as
ranging over `{x : Int | dom_S(x)}` (the **refined** semantics — the intended
meaning of `Nat`/`WNat`). Then for every formula `φ`:

```
   M ⊨ᵣ φ   ⟺   M ⊨ ⟦φ⟧
```

i.e. the encoding is **satisfiability-preserving in both directions** (sound AND
complete, not merely soundness-monotone). Consequences:

- `φ` is satisfiable under the refined semantics ⟺ `⟦φ⟧` is satisfiable over `Int`
  — so `lu` and `z3` (fed the explicit `Int + dom` encoding) must agree.
- No false-sat (`⟸` direction: a refined-unsat `φ` lowers to an `Int`-unsat `⟦φ⟧`).
- No false-unsat (`⟹` direction: a refined-sat `φ` lowers to an `Int`-sat `⟦φ⟧`).

Proof shape: structural induction on `φ`. The quantifier cases are the standard
relativization steps; the `⟹`/`∧` choice is forced by the `∀`/`∃` duality
(swapping them breaks the `∃` case: `∃x. dom ⟹ P` is satisfied by any
out-of-domain witness, losing the constraint). **This lemma is the
pre-verification target** (`~/nat-wnat-refinement-verification`, a cargo-verus
project, per the project's pre-verify-the-soundness-core convention).

### EUF-congruence caveat
Collapsing `nat2int` from an opaque EUF function to the identity changes
congruence behaviour (previously `nat2int(a) = nat2int(b)` only via `a = b`
through congruence; now they are literally equal as `Int` terms). This is the
*correct* semantics (the injection IS the inclusion, not an arbitrary function),
but it is **not trivially monotone**, so it requires the z3-differential before
any new `unsat` is trusted (per `lukb-type-relation-utilization`).

## 5. Implementation touch-points (`adsmt-ir-lower`)

1. `lower_sort` — map `theory::NAT` / `theory::WNAT` to the `Int` `CType`.
2. The injection arm — recognise `NAT2INT`/`WNAT2INT`/`NAT2WNAT` as identity
   (lower the argument, drop the head); `NAT2REAL`/`WNAT2REAL` → `int2real`.
3. Quantifier lowering — when a bound variable's sort is `Nat`/`WNat`, wrap the
   body with `dom_S ⟹ ·` (∀) or `dom_S ∧ ·` (∃) over the now-`Int` binder.
4. Free-variable hypotheses — collect erased `Nat`/`WNat` free variables and emit
   their `dom_S` as top-level facts (alongside the lowered assertion).
5. The `adsmt-class` `IntegerLike(Nat)`/`IntegerLike(WNat)` instances gain the
   `Reduces` instance data (`encode = id`, `domain = dom_S`) so the type-relation
   layer and the lowering agree (one source of truth).

The kernel `adsmt-ir/src/theory.rs` postulates are unchanged — `Nat`/`WNat`/the
injections still exist as kernel constants; only their *lowering* changes.

## 6. Validation plan

A randomized z3-differential dedicated to the refinement fragment: generate
formulas over `Nat`/`WNat`/`Int` variables (with `≤`/`<`/`=`/`≠`/`+`/`-`, and
`∀`/`∃` binders), then
- run `lu` through the new lowering, and
- run `z3` on the **explicit** `Int + dom` encoding (declare each Nat/WNat var as
  `Int`, assert its `dom`, guard each quantifier),

and compare. The dangerous direction is `lu sat / z3 unsat` (false-sat from a
dropped or mis-polarised guard). Mirror the two-variable LIA differential that
caught #340/#341.

## 7. Phasing

1. **This doc** + the pre-verified relativization lemma (`~/nat-wnat-refinement-verification`).
2. Quantifier-free core: 3a + 3b + free-var hypotheses (no binder guards yet) —
   validates the sort-collapse + injection-identity + free-var positivity.
3. Quantifier guards (3c for binders) — the relativization, gated on the lemma.
4. Wire the `Reduces` instance data into `adsmt-class` (one source of truth).
5. z3-differential gate (§6) before trusting any new `unsat`.

Once landed: the `EngineLawProver` order laws over `Nat`/`WNat` become provable
(their `le` no longer routes through an opaque `nat2int`), and the broad
Nat/WNat-positivity proof class is decidable on the lukb→engine path.
