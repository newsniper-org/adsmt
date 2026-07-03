# The `PartialEq` / `Eq` / `UpCast` / `PartialOrd` / `Ord` relation family

**Status: DECIDED by the owner, 2026-07-03** — this is the designated solution
path for #391 (the verus-emitted `is-{ctor}` tester symbols), and it RESHAPES
the existing 1-param `PartialOrd(I)`/`Ord(I)` pair in `adsmt-class::numberlike`
into the general heterogeneous family below.

## The owner's specification (normative)

Five type relations (adsmt "type relation" = the type-class layer,
`adsmt-class`; inheritance = instance-level premises, the `numberlike` idiom):

| relation | params | inherits (instance premises) |
|---|---|---|
| `PartialEq(A, B)` | 2 | — |
| `Eq(T)` | 1 | `PartialEq(T, T)` |
| `UpCast(A, B)` | 2 | — |
| `PartialOrd(T, A)` | 2 | `PartialEq(T, A)` **and** `UpCast(T, A)` |
| `Ord(T)` | 1 | `PartialOrd(T, T)` **and** `Eq(T)` |

Normative constraints, verbatim from the decision:

1. **`Eq(T)` inherits `PartialEq(T, T)`.**
2. **`PartialOrd(T, A)` inherits BOTH `PartialEq(T, A)` and `UpCast(T, A)`** —
   a cross-sort comparison requires the failure-free embedding of `T` into the
   comparison sort `A`; the order is decided in the wider carrier.
3. **Symmetry synchronization:** when `A ≠ B`, declaring an instance
   `PartialEq(A, B)` IMPLICITLY synchronizes the instance `PartialEq(B, A)`
   (the registry materializes the mirror; user code never declares both, and a
   conflicting explicit mirror is a duplicate-instance error).
4. **`UpCast(A, B)`** is the type relation for **failure-free casting to a
   supertype** (total, no partiality — the generalization of the elaborator's
   hardcoded numeric-injection lattice `Nat ⊂ WNat ⊂ Int ⊂ Real`).
5. **`UpCast(T, T)` instances are BUILTIN** (the identity cast, for every `T`)
   — **explicit user/library instances of `UpCast(T, T)` are FORBIDDEN**
   (declaring one is an admission error, not an overlap).
6. **`Ord(T)` inherits `PartialOrd(T, T)` and `Eq(T)`.**

Lawful-instance discipline applies throughout ([[lawful_type_relation_instances]]):
laws are goal-members discharged by adsmt's own solver at instance admission
(PartialEq: symmetry+transitivity in the heterogeneous form mediated by UpCast;
Eq: reflexivity/totality of `eq`; UpCast: injectivity is NOT required (it is an
embedding claim only where a law demands it), but composition-coherence laws
`UpCast(A,B) ∘ UpCast(B,C) = UpCast(A,C)` where all three instances exist;
PartialOrd: antisymmetry-up-to-`eq`, transitivity; Ord: totality — the existing
`law_totality`).

## Conflict rulings (owner, 2026-07-03 — supplements the spec above)

Three points where the spec meets the existing implementation, each RULED:

1. **FULL RESHAPE of `numberlike`'s 1-param `PartialOrd(I)`/`Ord(I)`.** The
   2-param `PartialOrd(T, A)` REPLACES the 1-param form; every existing premise
   site (`RealLike(R)`'s `PartialOrd(R)`, `IntegerLike(I)`'s `Ord(I)`,
   `ord_instance`, the FloatingPoint doc note) moves to the DIAGONAL
   `PartialOrd(T, T)` (where the inherited `UpCast(T,T)` premise is satisfied
   by the builtin identity). `Ord(T)` gains the `Eq(T)` premise. Internal
   `adsmt-class` API breakage accepted.
2. **Rust-style `Eq`-GATING of `=`.** Using `=`/`!=` at sort `T` REQUIRES an
   `Eq(T)` (i.e. `PartialEq(T,T)`) instance. To preserve every existing
   behaviour, the elaborator auto-grants a BUILTIN `Eq` instance to every
   declared sort — uninterpreted `sort S`, the ring sorts `GF(p)` /
   `IntModulo(m)` / `GFPower(p,n)`, `Prop`/Bool, numerics, and each `data`
   datatype (whose instance is the lawful auto-derivation of §"How this solves
   #391"). The gate is thus semantically explicit but observationally
   conservative today; a future opt-out (a sort WITHOUT Eq) becomes possible.
3. **`UpCast` and `Reduces` COEXIST as separate layers, WITH an inheritance
   edge: `UpCast(A, B)` inherits `Reduces(A, B)`** (owner follow-up ruling,
   2026-07-03). `UpCast` is the surface/elaboration-layer failure-free
   embedding (which sort a heterogeneous `=`/comparison lands in, which
   injection to insert); `Reduces` remains the solve-time theory-reduction
   spine of the *Like family. The inheritance direction is forced by the
   semantics: a failure-free supertype embedding IS a reduction edge (the cast
   method = `encode`, the image characterization = the refinement predicate —
   ℕ↪ℤ's positivity guard is exactly this), while the REVERSE does not hold
   (`GF(p)→Int` mod-p decode and `Complex→(Real,Real)` representation change
   are `Reduces` but NOT failure-free supertype casts) — so `UpCast ⊂ Reduces`,
   the stronger inheriting the weaker, the `Eq : PartialEq` shape. Coherence:
   the builtin `UpCast(T,T)` identity synchronizes a builtin `Reduces(T,T)`
   identity (the trivial reduction). `Reduces` is not yet a concrete
   `Relation` (the numberlike methods are "Reduces-spine-deferred"), so this
   edge TAKES EFFECT when `Reduces` materializes; until then `UpCast` carries
   no Reduces premise. The numeric `UpCast` instances' cast methods REUSE the
   existing injection constants (`nat2wnat`/`nat2int`/`to_real`, …) — no new
   kernel symbols.

## How this solves #391 (`is-{ctor}` testers)

The verus emitter calls `is-diff!Color./Red(x)` — undeclared. Under this
family, a `data` declaration auto-derives a **lawful `Eq(T)` instance** (the
laws discharged by the engine's datatype theory: distinctness + injectivity
make `eq` decidable), and the tester elaborates through it:

- `is-C(x)` for a NULLARY `C` ⟶ `x = C` — well-typed because `Eq(T)` (hence
  `PartialEq(T, T)`) licenses `=` at sort `T`.
- `is-C(x)` for a field-bearing `C` ⟶ the shape biconditional
  `x = C(sel₀(x), …)` (the SMT-LIB face's `9881b21` desugar), same licensing.

The elaborator recognizes `is-{ctor}` names for constructors of DECLARED
datatypes only (an unknown ctor stays an unknown-symbol error).

## The elaborator rerouting (the bigger consequence)

`adsmt-ir-lukb`'s `elab_bin`/`unify_sorts` currently hardcode the numeric
lattice (`numeric_rank`/`inject`). Under this family:

- `a = b` (and `!=`) elaborates via `PartialEq(A, B)` resolution: `A = B` needs
  `Eq(A)`/`PartialEq(A,A)`; `A ≠ B` needs a `PartialEq(A, B)` instance (or its
  synchronized mirror), whose own premises pull the `UpCast` that performs the
  injection. The kernel term still applies the ONE `=` prelude constant at the
  common (upcast-target) sort — the relation layer decides *which* sort and
  *which* injection, replacing `unify_sorts`' hardcoded lattice.
- `< <= > >=` elaborate via `PartialOrd(T, A)` the same way (comparison in the
  upcast target).
- The numeric lattice becomes four BUILTIN `UpCast` instances
  (`Nat→WNat`, `WNat→Int`, `Int→Real`; composition gives the rest) + the
  builtin identity; `Nat`/`WNat`/`Int`/`Real` get builtin `Ord` (hence
  `PartialOrd`/`Eq`/`PartialEq`) instances. Verdicts must be UNCHANGED on the
  existing test corpus (the reroute is a resolution-mechanism swap, not a
  semantics change).
- Datatypes: auto-derived `Eq(T)` (above). NO auto `Ord`/`UpCast` for
  datatypes in v1.

This realizes the four-way-interlock intent ([[four_way_interlock_design_intent]]):
the type-relation layer becomes a DECISION INPUT to elaboration (which
injection, which sort), not just a typecheck-time annotation — the same lever
#338 opened for Nat/WNat positivity.

## Staging

1. **F1 — the family in `adsmt-class`** (new `eq_ord.rs`, mirroring
   `numberlike.rs`): the five relations + builtin `UpCast(T,T)` identity +
   the explicit-`UpCast(T,T)`-forbidden admission gate + the `PartialEq`
   symmetry-sync in the registry + numeric builtin instances + laws. RESHAPE:
   `numberlike`'s `PartialOrd(I)`/`Ord(I)` re-based onto the 2-param forms
   (`ord_instance` premise chain updated; `IntegerLike`'s `Ord(I)` premise
   unchanged in name). Unit tests incl. sync-mirror + forbidden-identity.
   **LANDED `357db06`** (adsmt-class 51/0; engine class_laws re-based 5/0).
2. **F2 — lukb elaborator reroute**: `=`/`!=`/comparisons through
   `PartialEq`/`PartialOrd` resolution. **LANDED** — the shape that landed is
   *license-then-execute*: `elab_bin` GATES before `unify_sorts` (same-sort
   `=`/`!=` → `Eq(T)`; cross-sort → `PartialEq(A,B)` incl. the synchronized
   mirror; `< <= > >=` → `PartialOrd` in either operand order; arith ops
   ungated), every declaration site auto-grants the builtin `Eq`
   (`Item::Sort`, ring-sort canon, `Item::Data`, `Bool`≡Prop, numerics via
   `install_eq_ord_numeric`), and `class_sort_name` whnf-reduces first (a
   `match` motive leaves a β-redex sort). `unify_sorts`' `numeric_rank`/
   `inject` mechanics are KEPT as the cast EXECUTOR — the registry's edge set
   mirrors that lattice exactly, so gate and surgery agree by construction;
   retiring the rank table in favour of `UpCast` `cast`-method bodies is
   deferred until a consumer needs the method, not just the license. Existing
   corpus verdict-identical (lukb 89/0+5/0; driver 9/0 + z3-oracle
   differential 1/0).
3. **F3 — datatype `Eq(T)` auto-derivation + `is-{ctor}` tester elaboration**
   (closes #391; ob1-abs.lukb elaborates end-to-end).
4. **F4 — docs/books + memory + verus-fork notice.**
