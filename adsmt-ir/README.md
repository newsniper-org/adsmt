# adsmt-ir

The **typed CIC kernel IR** — the language-agnostic core lingua franca for
adsmt's multi-paradigm substrate (SMT-LIB-3.0 ⊕ typed-Datalog/ASP on one
trail). Surface languages elaborate *to* these kernel terms; the solver
lowers them *to* its CDCL(T) working representation. The kernel sits
**before** recursion / definitions / higher-order structure are flattened
into quantified axioms — the structure plain SMT-LIB discards and the
verus MBQI / trigger hell is made of.

A small, **dependency-free, trusted** Pure-Type-System kernel: CIC's λΠ
core with an impredicative `Prop` and a predicative `Type` tower, de
Bruijn-indexed, plus a bidirectional type checker. Nothing reaches the
environment without passing the checker — the IR-level instance of the
project's verdict-verification gate (an unverifiable term is *rejected*,
never silently trusted).

The one multi-paradigm-specific feature already in the kernel is the
**def / open modality**: `def` constants δ-unfold during conversion
(closed-world / inductive / ASP ownership); `open` constants stay opaque
(classical / theory ownership). Reduction reads the flag, so paradigm
ownership is structural in the kernel.

```sh
cargo test          # 12 kernel conformance tests + 1 doctest
cargo clippy
```

## Status

- **M1:** the dependent λΠ core — sorts, Π/λ/let, de Bruijn substitution,
  β/ζ/δ WHNF, convertibility, a bidirectional checker, the def/open
  modality. ✅
- **M2:** inductive types + constructors + the dependent recursor
  (`Term::Elim` primitive — typing rule + ι-reduction), strict positivity,
  and the Prop large-elimination soundness guard. ✅
- **M2.5:** **indices (GADTs)** — index-varying constructors
  (`Vec A : Nat → Type`), the dependent recursor over an index family
  (motive `Π(n). I … n → Sort`), via a per-constructor method template. ✅
- **M2.6:** non-recursive case analysis (`Match`), **guarded `fix`** with a
  conservative structural-decrease checker (the soundness-critical piece),
  and **mutual induction** (`declare_mutual`; independent recursors). ✅
- **M2.7:** **mutual recursors** (`Term::MutElim` — a tuple of motives,
  cross-member IHs, per-member dispatch + Prop guard); adversarially
  re-reviewed, 0 soundness holes. ✅
- **M2.8:** guard **`let`-aliasing** (recursion on a let-bound strict subterm)
  + **higher-order recursive arguments** (`Π(z:D). I idx` with a functorial IH
  `Π(z:D). motive (g z)`, ι threading `λz. Elim(…, g z)`; adversarially
  re-reviewed, 0 holes). ✅
- **후검증:** the kernel metatheory (subject reduction + `fix` termination +
  ι-preservation + positivity + ζ-alias + HO functorial-IH) is Verus-verified
  in [`../adsmt-ir-verification`](../adsmt-ir-verification) (38 verified). ✅
- **M2.8+ (deferred, re-reviewed every task from M3 on):** nested recursive
  containers, mutual `fix` (lexicographic measure), heterogeneous-universe
  elim.
- **M3-1:** the **AOT-bank** (`bank.rs`) — the checked `Env` serialized as an
  **admission journal** and reloaded by *re-admission* (`bank_encode` /
  `bank_decode`), so loading is type-checking, sound by construction; a corrupt
  / incompatible bank is rejected → fall through (`Unknown`-safe). The
  cross-hybridization AOT directive at the IR (DESIGN §8); design-reviewed (the
  "trust serialized state" alternative was found unsound) + adversarially
  re-reviewed (4 lenses, probes against the real bank): **0 soundness holes**
  (14/14 wrong-acceptance attacks correctly rejected), and one *totality* fix
  landed — a forged `Fix.rec_arg` reached `peel_pis`'s speculative allocation
  (a pre-existing kernel crash, not a wrong verdict). ✅
- **M3-2:** **hash-consing** (`term.rs`) — `Term` is now an `Arc`-interned
  handle: a global zero-dependency interner dedups structurally-equal terms, so
  `==` is `Arc::ptr_eq` and `Hash` is cached, both O(1). The §8 conversion/NbE
  memo's prerequisite; behavior-preserving (the suite is the oracle) + the
  faithfulness invariant (distinct terms never share an `Arc`) is regression-
  tested; adversarially re-reviewed. ✅
- **M3-3:** the **conversion memo** (`env.rs` `Memo` + `reduce.rs`) — the
  algebraic-JIT half: `whnf`/`is_def_eq` memoized on the `Env`, keyed by the
  hash-consed handle, **cleared on every state mutation** (so a hit is always
  valid — the §3.5 discipline) + the `a == b` α-equivalence fast-path. Sound
  (transparent: 후검증 `memoized_equals_uncached`) + staleness-regression-
  tested + adversarially re-reviewed. ✅
- **M3 (next):** surface faces (SMT-LIB-3.0, Datalog) + lowering to the solver
  (`def`→stable-model gate, `open`→theory/G-SAT gate).

✅ 70 tests (12 kernel + 9 inductive + 5 indexed + 12 recursion + 8 mutual +
3 higher-order + 4 bank + 4 memo + 9 bank-unit + 3 term-unit + 1 doctest) green,
clippy clean.

See [`DESIGN.md`](DESIGN.md) for the full design, the roadmap, the
AOT/algebraic-JIT optimization plan (§8), the relationship to
`adsmt-core`'s HOL+HKT `Term`, and the (sound-by-omission) frontier list.

## Layout

| file | contents |
|---|---|
| `src/term.rs` | kernel terms, universes, `shift` / `subst_top` |
| `src/env.rs` | the global environment + the `def`/`open` `Modality` |
| `src/reduce.rs` | `whnf` (β/ζ/δ/ι/μ) + `is_def_eq` (convertibility) |
| `src/check.rs` | bidirectional `infer`/`check` + checked `define`/`postulate`/`fix` |
| `src/inductive.rs` | inductive + mutual admission (positivity) + recursor/match templates |
| `src/guard.rs` | the `fix` structural-decrease guard (soundness-critical) |
| `src/error.rs` | `TypeError` (every constructor is a rejection) |
| `src/bank.rs` | the AOT-bank: admission-journal `bank_encode`/`bank_decode` |
| `tests/kernel.rs` | λΠ-core conformance + rejection-path tests |
| `tests/inductive.rs` | inductives, recursor (ι), positivity, Prop-elim guard |
| `tests/indexed.rs` | indexed inductives (GADTs) + index-family recursor |
| `tests/recursion.rs` | `Match`, guarded `fix` (μ), `let`-alias, guard rejections |
| `tests/mutual.rs` | mutual induction + mutual recursors + positivity |
| `tests/higher_order.rs` | function-typed recursive args (functorial IH + ι) |
| `tests/bank.rs` | AOT-bank round-trip through the real producer + rejection paths |

This is forward-looking, post-v1.0 work, kept in its own repository (like
`oxiz-nl2`, `unified-gate-verification`) so the `adsmt` v1.0.0
stabilization stays clean; it can be absorbed into the workspace once
mature.
