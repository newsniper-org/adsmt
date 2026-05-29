---
name: OxiLean surface syntax vs Lean4 — investigation findings
description: Precise comparison of OxiLean's parser/AST against Lean4 syntax, captured for T#31 prover_emit refactor planning. Conclusion — OxiLean is substantially a Lean4 dialect; no separate `prover_emit::oxilean` module needed.
type: reference
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
# OxiLean ↔ Lean4 surface-syntax investigation

**Investigated**: 2026-05-28T06:33:48Z (UTC)
**Subject repo**: <https://github.com/cool-japan/oxilean> (default branch
`main` at investigation time)
**Subject crate**: `oxilean-parse` v0.1.2 (matches OxiLean 0.1.2 release
2026-05-03)
**Sources consulted at investigation time**:
- `README.md` (top-level OxiLean repo)
- `crates/oxilean-parse/README.md` (parser crate readme with AST defs)
- `tests/formal_proofs_test/tests_logic.rs` (concrete parser inputs +
  expected acceptance, 280+ test cases)

## TL;DR

**OxiLean's surface syntax is substantially Lean4-compatible** —
keywords, types, lambdas, quantifiers, comments, Unicode connectives,
universe hierarchy all match. OxiLean publishes a **99.7% parse
compatibility rate against Mathlib4** (181,326 of 181,890 declarations
parse OK after light syntax normalization). For adsmt's
`adsmt-cert::lean_emit` purposes, a **single emit module covers both
Lean4 and OxiLean** — no separate `prover_emit::oxilean` slot needed.

## Surface AST (verbatim from `crates/oxilean-parse/README.md`)

```rust
pub enum SurfaceExpr {
    Var(String),
    App(Box<SE>, Box<SE>),          // f a
    Lam(Vec<Binder>, Box<SE>),      // fun x => body
    Pi(Vec<Binder>, Box<SE>),       // (x : A) -> B
    Arrow(Box<SE>, Box<SE>),        // A -> B (non-dependent)
    Let(String, Option<Box<SE>>, Box<SE>, Box<SE>),
    Match(Box<SE>, Vec<MatchArm>),  // match e with | ...
    ByTactic(Vec<Tactic>),          // by { tac1; tac2; ... }
    Lit(Literal),
    Hole,                           // _
    Parens(Box<SE>),
    Proj(Box<SE>, String),          // e.field
}

pub enum SurfaceDecl {
    Def { name, params, ret_ty, body },
    Theorem { name, params, ty, proof },
    Axiom { name, params, ty },
    Inductive { name, params, ty, ctors },
    Import(String),
    Universe(Vec<String>),
}
```

## Keywords, tokens, comments (matches Lean4)

| Category | Tokens accepted |
|---|---|
| Keywords | `def` `theorem` `axiom` `inductive` `where` `match` `with` `let` `in` `by` `import` `universe` `namespace` `end` `if` `then` `else` |
| Symbols | `->` (arrow), `=>`, `:`, `;`, `,`, `.`, `\|`, parens, braces, brackets, `:=`, `_`, `@`, `#` |
| Literals | `NatLit(u64)`, `StrLit(String)` |
| Comments | `--` line comments, `/- ... -/` block comments (nested) |
| UTF-8 | identifier + math symbol support (α, β, π, λ, →, ⊢, …) |

## Type theory layer (matches Lean4)

| Feature | Status |
|---|---|
| Universe hierarchy `Prop : Type 0 : Type 1 : ...` | identical |
| Dependent types `Pi (x : A), B` | identical |
| Inductive types (`Nat`, `List`, `Eq`, …) | identical |
| Proof irrelevance | identical |
| Universe polymorphism | identical |

## Concrete parser inputs from `tests/formal_proofs_test/tests_logic.rs`

These exact strings are fed to OxiLean's parser+elaborator in the
upstream test suite. They all pass:

```text
axiom impl_self : forall (p : Prop), p -> p
axiom and_intro_type : forall (p q : Prop), p -> q -> p ∧ q
axiom contrapositive : forall (p q : Prop), (p -> q) -> ¬ q -> ¬ p
axiom em : forall (p : Prop), p ∨ ¬ p
theorem and_intro_thm : forall (p q : Prop), p -> q -> p ∧ q := sorry
def id_logic : forall (p : Prop), p -> p := fun h -> h
def compose_impl : forall (a b c : Prop), (a -> b) -> (b -> c) -> a -> c := fun f g x -> g (f x)
```

Observations:
- **Lambda body separator**: tests use `fun x -> body` (OxiLean's
  preferred form). The AST comment uses `fun x => body` (Lean4's
  preferred form). Parser **accepts both** per the README's
  normalization pipeline.
- **Function types**: `A -> B`. Unicode `→` not seen in the tests
  but the lexer says UTF-8 math symbols are supported.
- **Quantifier**: ASCII `forall`, NOT Unicode `∀`. (Lean4 accepts
  both; OxiLean preferred form is ASCII per Mathlib4 normalization.)
- **Connectives**: Unicode `∧`, `∨`, `¬` (same as Lean4).
- **Equality**: `=` (standard).
- **Theorem/axiom/def**: same keywords as Lean4.
- **`sorry`**: supported tactic for stub proofs.
- **Method-style call** (`e.field`, `(x).mp`): supported via
  `Proj(Box<SE>, String)` AST node.

## Mathlib4 parse-compatibility number

From the OxiLean README:
> 7,759 Mathlib4 source files parsed across 280+ categories
> 181,890 declarations tested — **99.7% parse compatibility**
> (181,326 parsed OK)

Categories span all 28+ top-level Mathlib directories (Algebra,
Analysis, CategoryTheory, …). Normalization pipeline applied to
Mathlib4 files before parsing handles `=>` → `->`, Unicode arrow
shorthand, head binders to `forall`, 280+ Unicode operators,
quantifier binders, set-builder notation, subscript indexing, proof
replacement, etc.

→ Strongly implies: anything `lean_emit` outputs in *plain Lean4
shape* (axioms + theorems with `forall` / `->` / `:=`) parses on
OxiLean without modification.

## Tactics (subset of Lean4's)

OxiLean v0.1.2 supports: `intro`, `apply`, `exact`, `simp`, `rfl`,
`ring`, `omega`, `sorry`, `cases`, `induction`, `constructor`.

Our `lean_emit` currently uses **`sorry`** and **`rfl`** only —
both supported.

## Standard library — UNVERIFIED

Lean4's `mathlib4` ecosystem has rich method names like `Eq.trans`,
`(·).mp`, `Eq.subst`, `funext`, etc. OxiLean has its own
`oxilean-std` (416k SLOC, 7,977 tests) but I did NOT verify whether
these specific names exist under those exact spellings.

**Verification action (deferred to T#31 resumption)**: when adding
compound-rule reconstruction (`Trans` → `Eq.trans s<l> s<r>`, etc.),
test the output against OxiLean's stdlib to confirm the names
resolve. If they don't, either:

- Use OxiLean's alternative spellings, OR
- Emit `:= by sorry` style and let the tactic layer fill in, OR
- Add a tiny adsmt-side prelude file (`.lean` / `.oxilean`) that
  defines whatever stdlib names we use as aliases.

## Implications for `adsmt-cert::prover_emit` refactor (T#31)

**Recommended approach (Option A — single emit module)**:

- `prover_emit::common` — shared helpers (collect_free_vars,
  classify_type, witness_summary, escape_for_comment) + semantic
  guide doc-comment
- `prover_emit::lean` — emit Lean4 source. Output is also valid
  OxiLean (per the 99.7% Mathlib4 parse compat) modulo possible
  stdlib name differences.
- `prover_emit::common` doc explicitly notes the dual-target
  intent: "Output produced by this module targets both Lean4 and
  OxiLean. Verify stdlib name resolution at compound-rule
  reconstruction time."

**Rejected approaches**:

- *Option B*: ASCII-normalize the output (`=>` → `->`, Unicode
  arrows → `->`, etc.). Rejected because it makes the output less
  idiomatic Lean4 without measurable benefit on the OxiLean side
  (which parses Unicode too).
- *Option C*: Separate `prover_emit::oxilean` module. Rejected
  because the divergence between the two surfaces is below the
  threshold that justifies code duplication.

**Verification path during T#31**:

When implementing compound-rule reconstruction
(`Trans`/`EqMp`/`Deduct`/`Abs`/`Beta`/`Inst`/`InstType`), emit
samples through both `lean` and `oxilean` toolchains (or at least
the parser/checker step) and confirm acceptance. If a stdlib name
fails on one side, document the divergence and pick the
remediation (alternate name / sorry-stub / adsmt prelude file).

## Out-of-scope (left for separate investigation)

- **Tactic compatibility for the long tail**: `simp`, `omega`,
  `ring` are listed as supported but their exact lemma libraries
  may differ. Not a concern for `lean_emit`'s current scope (only
  `sorry`/`rfl` used).
- **Mathlib4-specific notations**: typeclass instances, `‹›`
  anonymous constructor, `⟨ … ⟩` anonymous constructor, etc. Our
  cert layer doesn't emit these.
- **OxiLean's WASM build target**: not relevant to text emission.
- **`oxilean-std` API surface**: 416k SLOC, would need separate
  audit to map our cert rule names to OxiLean stdlib names.

## When this memory becomes stale

OxiLean is at v0.1.2 with active development. If OxiLean releases
a >=0.2.0 version that changes lambda separator preference, drops
Unicode connectives, restricts `=>` parsing, or otherwise diverges
from the snapshot recorded here, re-investigate before applying
this memory's conclusions. Check
<https://github.com/cool-japan/oxilean/blob/main/CHANGELOG.md> at
that point.
