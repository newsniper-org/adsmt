<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-07-03
re: emit-lukb fidelity — LUKB_SUCCESSOR_SURFACE.md §2c/§6 ("case analysis (`match`) is a later surface slice")
title: "Surface `if` + general `match` for lu-kb-successor — sort-directed elaboration onto the verified term-`ite` and the kernel `Match`"
status: PROPOSED — Phase-1 (`if` + prelude `ite` postulate + emitter edit) landable now; `match`/Phase-2 native-emit gated on the VIR retarget
references:
  - adsmt-ir-lukb/src/{ast,parser,elab,lexer}.rs (surface; the slice-7 data/fn precedent to mirror)
  - adsmt-ir/src/{term,check,reduce}.rs (kernel Match/Elim; check.rs:138-144 exhaustiveness gate; reduce.rs:143-152 totality guard)
  - adsmt-ir-lower/src/lower.rs (hoist_term_ite :270-289; lower_match :649-703; datatypes.rs:223 → #331 CLOSED)
  - verus air/src/lukb.rs (ExprX::IfElse fallback to close) + vir/src/ast_simplify.rs:544-589 (Rust match → nested if desugar; check_ast_flavor asserts no AIR Match)
  - term-ite-lifting-verification/src/ite_lift.rs (atom-duplication Verus-verified 8/0)
  - DOC CORRECTION requested: LUKB_SUCCESSOR_SURFACE.md:434-441 still frames datatype-Match as "#331 gated"; it is CLOSED (verdict-complete for non-param/non-indexed Prop-valued matches)
---

> **verus-fork decisions (confirmed by the owner, 2026-07-03):** (1) **guards = INCLUDE** in v1
> (they ride the proven term-`ite` path and are the only way to match Int/Real literals);
> (2) **non-exhaustive = strict hard-error** (the Rust-faithful default). So Asks §8.6 and §8.7
> below are our **firm recommendation**, not open questions — we'd only want your ack or a
> soundness objection. Everything else in §8 is a genuine ask.
>
> **Provenance.** This proposal was produced by a grounded multi-lens design workflow (3 design
> lenses — Rust-faithful / Erlang-faithful / minimal-kernel-fit — + an adversarial soundness pass),
> reading the real `adsmt-ir-lukb` / `adsmt-ir` / `adsmt-ir-lower` sources. The line anchors are
> from that reading; flag any that have since moved.

# Adversarial review of the three candidate designs, and the best-of-breed selection

Before the proposal proper, the soundness verdict on each candidate, on the axes the review demanded. The synthesized design below takes the intersection of what survives attack.

**The one decision that is soundness-*forced*, not stylistic (all three agree, correctly):** a `if`/2-arm-`true`/`false` conditional whose *result* is a first-order value (Int/Real/uninterpreted) must elaborate to the `ite` prelude constant and lower via `hoist_term_ite` atom-duplication (`lower.rs:270-289`), **never** to a 2-branch `Match`/`Elim` over a `Bool` inductive. This is not a preference: as a `Match` the motive is value-valued ⇒ *data-valued* ⇒ abstains at `lower.rs:658-661` (`data_valued_match_abstains`, `solve.rs:276`); as an `Elim` it abstains unconditionally at `lower.rs:253-255`. The atom-duplication path is the *only* route that yields a value-level verdict, and it is Verus-verified 8/0 (`ite_lift.rs`: `lift_preserves_sat:323`) and green e2e (`solve.rs:55-72`). Any design that routed bool-`if` through the #331 datatype path would be a regression to `Unknown`; none does.

**Exhaustiveness (the central soundness gate).** The kernel enforces `minors.len() == ind.ctors.len()` with each minor positional to its constructor and *no* default/wildcard branch (`check.rs:138-144`). All three designs correctly conclude: a well-typed kernel `Match` is exhaustive-by-construction, so the *surface* must make every accepted match total before handing it down, and a genuinely non-exhaustive match must degrade to a hard elaboration error or a refuse-to-build `Unknown` — never a fabricated minor. All three are sound here; two fail-safes sit below the elaborator (a padded/under-length `Match` fails the `check.rs:138-144` length gate → `BadElim`; failing that, reduction stays *stuck* via the totality guard `reduce.rs:143-152` → `Unknown`, never a panic, never a wrong answer).

- *rust-faithful §6* — bucket→order→total, wildcard expanded across remaining constructors, non-exhaustive → hard error (preferred) or `Unknown`. Sound. Adopted.
- *minimal §6* — identical stance, cleanest statement of the invariant ("the surface never emits a kernel term whose missing constructors are filled by a fabricated value"). Adopted verbatim as the contract spine.
- *erlang-faithful §6* — same strict default, **plus** an opt-in permissive "`:badmatch`-skolem terminal": fill an uncovered branch with a *fresh, axiom-free* symbolic constant of the branch type, provenance-tagged `:badmatch`. **Adversarial finding: this is sound but heavier.** A single fresh constant with no defining axiom is the weakest possible term — it can never *add* a contradiction, so it can never fabricate `unsat`; all its occurrences are equal to each other (correct partial-function semantics, congruence-safe); for a Prop-valued branch it is a free boolean the SAT layer can flip either way ⇒ any goal depending on the branch stays underivable ⇒ sound `Unknown`/`sat`. **But** it mutates the kernel `Env` (postulating a fresh const per uncovered branch), it *requires* the provenance tag to report honestly, and a counterexample that drives the scrutinee into the uncovered branch may look like a spurious `sat` to the user (a fidelity, not soundness, concern). Verdict: keep as an explicitly-deferred, opt-in mode for partial functions; **strict-reject is the v1 default.**

**Guards.** rust-faithful and erlang-faithful include guards; minimal defers them behind "the match-compiler." Adversarial finding: minimal *overstates* the cost — guards folded into the *per-constructor* minor body (`C(x) if g => e1, C(x) => e2` ⟶ `minor_C = λx. ite(g, e1, e2)`) are a *local* right-fold over the arms reaching that constructor in source order; they do **not** require a nested-pattern compiler, and the `ite` they emit rides the already-proven term-`ite` path. The real soundness hazard both including designs handle correctly: **a guarded match is not exhaustive by construction.** The kernel gives one total minor per constructor; a constructor reached only by guarded arms with no unguarded backstop is genuinely non-exhaustive. The sound rule (adopted) is *syntactic*: a constructor bucket is total iff its last contributing arm is unguarded (or a wildcard/binder catch-all covers it). We **never** attempt semantic guard-completeness (undecidable) and **never** silently drop the last guard to force totality. Verdict: **include guards** (they unlock Int/Real literal patterns — otherwise impossible, since Int/Real are not finite-constructor inductives — via the `x if x = n` desugar, and they ride the verified path), staged as a cleanly-separable sub-slice, under the syntactic-backstop contract.

**`if` ⇔ `match` equivalence.** `if c then a else b ≡ match c { true => a, false => b }` must hold. Adversarial finding: the clean, sound reading is that `true`/`false` are the **Prop prelude constants** postulated in `Elab::new()` (`elab.rs`), the `if` condition is a **Prop** (SMT-`Bool` = `Prop`), and a `true`/`false`-pattern match over a Prop scrutinee is a **Prop-literal match desugared directly to `ite(c,a,b)`** — it never declares or touches a `Bool` *inductive*. rust-faithful's "route by scrutinee-sort → the same `ite` builder" realizes this; erlang-faithful's "`is-Variant`-guarded `if`-chain" framing is slightly off for the Prop case (it implies a `Bool` inductive with `is_true` discriminants, which the prelude does not ship — `theory.rs:123` installs only Int/Real/Nat/WNat). The equivalence is then *definitional* and costs nothing. Adopted from rust-faithful.

**Nested / or- / @-patterns.** erlang-faithful supports nested patterns by surface expansion into an inner `case`. Adversarial finding: this is kernel-fittable (each inner match is a flat, well-typed `Match`) but the *elaborator* must then implement a real first-match pattern-match compiler with correct fall-through — precisely where provers historically get exhaustiveness/reachability wrong, a **soundness** risk. rust-faithful and minimal defer nesting so that every arm is a single flat `match_template` instantiation and exhaustiveness stays a trivially-checkable syntactic property. Verdict: **defer nested/or/@ in v1** (sound workaround: user writes an explicit inner `match`); flat constructor patterns only.

**Kernel-fit.** All three emit `Match` (never `Elim`/`Fix`) for v1 and reject anything the kernel `Elim` can't type-check; `Elim`/`Fix` (structural recursion) is deferred (abstains at `lower.rs:253-255`; `Fix` also needs a decreasing-argument analysis absent from the four IR files). Adopted.

**Lexer/token.** erlang-faithful correctly found `->` already exists as `Tok::Arrow` (`lexer.rs:51`, tokenized `:223`), so a clause arrow *could* reuse it at zero cost — but `->` already means `Type::Arrow`, so reuse leans on grammar-position disambiguation. rust-faithful/minimal add a fresh `=>` (one arm in the longest-first ladder at `lexer.rs:183-234`, next to `->` at `:223`) — unambiguous and Rust-familiar. For a proposal *from verus-fork* (a Rust frontend), the Rust-shaped `match e { pat => body }` with `=>`, and ML-style `if c then a else b` (mirroring how `Let … in` bounds its body), is the most reviewable. **Adopted: `=>`, keywords `if`/`then`/`else`/`match`, guards reuse the `if` keyword** (Rust-faithful `pat if g => body`), a 4-keyword + 1-operator reservation — the minimal set.

Net best-of-breed: the **rust-faithful skeleton** (sort-directed split, `match {…=>…}` shape, flat patterns, `if`-guards, hard-error-or-`Unknown` exhaustiveness), sharpened by **minimal's** kernel-fit discipline and one-prelude-postulate framing and its crisp non-fabrication invariant, plus **erlang-faithful's** two genuinely additive contributions: the confirmed *absent* `ite` postulate as the load-bearing bridge, and the sound (but deferred) `:badmatch` permissive mode.

---

# Surface `if` + general `match` for lu-kb-successor

*A proposal from verus-fork to adsmt.*

## 1. Motivation

The lu-kb-successor surface today has **zero conditional or case forms** — `ast.rs:107-141` has no `If`/`Match` and there is no `Pattern` type; the `Item::Data` doc comment (`ast.rs:31-32`) already anticipates "case analysis (`match`) is a later surface slice." We propose exposing **both** `if` and a general `match` at the surface, and we deliberately leave the *internal lowering* of each as adsmt's freedom. The design turns on one observation that the ground reports make unavoidable:

- **`if` folds in as a pattern-match special case, not a separate primitive.** `if c then a else b` is exactly `match c { true => a, false => b }` where `true`/`false` are the two Prop prelude constants; both must denote a value and both must ride the **term-`ite` atom-duplication** that is already Verus-verified and green (`lower.rs:270-289`, `ite_lift.rs`).
- **`match` future-proofs the Phase-2 datatype retarget.** The kernel already has the eliminator nodes (`Elim`/`Match`, `term.rs:344-350`), the lowerer already has the tester+selector encoding with the #331 verdict-gate **closed** (`lower.rs:649-703`; `congruent_selector_reductions`, `datatypes.rs:223`), and the emitter already renders native `data` decls (`lukb.rs:66-105`). The only missing piece for genuine datatype case-analysis is the surface term and its elaboration — which is what this proposal adds, ahead of the VIR producer that will eventually feed it.

Exposing both, with `if` as a folded-in match case, means one surface, one soundness contract, and a clean seam for the Phase-2 native-datatype path — while `if` delivers value today.

## 2. Surface grammar for `if` and `match`

Both forms are keyword-led prefix terms parsed in `unary()` (`parser.rs:517-568`) alongside the existing `Forall`/`Exists`/`Let`/`Solve` arms — the exact precedent for "keyword, then parse full `term()` sub-parts." Layout is delimiter-based (braces + commas), not indentation-sensitive, consistent with `data N = C0(f:T) | C1` and `fn f(x:T):U = body`; the surface has no off-side rule and we import none.

```
term        := … | if_term | match_term            # new unary()-level alternatives
if_term     := 'if' term 'then' term 'else' term    # 'else' mandatory: an if is an expression, must denote a value
match_term  := 'match' term '{' arm ( ',' arm )* ','? '}'
arm         := pattern ( 'if' term )? '=>' term     # optional guard reuses the 'if' keyword
```

The `,`-separated arm loop with optional trailing comma is the direct analogue of the `while self.eat(&Tok::Pipe)` ctor loop at `parser.rs:98-107`. The optional guard reuses the fn-body optionality idiom `let g = if self.eat(&Tok::If) { Some(self.term()?) } else { None };` (mirroring `let body = if self.eat(&Tok::Eq) {…}` at `parser.rs:95`), followed by `expect(&Tok::FatArrow)`.

**Lexer wiring** (`lexer.rs`), each a two-edit change through the single `keyword()` choke-point (`lexer.rs:63-86`) + an `enum Tok` variant (`lexer.rs:11-61`):
- Reserve `if`, `then`, `else`, `match` — 4 keyword arms + 4 `Tok`s. Guards reuse `if`; no `case`/`of`/`when` needed.
- Add `=>` (`Tok::FatArrow`) as a multi-char operator in the longest-first ladder (`lexer.rs:183-234`, next to the `->` handling at `:223`). (`->`/`Tok::Arrow` already exists at `lexer.rs:51`; we do **not** overload it, keeping the clause arrow lexically distinct from `Type::Arrow`.)
- **Source-compat cost, disclosed:** keywords are non-contextual/fully reserved, and `keyword()` also feeds `ident_needs_quote` (`lexer.rs:113-123`), so `if`/`then`/`else`/`match` thereafter require backtick-quoting to be used as identifiers. This is the minimal 4-keyword reservation.

**Parser wiring:** add `if`/`match` arms to `unary()` (`parser.rs:517-568`); add `Tok::If` and `Tok::Match` to `starts_term()` (`parser.rs:216-233`) so a conditional/match can open a `fn … = body` block or a nested operand.

## 3. Pattern grammar + v1 scope

```
pattern   := '_'                                   # wildcard
           | ident                                 # binder OR nullary-ctor — resolved in elab
           | ctor_pat                              # constructor pattern (flat)
           | scalar_lit                            # Int / Real literal (see guard desugar)
ctor_pat  := ident '(' pat_arg ( ',' pat_arg )* ')'
pat_arg   := '_' | ident                           # v1: wildcard or fresh binder only (flat)
scalar_lit:= INT | REAL                            # true/false are Prop-literal patterns, see §4a
```

Pattern parsing reuses the `ctor()`/`ctor_field()` **two-token-lookahead idiom verbatim** (`parser.rs:136-165`): an ident, and if the next token is `(` it is a `ctor_pat`, else a bare name. The bare-name var-vs-nullary-ctor ambiguity is resolved in **elab** (Rust-faithful): a name is a nullary-constructor pattern iff it resolves to a constructor of the scrutinee's inductive, else a fresh binder — the same "is this the self-recursive name?" resolution `elab_field_type` already performs (`elab.rs:317-322`).

**v1 IN (each elaborates with the existing kernel `Match`, no new kernel work):**

| Form | Kernel-fit rationale |
|---|---|
| Wildcard `_` (arm-level) | Catch-all, *expanded* across the remaining constructors (kernel has no default; §6). |
| Wildcard `_` (sub-position) | A fresh, unused λ-binder in the minor telescope. |
| Binder `x` (arm-level) | Catch-all that also binds the scrutinee (= `_` plus a `Let`). |
| Binder `x` (sub-position) | One λ per non-parameter ctor arg — exactly the `match_template` shape (`inductive.rs:275,467-475`). The core faithful case. |
| Constructor `C(x0,…,xn)` (flat) | 1:1 with one kernel minor. |
| Nullary ctor / `true` / `false` | Empty λ-telescope ⇒ minor is just the body. `true`/`false` are Prop-literals → §4a. |
| Int/Real scalar literal `n` | Not a datatype match (Int/Real aren't finite-ctor inductives). Desugars to an equality **guard** `x if x = n => body` — see guards below. |

**v1 DEFERRED (each needs machinery absent from the four IR files / kernel — named, not invented):**

- **Nested patterns** (`Cons(Cons(h,t), r)`): the kernel minor binds only *immediate* ctor args as a flat λ-telescope (`inductive.rs:275`); nesting requires a real first-match pattern-match compiler with correct fall-through, which the elaborator has no machinery to reuse (elab report §4, "this is the hard part"). Compiling it wrong is a *soundness* risk (dropped/duplicated cases). **Sound workaround:** bind the sub-scrutinee and write an explicit inner `match`. Keeping arms flat makes exhaustiveness a trivial syntactic check.
- **Or-patterns** (`A | B => body`): would break the positional `minors[j] ↔ ctors[j]` 1:1 the checker enforces (`check.rs:138-144,177-184`). Soundly addable later as pure surface arm-duplication *before* constructor-bucketing.
- **`@`-bindings** (`x @ C(..)`): desugar to `Let x = <major> in <body-with C(..)>` using the existing `Let` node; deferred only to keep v1 binding uniform.
- **Ranges, slices/arrays, refs, struct-field `{f: p}`, rest `..`**: no kernel or surface analog. (Struct-field could later map to the `Ctor` named-selector field `ast.rs:45`; positional binding suffices for v1.)

**Guards (recommended IN, as a cleanly-separable sub-slice).** Surface `pattern if g => body`. Recommendation: **include**, because (a) their lowering is the *already-proven* term-`ite` path, (b) they are the *only* way to match Int/Real literals (via `x if x = n`), which are otherwise impossible since Int/Real are not finite-constructor inductives, and (c) with the syntactic-backstop rule (§6) exhaustiveness stays a *syntactic* check. The elaborator *buckets* all arms reaching a constructor `C`, in source order, and right-folds them into that constructor's single minor body as a nested `ite` over the guards, terminating in the bucket's unguarded backstop: `C(x) if g1 => e1, C(x) => e2` ⟶ `minor_C = λx. ite(g1, e1, e2)`; each inner `ite` is a term-`ite` (§4a). A constructor whose only arms are guarded, with no unguarded/wildcard backstop, is **non-exhaustive** (§6) — we never fabricate a default `ite` tail. If adsmt prefers a truly minimal first cut, guards (and literal-via-guard) are the natural second sub-slice, landing after bare flat `match`.

## 4. Elaboration to the kernel `Elim`/`Match`

Both forms elaborate through `elab_term(ctx: &mut Vec<(String,K)>, …)` (`elab.rs:417-467`) with the push/pop de-Bruijn discipline that `Let` and the quantifiers already use, and both need new arms in the two whole-tree walkers `subst_surface` (`elab.rs:939-965`; pattern-bound vars **shadow** like the `Let`/binder logic at `:948-962`) and `collect_ticks` (`elab.rs:1075-1116`).

**Prelude prerequisite (confirmed absent — the one load-bearing bridge).** `ite` is *named* in the `elab.rs:50` comment but is **not** postulated in `Elab::new()` (`elab.rs:47-75` postulates `true/false/not/and/or/=/exists/nop` + `install_arith` only). It must be postulated, spelled exactly `"ite"` so the lowerer recognizes it (`lower.rs:274,:452`):

```
ite : Π(T:Type). Prop → T → T → T
```

This is a **prelude postulate, not a kernel change**; the lowerer already assumes the `ite` head exists (`find_hoistable_ite`, `try_prelude "ite"`).

### 4a. `if c then a else b` (and every `true`/`false` Prop-literal match) → term-`ite`

`S::If(c,a,b)` arm, mirroring `S::Let`:
1. Elaborate `c` at **Prop** sort (SMT-`Bool` = `Prop`; `true`/`false` are the Prop prelude constants — no `Bool` inductive is declared or touched).
2. Elaborate `a`, `b`; reconcile the two branch sorts with `unify_sorts` (`elab.rs:752-761`) — the same numeric-lattice merge `elab_bin`/`Neg` use (`elab.rs:436-447`) — to a common result type `T`.
3. Emit the **`ite` prelude application** `K::apps(K::cnst("ite"), [T, c, a, b])` — *not* a `Match`.

A literally-written `match c { true => a, false => b }` with a Prop scrutinee is detected as a Prop-literal match and routed to this **same** builder. This makes `if c then a else b ≡ match c { true => a, false => b }` a *definitional* identity, and keeps every conditional off the `Bool`-inductive/#331 path.

### 4b. Datatype `match e { … }` → kernel `Match`

`S::Match` arm. The elaborator gains its one genuinely new capability — **constructor-arity readback** (the datatype path today stops at `declare_inductive`, `elab.rs:121`, and never reads ctor arities). Grounded in the real `Term::mtch(ind, motive, minors, major)` signature (`term.rs:344-350`) and `check.rs` requirements:

1. **`major` + `ind`.** `major = elab_term(ctx, e)`; infer/whnf its type; `as_const_app` gives head `ind` and spine. **Do not pass params/indices positionally** — the checker recovers them from `major`'s inferred type (`check.rs:146-158`); the elaborator's sole obligation is that `major` has an inductive head with `n_params + n_indices` spine entries. If the head is `Prop` (a `true`/`false` match) → route to §4a instead.
2. **Constructor list + arities.** Query `env.inductive(ind).ctors` (`env.rs:118-160`) for the constructor list and per-ctor non-parameter arities.
3. **Result sort.** Elaborate each arm body under its extended `ctx`; reconcile via `unify_sorts` → common `T`. (A *value*-typed `T` will abstain in lowering, §5 — sound `Unknown`, not an elab error.)
4. **`motive`.** `motive = λ(indices…). λ(x:I params indices). T` — non-dependent (ignores its binders). Must land in a `Sort`; kept Prop/Bool-valued so the Prop large-elimination bar (`check.rs:172-176`) is respected automatically.
5. **`minors` — order + telescope.** Produce **exactly one** minor per constructor, in `ind.ctors` **declaration/admission order** (`inductive.rs:91-95`; `minors[j] ↔ ctors[j]`; `check.rs:138-144,177-184`). Bucket + guard-merge + wildcard-expand the surface arms into that order (§3, §6), rejecting missing/duplicate/extra/unknown-ctor arms. Each `minors[j] = λ(a0:A0)…λ(a_{m-1}:A_{m-1}). body_j` — **one λ per non-parameter ctor arg** (the IH-free `match_template`, `inductive.rs:275,467-475`); nullary ctors ⇒ empty telescope. Push the pattern binders onto `ctx` with the extend-then-pop discipline of `elab_quant` (`elab.rs:560-564`); the de-Bruijn body sees ctor args as `Bound(m-1)…Bound(0)`.
6. **Emit** `Term::mtch(ind, motive, minors, major)`. The elaborator does **not** hand-build method types — it gets *count and order* right and lets `check` compare each minor against `match_type` up to convertibility (`check.rs:177-184,291-301`). ι-reduction then computes: `ind.match m… (c_j …) ⟶ m_j …` (`iota_match`, `reduce.rs:172-180`).

**v1 emits `Match`, never `Elim`/`Fix`.** There is no surface recursion yet; `Elim` abstains at lowering (`lower.rs:253-255`), and `Fix` needs a decreasing-argument analysis absent from the IR. The reduction totality guard (`reduce.rs:143-152`) is the final safety net: even a malformed under-length `Match` stays *stuck* ⇒ `Unknown`, never a panic, never a fabricated verdict.

## 5. Non-binding internal-lowering suggestion (adsmt's choice)

How the surface lowers is **adsmt's freedom**; this is the sort-directed routing that maximizes verdicts given the current lowerer, offered as a suggestion, not a requirement.

| Surface | Result / scrutinee | Suggested internal encoding | Verdict today? |
|---|---|---|---|
| `if` / `true`/`false` match | first-order value (Int/Real/uninterp) | term-`ite` → `hoist_term_ite` atom-dup `and(or(¬c,F[a]), or(c,F[b]))` (`lower.rs:270-289`) | **Yes** — Verus-verified 8/0; the *only* route to a value verdict |
| `if` / `true`/`false` match | Prop (both branches formulas) | `ite` prelude → `try_prelude "ite"` `(c→a)∧(¬c→b)` (`lower.rs:452-469`) | Yes |
| datatype `match` | Bool/Prop-valued, non-param, non-indexed | kernel `Match` → `lower_match` tester+selector (`lower.rs:649-703`) | **Yes** — #331 gate CLOSED (`datatypes.rs:223`; `solve.rs:317`) |
| datatype `match` | value-valued (Int/Real/datatype) | data-valued → abstains (`lower.rs:658-661`) | `Unknown` (sound-incomplete) |
| datatype `match` | parametric / indexed | abstains (`lower.rs:667-669`) | `Unknown` |
| `Elim`/`Fix` (recursion) | any | abstains (`lower.rs:253-255`) | `Unknown` — v1 never emits these |

The load-bearing routing rule: **route by result/scrutinee sort, not by surface keyword.** A bool-`if` over a first-order value and a value-producing `match` belong on term-`ite`; a datatype-scrutinee Bool/Prop `match` belongs on the kernel `Match`.

**Non-binding future lead (out of v1):** a *value-producing* datatype `match` could be routed to a verdict by desugaring to `is-Variant`-guarded `ite` over the discriminants with field reads as selectors (`ite(is_C0(x), e0[a:=sel0(x)], ite(is_C1(x), e1, ⊥))`) — exactly what Verus's own `ast_simplify` already does upstream (§7). This makes the surface `match`, the kernel `Match`, and the Verus emit path agree on one `is-Variant`-guarded-`if` normal form. It needs the tester/selector prelude (`{ctor}!sel{i}`, `lower.rs:685-695`) exposed at the elaboration level *and* the datatype theory's discriminant-exhaustiveness to retire the `⊥` tail; until then, value-producing datatype matches remain sound `Unknown`.

## 6. Soundness / exhaustiveness contract

The invariant, stated plainly and non-negotiably: **the surface never emits a kernel term whose reachable cases are decided by a fabricated value.** Every accepted `match` is either provably total or degrades to error/`Unknown`. Concretely:

1. **The kernel is the enforcement point.** `infer_eliminator` requires `minors.len() == ind.ctors.len()`, positional to constructors, with **no wildcard/default** (`check.rs:138-144`). A well-typed kernel `Match` is therefore exhaustive by construction. The surface must make every accepted match total *before* handing it down.
2. **Bucket → order → total-per-constructor.** Arms are bucketed by constructor in **declaration order**; a wildcard `_ => d` or binder `x => d` is *expanded* into the missing constructors' minors and into the fall-through of guarded buckets. This is how a match that "looks non-exhaustive" becomes a total kernel `Match`.
3. **Guarded buckets — syntactic backstop only.** A constructor bucket is total **iff its last contributing arm is unguarded** (or a wildcard/binder catch-all covers that constructor). We **never** attempt semantic guard-completeness (undecidable) and **never** drop a guard to force totality. A constructor reached only by guarded arms with no backstop is non-exhaustive (case 5).
4. **Reject malformed arm sets** at elaboration: duplicate, extra, or unknown-constructor arms.
5. **Genuinely non-exhaustive** (a reachable constructor has no total minor and no backstop): **never fabricate a branch** — no `unreachable`, no arbitrary default, no reuse of a sibling body. Two sound outcomes, prefer (a):
   - **(a) Hard elaboration error** "non-exhaustive match: constructor `C` uncovered" — the strict, most Rust-faithful default (v1 recommended).
   - **(b) Refuse to build the `Match`, degrade the whole term to abstain/`Unknown`** — the solver returns `Unknown`, never a verdict.
   Both preserve the invariant; both are additionally fail-safe below the elaborator (a padded/under-length `Match` → `BadElim` at `check.rs:138-144`, or stuck at `reduce.rs:143-152` → `Unknown`).
6. **Redundant / unreachable arms** (shadowed by an earlier arm or a wildcard, under first-match): **warn** (as Rust/Erlang do) but keep — the fold never reaches them, so it is sound.
7. **Scrutinee-sort the solver can't decide** (parametric/indexed datatype, or a value-producing case): the kernel `Match` may type-check, but lowering abstains (`lower.rs:658-669`) ⇒ sound `Unknown`, never a fabricated verdict.
8. **Optional permissive mode (opt-in, deferred): the `:badmatch` skolem terminal.** For a deliberately partial match, an uncovered branch (or an all-guarded chain's fall-through) may be filled with a **fresh, unconstrained, axiom-free** constant of the branch type, provenance-tagged `:badmatch` (cf. the `:goal-negation` tagging, commit `0e9a9e3dd`). Soundness: a fresh axiom-free constant is the weakest possible term — it can never *add* a contradiction, so it can never fabricate `unsat`; all its occurrences are mutually equal (correct partial-function semantics, congruence-safe); a goal depending on that branch stays underivable ⇒ sound `Unknown`, and a counterexample driving the scrutinee there is a *real* reachable partial-match (honest `sat`). **Caveats that keep this out of the v1 default:** it postulates a fresh const into the `Env` per uncovered branch, it *requires* the `:badmatch` provenance to report honestly ("`Unknown`/`sat` because a `:badmatch` branch was reachable"), and such a counterexample can look spurious against the user's intended totality. Strict-reject (case 5a) is the v1 default; this mode is a sound, clearly-labeled extension for partial functions.

**`if`-specific soundness:** because `if`/`true`-`false`-match always elaborates to the `ite` prelude const (§4a) and never to a `Bool` `Match`/`Elim`, it never touches the exhaustiveness machinery at all — its two branches are total by construction and its verdict comes from the Verus-verified atom-duplication. No regression hazard.

## 7. Staging + verus-emit implications

**Phase-1 (landable now — one prelude postulate + one emitter line, plus the `if` elaboration).**
- AIR's `ExprX` has **no `Match`** — `IfElse(Expr,Expr,Expr)` is the sole conditional (`air/src/ast.rs:208`). Rust `match` is *fully* desugared upstream in VIR `ast_simplify` (`Match → nested If`, `ast_simplify.rs:544-589`; patterns → `IsVariant` tests + `FieldOpr` selectors, `patterns.rs:112-145`), and `check_ast_flavor.rs:13,25-26` *asserts* no `Match` survives. By the time anything reaches the lukb emitter, every match is already `ite( Apply(is_Variant_C,[x]), body, … )` with field reads as `Apply(field_selector,[x])`.
- Consequence: the Phase-1 emit change is a **single line** — replace `air/src/lukb.rs:225` `ExprX::IfElse(..) => Err("if-then-else term")` (which today degrades *every* conditional, including every desugared match, to a `# fallback (...)` comment via `render_item`, `lukb.rs:474-476`) with a real `if c then a else b` rendering of the surface `if` designed here. The `is_Variant_C(x)` / `field(x)` applications inside it already render through the existing `ExprX::Apply` path (`lukb.rs:245-257`) as call-syntax and need nothing new.
- **verus emits `if` now.** So a Rust `match` is fully covered *today* by emitting `if` + the existing apply path; the native `match` surface is not exercised by Verus at all yet. **The current `lukb.rs:225` `IfElse` fallback closes the moment the surface `if` lands** — and it needs the §4.0 `ite` postulate to reach the verified `hoist_term_ite` path.

**Phase-2 (native lukb `match` emit — gated on the VIR retarget).** A native lukb `match` is emitted only if the VIR→SST→AIR producer is retargeted to carry native datatypes + a native match/case term instead of the current `is_Variant`+selector+`ite` desugaring. No such term exists in AIR `ExprX` today, so **while the emitter reads AIR it must never fabricate a native `match`.** The datatype-*declaration* half of Phase-2 is already present (`lukb.rs:66-105` renders native `data` decls); only the scrutineeing term stays desugared. The `match` surface + kernel `Match` lowering designed here are therefore **ready ahead of the producer** and cost zero kernel work when it lands.

**What can land now vs later:**
- **Now:** `ite` prelude postulate (§4a); surface `if` (lexer/parser/elab + `subst_surface`/`collect_ticks`); the `lukb.rs:225` emitter edit. This delivers every Verus conditional *and* every already-desugared Rust `match` as sound term-`ite`.
- **Now, but consumed only by hand-written / third-party lukb sources (not Verus):** the `match` surface + flat patterns + datatype `Match` elaboration; verdict-complete today for non-param/non-indexed **Prop/Bool-valued** datatype matches (#331 CLOSED — note the stale "#331 gated" framing at `LUKB_SUCCESSOR_SURFACE.md:434-441` should be corrected).
- **Deferred:** guards + Int/Real literal patterns (cleanly-separable sub-slice); nested/or/@-patterns; value-producing datatype-match verdicts (the §5 future lead); structural recursion (`Elim`/`Fix`); the opt-in `:badmatch` permissive mode; the Phase-2 native-`match` emit path.

## 8. Ask

1. **Postulate `ite : Π(T:Type). Prop → T → T → T`** in `Elab::new()` (`elab.rs:47-75`), spelled exactly `"ite"` — confirmed absent; without it the `if` elaboration won't type-check and won't reach `hoist_term_ite`. *(Prelude postulate, not a kernel change.)*
2. **Confirm the sort of the `if` condition and of `true`/`false`** is `Prop` (SMT-`Bool` = `Prop`), so `if c then a else b ≡ match c { true => a, false => b }` is definitional and never declares a `Bool` inductive. If the prelude's `true`/`false` are *not* `: Prop`, tell us the intended condition sort.
3. **Add constructor-arity readback** (`env.inductive(ind).ctors`) to the elaborator — the one new capability the datatype `match` needs (the surface today stops at `declare_inductive`).
4. **Accept the token/keyword plan:** reserve `if`/`then`/`else`/`match` (guards reuse `if`); add `=>`/`Tok::FatArrow` (not overloading `->`/`Tok::Arrow`). Confirm the ident-backtick-quoting cost (`lexer.rs:113-123`) is acceptable.
5. **Confirm v1 emits `Match` only** (never `Elim`/`Fix`), and that value-producing / parametric / indexed datatype matches are sound `Unknown` in v1 (abstain), not elaboration errors.
6. **Rule on guards for v1:** we recommend **include** (proven `ite` lowering; unlocks Int/Real literal patterns; syntactic-backstop exhaustiveness) as a separable second sub-slice. Confirm include-now vs defer-to-sub-slice-2.
7. **Rule on the exhaustiveness default:** we recommend **strict hard-error** (§6 case 5a) for v1, with refuse-to-`Unknown` (5b) and the opt-in `:badmatch` mode (case 8) as explicitly-deferred options. Confirm.
8. **Confirm the non-binding lowering (§5) is adsmt's to decide** — we propose sort-directed routing but do not require it.
9. **Correct the stale doc:** `LUKB_SUCCESSOR_SURFACE.md:434-441` still frames datatype-`Match` as "#331 gated"; per `lower.rs:639-648` + `datatypes.rs:223` + green `solve.rs:317`, it is verdict-complete today for non-param/non-indexed Prop-valued matches.

— filed by verus-fork (윤병익 / Claude Opus 4.8) / `backend-pluggable` / 2026-07-03
