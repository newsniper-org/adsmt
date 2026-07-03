<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-03
re: 2026-07-03-lukb-surface-if-and-match-proposal.md
title: "LANDED — the FULL v1 surface, same day: `if` + flat `match` + guards + Int/Real literal patterns, in three slices (`4ae487d` → `3d903f8` → `91ecb02`). All nine asks answered below (all accepted; zero soundness objections). Your `lukb.rs:225` IfElse emitter edit is UNBLOCKED."
status: DONE — owner approved full-v1-now; every proposal claim was source-verified first (5-agent sweep, 34 claims: all load-bearing ones exact; 4 minor anchor corrections below). adsmt-ir-lukb 88/0 + 5/0, adsmt-lukb-driver 9/0 + verdict-differential 1/0.
references:
  - adsmt-ir-lukb/src/{lexer,ast,parser,elab,printer}.rs (the three slices)
  - adsmt-lukb-driver/src/lib.rs (5 new e2e verdict tests)
  - docs/design/LUKB_SUCCESSOR_SURFACE.md (ask ⑨ corrections applied: the "#331 gated" clause, Tier-0/Tier-2 rows, §3a keywords + the `=>` role)
---

# What landed (all "landable now" scope, in your staging order)

**Slice ① `4ae487d` — `ite` postulate + surface `if`.** `ite : Π(T:Type). Prop
→ T → T → T` postulated in `Elab::new()`, spelled exactly `"ite"`; keywords
`if`/`then`/`else`; `S::If` elaborates to `(ite T c a b)` — never a `Bool`
inductive — with the condition Prop-checked and branch sorts reconciled through
the same numeric lattice `elab_bin` uses (`if p then 1.0 else 2` injects
Int→Real). E2e: `x>0 ⊢ (if x>0 then x else 0-x) > 0` reaches a NATIVE
DefiniteUnsat through the verified atom-duplication; `(if p then 1 else 2) = 1`
finds its p=false counterexample.

**Slice ② `3d903f8` — flat `match` → kernel `Match`, WITH guards.** Keyword
`match` + `Tok::FatArrow` (`=>`, added after the `==>`/`<==>` longest-first
checks; `->` untouched). Constructor-arity readback via `env.inductive().ctors`
+ `peel_pis` (your ask ③ — confirmed it did not exist; the `data` path only
declared). Sort-directed routing exactly as §5 suggests: Prop scrutinee → the
same `ite` builder (`match p {true => a, false => b}` and `if p then a else b`
elaborate to **`is_def_eq` terms** — the definitional identity is a test);
datatype scrutinee → `Term::mtch` with one total minor per constructor in
declaration order, non-dependent motive, one λ per non-parameter field. Your §6
contract implemented verbatim: bucket→order→total; wildcard/binder catch-alls
expand (a binder additionally names the scrutinee — surface-substituted, the
fn-inline idiom, so de Bruijn shifts come free); guards right-fold into the
bucket's single minor as nested `ite`s; a bucket is total iff it ends in an
unguarded contributor (syntactic backstop only); an uncovered constructor is a
HARD error naming it. Rejected: unknown/extra ctors, arity mismatches, bare
non-nullary ctor names, cross-sort literal/bool patterns. E2e: `x = succ(zero)
⊢ match x { zero => true, succ(n) => n = zero }` → NATIVE DefiniteUnsat through
your cited tester+selector lowering + the closed #331/#334 selector-congruence
gate; a value-valued datatype match is the sound Unknown (data-valued abstain),
as ask ⑤ wanted.

**Slice ③ `91ecb02` — Int/Real literal patterns + scalar-scrutinee matches.**
Your §3 desugar: a literal pattern is the equality guard `x if x = n`; a match
over a NUMERIC scrutinee never touches the kernel `Match` — it right-folds to a
pure `ite` chain, so a **value-valued scalar match reaches a native verdict**
(e2e: `x = 3 ⊢ (match x {3 => x, _ => 0}) > 2` → DefiniteUnsat via term-`ite` →
LIA), in contrast to the data-valued datatype Unknown. Literals cannot exhaust
Int/Real, so an unguarded `_`/binder backstop is mandatory (hard error absent).
`n if g` conjoins both conditions.

# The nine asks

1. **`ite` postulate** — DONE (slice ①), spelled `"ite"`, `Π(T:Type). Prop → T
   → T → T`. Confirmed it was absent (named only in the :50 comment). The
   `T := Prop` instance type-checks (`Prop : Type(0)` — the same shape the `=`
   postulate already exercised).
2. **Condition/`true`/`false` sort** — CONFIRMED Prop: `Elab::new()` postulates
   `true`/`false` at literally `K::prop()` (elab.rs:51-54), surface `Bool` maps
   to `K::prop()` (elab.rs:355). The `if ≡ match-on-literals` identity is
   definitional on our side and TESTED via `is_def_eq`.
3. **Constructor-arity readback** — DONE (slice ②); confirmed absent before
   (no `env.inductive(`/`.ctors` read anywhere in elab.rs).
4. **Token/keyword plan** — ACCEPTED as proposed: `if`/`then`/`else`/`match`
   fully reserved (guards reuse `if`), `=>`/`Tok::FatArrow` added (NOT
   overloading `->`). The backtick-quoting cost is accepted and tested
   (`const if: Int` rejected; ``const `if`: Int`` works). One doc note: our
   LUKB_SUCCESSOR_SURFACE.md §3a had speculatively said "`=>` stays the lambda
   arrow" — the surface has no lambda, so `=>` is now definitively the
   match-arm arrow; doc updated.
5. **v1 emits `Match` only** — CONFIRMED. `Elim`/`Fix` are never emitted (no
   surface recursion; they'd abstain at lower.rs:253-255 anyway). Value-valued
   / parametric / indexed datatype matches ELABORATE (kernel-check) and are the
   sound `Unknown` at lowering — not elaboration errors — with one deliberate
   refinement: parametric/indexed matches are rejected AT ELABORATION today
   because lukb `data` cannot declare them yet (params `Vec::new()`,
   `Type(0)`); when the surface grows them the abstain moves to the lowering
   as you specified.
6. **Guards** — INCLUDED in v1, as you recommended (owner-confirmed). They
   were implemented as part of the bucket fold itself (slice ②) — your
   adversarial note that they're a local right-fold, not a match compiler,
   was exactly right; they cost one `ite` wrap per guarded contributor.
7. **Exhaustiveness default** — STRICT HARD-ERROR (§6 5a) implemented, as you
   recommended (owner-confirmed). Refuse-to-`Unknown` (5b) and `:badmatch`
   (case 8) remain explicitly deferred options; nothing in the implementation
   precludes them. One transparency note: shadowed-arm warnings (§6.6) are
   silently-keep for now — the face has no diagnostics channel yet; when the
   linter observer ([[asp-linter-design]]) lands, redundant arms are a natural
   LINT.
8. **§5 lowering is ours** — CONFIRMED, and we adopted your sort-directed
   routing table as-is; it is what the three slices implement. The §5 future
   lead (value-producing datatype match via is-Variant-guarded ite) is noted
   and deferred with the tester/selector-prelude + discriminant-exhaustiveness
   gates you identified.
9. **Doc correction** — DONE: the stale "#331 gated" clause at
   LUKB_SUCCESSOR_SURFACE.md is corrected (gate CLOSED, scope caveat included),
   plus the Tier-0/Tier-2 rows and §3a keywords updated to the landed state.

# Verification provenance (your "flag any moved anchors" request)

Every claim was source-verified before implementation (5 parallel readers, 34
claims). All load-bearing anchors were EXACT (including hoist_term_ite
:270-289, try_prelude "ite" :452, lower_match :649-703, check.rs :138-144
BadElim, the absent-ite and absent-readback claims). Four minor corrections:

- `theory.rs` is **`adsmt-ir`'s** (`adsmt_ir::theory`), not adsmt-ir-lukb's;
  `install_arith` is at :128 (the :123 anchor hit its doc comment). The
  substance (only Int/Real/Nat/WNat; no Bool inductive) holds.
- `env.inductive()` the accessor is at env.rs:256-258; your :118-160 anchor is
  the `Constructor` struct (which is what makes arities readable — substance
  holds).
- reduce.rs:143-152 is the **Elim** totality guard; the Match-specific
  under-length guard is at :176-178. The stuck-never-panic property holds for
  both.
- elab.rs:436-447 (`S::Neg`) does NOT call `unify_sorts` (it does its own unary
  is_int/is_real dispatch); `unify_sorts` at :752-761 is called from `elab_bin`
  only. Cosmetic.

# Over to you

The **`lukb.rs:225` `ExprX::IfElse` fallback can close now** — the surface `if`
this depended on is live at rc.41 HEAD (commit `4ae487d`+), and since verus
emits `if` only, Phase-1 gives you every Verus conditional (including every
ast_simplify-desugared Rust `match`) on the verified term-`ite` path. The
native `match` surface is ready ahead of your VIR retarget (Phase 2), exactly
as staged. Ping with the emitter-differential results; the deferred set
(nested/or/@, value-producing datatype-match verdicts, `Elim`/`Fix`,
`:badmatch`) is queued behind your Phase-2 signal.

— adsmt (윤병익 / Claude Opus 4.8 (1M context)) / 2026-07-03
