# The lu-kb-successor surface — design (the non-S-expr unified verification surface)

**Status:** design / RFC (2026-06-26). Supersedes the mislabelled "Phase 1 =
SMT-LIB-term-shaped item-structured surface" sketch in the
`verus-emits-lukb-surface` memory, which was **not** lu-kb (it emitted
`(axiom …)`/`(goal …)` S-expressions). The actual lu-kb language is **not
S-expression based**; this document designs its successor as a real
indentation/keyword surface.

## 0. Why this exists

The strategic goal (user / verus-fork owner, 2026-06-26): have Verus emit the
**lu-kb-successor unified surface** to adsmt instead of flattening to SMT-LIB,
because AIR→surface is less lossy than AIR→SMT-LIB (the goal/assume distinction
and typed definitions survive). For that to be real, the surface has to be the
*actual* lu-kb-successor language — a layout/keyword syntax — not S-expressions
wearing item names.

The surface is the **third concrete face of the typed CIC kernel
[`adsmt-ir`]**, beside:

- `adsmt-ir-smtlib` — the SMT-LIB-3.0 face (classical / theory, `open` modality)
- `adsmt-ir-asp`    — the typed-ASP face (closed-world / stable models, `def`)

All three elaborate to the same kernel and are re-checked by the same trusted
admitters. The lu-kb-successor is the *human-and-Verus-facing unified* face: it
spans both worlds (it has theory terms AND Horn rules) in one layout syntax.

## 1. The key finding — lu-kb's surface *syntax* is already ~70 % of the way there

> **Scope of the claim (review-corrected, 2026-06-26):** "~70 %" is about the
> reusable surface **syntax/layout**, not the engine. The expression *parser* is
> a flat single-binop fold (no precedence — §3b box), `&&`/`||` don't exist (only
> `and`/`or`), term-level `not`/unary-`-` are new, and the lu-kb→kernel consumer
> today lifts only `Fact` atoms — so the theory-term **elaborator is net-new**.

The existing lu-kb language (`adsmt-parser-lu-kb`) is **already** a rich
layout/keyword language with an infix expression grammar. Reusing it (rather
than inventing) is the whole strategy. lu-kb today has:

| lu-kb construct | concrete syntax | AST |
|---|---|---|
| layout block items | `rule head(x: T):` ⟶ indented body | `Item::{Rule,Constraint,Abduce,Fact,Fn,…}` |
| typed args | `x: Int`, `xs: List(Int)` | `TypedArg { name, type_ann }` |
| **infix operators** | `==` `!=` `<` `>` `<=` `>=` `+` `-` `*` `/` `and` `or` | `Expr::BinOp(_, BinOp, _)` |
| function application | `f(a, b)` | `Expr::Call` |
| negation | `not p(x)` | `BodyExpr::Not` |
| body `let` | `let y = e` | `BodyExpr::Let` |
| conditions | `x > 0` as a body line | `BodyExpr::Condition(Expr)` |
| named sorts / params | `Int`, `BitVec(32)`, `List(T)` | `TypeExpr::{Named,Parameterized}` |
| enums / datatypes | `enum Color:` ⟶ ctors; `data` | `EnumDef`, `DataDef` |
| HKT kinds | `Type -> Type`, `Slot(n)` | `KindExpr` |
| modules | `import`/`export`/`as` | `Import`/`Export` |

Lexer keywords today: `fact rule abduce constraint fn let type data relation
instance import export where not and or explain as overlap enum`. Operators:
`:` `<-` `=>` (FatArrow) `->` (RightArrow) `|>` (pipe) plus the binops above,
layout via `Indent`/`Newline`.

**So the infix theory-term *shape* the user wants (`x + y = y + x`, `x > 0`)
already parses** — the successor makes `=` the canonical equality (keeping lu-kb's
`==` as a legacy alias, §3a) and adds the heads below. It is an *extension*, not a
rewrite.

## 2. What's missing (the three additions)

To carry Verus's theory-laden verification conditions, the successor adds
exactly three things on top of lu-kb:

### 2a. Quantifier expressions

Verus VCs are full of `∀`/`∃`. lu-kb's `Expr` has lambdas but no quantifiers.

```
forall x y: Int. x + y = y + x
exists k: Int. n = 2 * k
forall x: Int. x in xs ==> x >= 0          # with a guard
```

Grammar: `forall <binders> . <expr>` / `exists <binders> . <expr>`. Per the
user's chosen syntax, a binder **group** shares a type via space-separated
names (`x y: Int`), and groups are comma-separated:

```
binders ::= group ( "," group )*
group   ::= ident+ ":" type             #  x y: Int ,  k: Bool
```

The body extends as far right as possible (lowest precedence, like Lean/Coq),
terminated by the `.`. **Triggers** (the matching-loop control that makes or
breaks MBQI) attach as an optional annotation — see §3d.

#### 2a′. Bounded & guarded quantifiers (sugar — user proposal, 2026-06-26)

Two readability sugars over the core `forall binders. body`. Both desugar to the
core form, so they cost the elaborator nothing past the parser.

**Membership-bounded.** `forall x in C. body` / `exists x in C. body`, with the
element type **inferred** from `C` (annotate via `forall (x: T) in C. …`):

```
forall x in xs. x >= 0     ⟺  forall x: elem(xs). x in xs ==> x >= 0
exists x in xs. x > 0      ⟺  exists x: elem(xs). x in xs and x > 0
```

(`forall` guards with `==>`, `exists` with `and`.) Integer **range** bounds work
at Tier 0/1 — `forall x in 0..n. p(x)` ⟺ `forall x: Int. 0 <= x and x < n ==> p(x)`;
collection membership is Tier 2 (needs the Seq/Set theory).

**Refinement-constrained binders — and the constraint/antecedent distinction
(user, 2026-06-26).** A binder group may carry, **before the `.`**, a list of
*refinement constraints* that narrow the **quantification domain**. These are a
**typing-level** concept — a refinement type `{x: T | …}` — and are kept
**distinct from a body-level logical antecedent**, which lives **after the `.`**
in the proposition (written with `==>`/`<==>`). In real mathematics these are
different things ("for all odd `n > 5`, P" — *domain* — vs "for all `n`, if
`odd(n)` then P" — *hypothesis*); the surface preserves whichever the author
wrote and never silently normalises one into the other.

```
# `> 5` is a DOMAIN CONSTRAINT (refinement, before `.`);
# `odd(n)` is the BODY ANTECEDENT (logic, after `.`):
forall (n: Nat) > 5. odd(n) ==> p(n)

exists (a b c: Nat) >= 2, prime(a), prime(b), prime(c). a + b + c = n

# general REFINEMENT-TYPE form — an explicit brace literal `{ names : T | φ }`,
# φ an arbitrary Bool term over the binders (the comparison `(n:T) op rhs` above
# is its single-predicate special case; they elaborate to the SAME kernel term):
forall { n: Int | n > 5 }. p(n)
forall { a b: Int | a < b }. q(a, b)

# general form:  QUANT binder ("," binder)* "." body
#   binder  ::=  "(" names ":" T ")" constraint*    (paren + cmp/pred sugar)
#             |  "{" names ":" T "|" pred-term "}"   (brace refinement type)
#             |  names ("in" lo ".." hi | ":" T)     (range / plain)
#   constraint  ::=  cmp e            (e.g. > 5 ;  applies to EACH name)
#                 |  "," pred-term    (e.g. , prime(a) ;  a Bool term over the binders)
#                 |  "in" collection  (membership / range, §2a′ above)
```

**Semantics.** The bounded-quantifier lowering is the standard
`∀ x:{T|C}. φ  ⤳  ∀ x:T. C ==> φ` and `∃ x:{T|C}. φ  ⤳  ∃ x:T. C ∧ φ`. The brace
form `{x:T | φ}` is the general realisation of this `{T|C}` refinement type (the
predicate `φ` is carried verbatim as the guard `C`); the parenthesised comparison
`(n:T) op rhs` is the special case `{n:T | n op rhs}`. The lowering polarity
(`∀ → ⟹`, `∃ → ∧`) is pre-verified — see
`docs/design/REFINEMENT_TYPES_AND_GENERIC_CONSTRAINTS.md`.

**Refinement types in type position + generic `'p` (LANDED).** Beyond quantifier
binders, `{v: T | φ}` is also a first-class **type** (`Type::Refine`) usable in
`const` / `fn`-param / `fn`-return position. A `const c: {v:T|φ}` postulates
`c: T` plus the fact `φ[v:=c]`. A predicate `φ` may name **generic predicate
parameters `'p`** (a leading single quote — `is_tick_ident`; concrete `q` has no
quote, the parse-time disambiguation). A `fn` collecting `'p`s from its
refinements is **predicate-polymorphic**: each `'p` binds implicitly at the head
as `Π('p: T→Prop)` (the body checks once with `'p` abstract), the param
refinements are preconditions and the return refinement a postcondition, and the
contract `∀'p⃗.∀x⃗. (⋀ φᵢ) ⟹ ψ(g('p⃗,x⃗))` is a **goal** for a definition / a
**trusted axiom** for a signature. The constraint-preserving lambda
`{v:T|'p v} -> {v:T|'p v}` is exactly this. See
`docs/design/REFINEMENT_TYPES_AND_GENERIC_CONSTRAINTS.md` §7.

> **Corrected by review (kernel-fit, 2026-06-26).** The adsmt-ir kernel
> `TermKind` (Sort/Bound/Const/App/Lam/Pi/Let/Elim/Match/Fix) has **no
> subset/refinement (`{x:T|C}` / Σ) constructor**, and a `Pi`/`Lam` binder
> carries only a domain type — no constraint slot. So the constraint/antecedent
> split is **a surface-AST + pretty-printer concern only**; the **kernel term is
> the lowered `C ==> φ` / `C ∧ φ`**. A cert therefore round-trips the lowered
> form unless the surface AST is serialized alongside it. Preserving the split
> "in the kernel" would require a real Σ/Subtype kernel addition — out of scope
> for Phase 1b (see §9). This is *not* a soundness issue (the lowering is sound);
> only the intent-preservation claim is downgraded to surface-level.

The user's space-separated form (`prime(a) prime(b) prime(c)`) parses
unambiguously here (lu-kb application is always parenthesized `f(x)`, never
juxtaposed), but the **comma** form is the recommended spelling; both parse.

### 2b. The proof-obligation item layer

lu-kb has `rule`/`fact`/`constraint` (the closed-world Horn world) but no way
to state a *classical entailment obligation*. The successor adds three layout
items mirroring AIR `StmtX`/`DeclX`:

```
axiom add_comm:                            # trusted hypothesis (∈ H), DeclX::Axiom
  forall x y: Int. x + y = y + x

assume positives:                          # VC path condition (∈ H), StmtX::Assume
  x > 0 and y > 0

goal sum_pos:                              # the obligation, StmtX::Assert
  x + y > 0
```

`H = (axioms ∪ assumes)`; the consumer checks `H ⊨ goal` by refuting
`H ∧ ¬goal`. The goal carries the obligation **un-negated** — adsmt forms `¬G`
itself, so the goal/H split is structural (this is the real, native version of
the Phase-0 `:goal-negation` tag — no tag needed). A discharged `goal` is
`unsat(H ∧ ¬G)`.

**Sequent sugar** (the user's `|-`): a one-line obligation may inline its
hypotheses with a turnstile:

```
goal sum_pos:
  x > 0, y > 0 |- x + y > 0
```

is exactly `assume (x > 0 and y > 0)` then `goal (x + y > 0)`. The turnstile
form is sugar; the block form is canonical.

### 2c. The theory operators / types Verus needs (staged — the "theory cliff")

The infix grammar covers linear-Int + Bool + EUF + (dis)equality already. The
remaining theory vocabulary is **staged** (the memory's "theory cliff"):

- **Tier 0 (now):** `Int`, `Bool`, uninterpreted sorts/functions, `=`/`!=`,
  `< > <= >=`, `+ - *` (and `*` by a literal = linear), `and or not`,
  `==>` (implies), `<==>` (iff), `if c then a else b` (ite), `let x = e in b`
  (term-let), `∀`/`∃`, enums + simple datatypes with selectors/discriminators.
- **Tier 1 (later):** `Real` and `/` (real division), `div`/`mod` (Int
  Euclidean), nonlinear `*`.
- **Tier 2 (later):** `BitVec(n)` + the bv operators (`&` `|` `^` `~` `<<`
  `>>` `bvadd` …), `Array(K, V)` + `select`/`store`, full **recursive**
  datatypes. (The non-recursive `match` surface itself LANDED 2026-07-03 —
  flat patterns + guards + literal patterns, elaborating to the kernel
  `Match`, verdict-complete for Prop/Bool-valued non-parametric matches;
  recursion/`Elim`/`Fix` stays later.)

A surface that hits an unrepresentable construct **falls back to SMT-LIB**
(never silently drops it) — the differential oracle stays SMT-LIB throughout
bring-up.

## 3. Concrete syntax (the spec)

### 3a. Lexical additions

New keywords: `forall exists axiom assume goal in then else if match`. (`let`
already exists; reused for term-`let … in`.) New operator tokens: `==>`
(implies), `<==>` (iff), `|-` (turnstile), `.` (quantifier-body separator —
already a char, promoted to a token after a binder list). `=>` (FatArrow) is
the **match-arm clause arrow** (`pat (if g)? => body`, landed 2026-07-03);
implication is the distinct `==>` to avoid the collision. `if`/`then`/`else`/
`match` are fully reserved — backtick-quote to use them as identifiers.

**Equality spelling.** The **canonical** spelling is a single `=`
(`x + y = y + x`), disequality `!=`. lu-kb's `==` is **kept as a legacy alias**
(lexed to the same `Eq` operator) so existing/`==`-style sources keep parsing —
**non-breaking**. The pretty-printer always emits the canonical `=`. `=` stays
unambiguous because binding only occurs in the keyworded `let ident = term in …`
form (after `let ident`, `=` is the binder; everywhere else `=` is equality), so
there is no parse conflict.

**Quoted identifiers (slice 6 — added for the Phase 1c producer).** A symbol
that a bare identifier cannot hold — special characters (`%`, `~`, `@`, `!`,
`.`), an empty name, or a keyword spelling — is written backtick-quoted:
`` `%%location_label%%0` ``, `` `lib.is_even` ``, `` `forall` `` (the *symbol*
named `forall`, not the keyword). The content is any character except a
backtick, taken verbatim as one `Ident` token (so the parser is unchanged — a
quoted ident flows through anywhere a bare ident is accepted). **Backticks, not
SMT-LIB `|…|`, are the delimiter** — `|…|` would collide with the `|-`
turnstile (`a |- |b c|` is ambiguous). The pretty-printer re-quotes exactly the
names that would not lex back bare (`lexer::ident_needs_quote`), so the
round-trip is stable. This is what lets the AIR→lukb producer (§5) render
Verus/AIR's internal mangled names **faithfully** rather than mangling them
(which would be *more* lossy than SMT-LIB — the opposite of the surface's
purpose).

### 3b. The term grammar (the centrepiece)

Precedence, loosest → tightest (all left-assoc unless noted):

```
term    ::= "forall" binders "." term
          | "exists" binders "." term
          | "let" ident "=" term "in" term
          | "if" term "then" term "else" term
          | iff
iff     ::= implies ( "<==>" implies )*
implies ::= disj ( "==>" disj )*           # right-assoc
disj    ::= conj ( ("or" | "||") conj )*
conj    ::= cmp  ( ("and" | "&&") cmp )*
cmp     ::= add ( ("=" | "!=" | "<" | ">" | "<=" | ">=") add )?    # non-assoc
add     ::= mul ( ("+" | "-") mul )*
mul     ::= unary ( ("*" | "/") unary )*
unary   ::= ("not" | "-") unary | app
app     ::= atom ( "(" term,* ")" )* | atom ( "." field )*
atom    ::= ident | int | real | string | "(" term ")"
binders ::= typed_arg ( "," typed_arg )*   # reuses lu-kb's typed-arg list
```

Quantifiers / `if` / `let-in` / `==>` / `<==>` are the new heads.

> **Corrected by review (grammar + faithfulness, 2026-06-26).** This ladder is a
> **new precedence-climbing parser**, NOT a superset of the real lu-kb expression
> parser. lu-kb's `parse_expr_rest` is a **flat single-binop fold** that consumes
> exactly one operator and returns — so `a + b + c` does **not** parse today,
> there is no `*`-over-`+` precedence, and comparison is single-shot. Phase 1b
> **replaces** that parser with the ladder above; this *changes which strings
> parse and how they associate* (chained/mixed-precedence terms that error or
> mis-associate today start parsing). Also new (not present in lu-kb's `Expr`):
> term-level `not` and unary `-` (lu-kb's `not` is body-line only); `&&`/`||`
> are dropped — lu-kb has no such tokens (use the `and`/`or` keywords). The
> lexical additions `..` (range), `|-` (turnstile), and contextual keywords are
> in §3a. See §9.

### 3c. The item grammar (extends lu-kb `Item`)

```
item ::= <existing lu-kb items>            # rule / fact / constraint / fn / enum / data / …
       | "axiom"  name? ":" INDENT term+ DEDENT
       | "assume" name? ":" INDENT term+ DEDENT
       | "goal"   name? ":" INDENT obligation DEDENT
obligation ::= ( term "," )* term "|-" term     # sequent sugar
             | term                              # H comes from preceding axiom/assume items
```

Multiple `term` lines in an `axiom`/`assume` block are conjoined. A module is a
sequence of declarations (sorts/fns/datatypes — reuse lu-kb `data`/`enum`/`fn`
+ a bare `sort S` and `fn f(x: Int): Int` *signature* form) followed by
`axiom`/`assume`/`goal` items.

### 3d. Triggers (soundness-critical, opt-in)

Because MBQI completeness/termination hinges on triggers, a quantifier may
carry an explicit pattern annotation. Proposed surface (mirrors the body-guard
style, avoids `:pattern` S-expr keywords):

```
forall x: Int. f(x) >= 0   trigger f(x)
forall x: Int. f(x) >= 0   trigger { f(x) }      # multi-pattern: { p1, p2 }
```

No `trigger` ⟹ the kernel/solver picks (Miller / auto), exactly as today.

## 4. Worked example — a Verus VC, three ways

A Verus obligation `requires x > 0, y > 0 ensures x + y > 0` with an in-scope
commutativity lemma, in the **successor surface**:

```
sort Int                                  # (built-in; shown for completeness)
axiom add_comm:
  forall a b: Int. a + b = b + a
goal sum_positive:
  x > 0, y > 0 |- x + y > 0
```

The same content **today on the SMT-LIB face** (what adsmt actually consumes):

```
(declare-const x Int) (declare-const y Int)
(assert (forall ((a Int) (b Int)) (= (+ a b) (+ b a))))
(assert (> x 0)) (assert (> y 0))
(assert (! (not (> (+ x y) 0)) :goal-negation))
(check-sat)
```

Both elaborate to the same kernel obligation. The successor is strictly more
informative (the `goal` item is typed; no positional/`:goal-negation` heuristic
needed) and human-readable.

## 5. Elaboration & architecture

- **New crate `adsmt-ir-lukb`** (sibling of `adsmt-ir-smtlib` / `adsmt-ir-asp`),
  own lexer/parser (extend the existing `adsmt-parser-lu-kb` grammar) →
  `adsmt-ir` kernel terms. Trust boundary identical to the other faces: untrusted
  elaborator, re-checked by the kernel admitters; a face bug yields `FaceError`
  or `Unknown`, never a manufactured verdict.
- **Producer (verus-fork) — LANDED Phase 1c (`748fc08fb`, branch `backend-pluggable`).**
  A `-V emit-lukb` flag dual-emits each AIR obligation to a `.lukb` log
  ALONGSIDE the canonical `.smt2`, in the lu-kb-successor surface. AIR
  `DeclX::Sort`→`sort`, `Const`/`Var`→`const`, `Fun`→`fn` (synthetic param
  names), `Axiom`→`axiom`; the assertion tree's `StmtX::Assume`→`assume`,
  `StmtX::Assert`→`goal` (the **un-negated** goal); `ExprX`/`TypX`→the term
  grammar (Tier-0/1 native; Tier-2+ → `#` fallback **comment** carrying the
  reason, never a silent drop). Self-contained renderer `air/src/lukb.rs` (no
  adsmt dep); arbitrary AIR symbols backtick-quoted (slice 6). The structural
  (parse/elaborate) differential is `adsmt-ir-lukb`'s `check_lukb` example.

  > **Two implementation choices that DIVERGE from the original review sketch
  > (both validated empirically, 2026-06-26):** (1) **solver-independent**, not
  > "adsmt path only" — the `.lukb` log is an inert artifact, so gating it on the
  > solver would needlessly limit it; it emits under any `-V`/default z3. (2) The
  > hook is the **post-`block_to_assert` final query** (`Context::check_valid`),
  > NOT the pre-fold block the review worried about. `block_to_assert` does fold
  > body path-conditions into the goal antecedent (`Assume(Q); Assert(P)` →
  > `goal: Q ==> P`), but that is **semantically faithful** and simpler, and the
  > USER-meaningful structure still comes through cleanly: Verus encodes a
  > function's `requires` as query-local `DeclX::Axiom`s, so they render as
  > separate `axiom:` hypotheses, and the `ensures` is the un-negated `goal:`.
  > Confirmed: `requires x>0,y>0 ensures x+y>0` → `axiom: \`x!\` > 0` /
  > `axiom: \`y!\` > 0` / `goal: Add(\`x!\`, \`y!\`) > 0`. Control-flow stmts
  > (`Switch`/`Breakable`/`Havoc`/`Assign`/`Snapshot`/`Break`) — eliminated by the
  > lowering before the final query; a stray survivor emits a `#` fallback comment.
- **Consumer (adsmt):** `lu-smt` (or a face entry) parses the successor surface →
  kernel → existing solve/abduce/lint pipeline. `goal` routes to the entailment
  check (assume H, refute G). NB the existing `adsmt-shim-lu-kb` consumer lifts
  only `Fact` atoms today — the `Expr`/`BinOp`/quantifier/type → kernel
  elaborator is **net-new** Phase-1b work, not a wiring-up of an existing path.
- **Differential (mandatory through bring-up):** SMT-LIB stays the canonical wire
  and the z3-differential oracle; the successor run's verdict is asserted equal to
  the SMT-LIB run's on the 54 vstd obligations + corpus + randomized z3-diff
  before any successor verdict is trusted. Coverage gaps fall back to SMT-LIB,
  never silent-drop.

## 6. Staging (real Phase 1 and beyond)

- **Phase 1a — language design (this doc) + the term/item grammar frozen. DONE.**
- **Phase 1a′ — adsmt-ir Int/Real theory slice (PREREQUISITE, user-chosen §9c).
  SUBSTANTIALLY DONE — re-measured 2026-08-30.** The `theory` prelude carries
  `Int.{add,sub,mul,div,mod,neg,abs,lt,le,gt,ge}` (11) and
  `Real.{add,sub,mul,div,neg,lt,le,gt,ge}` (9), and `adsmt-ir-lower` decides
  them (`int_linear_entailment_unsat`, `int_bound_box_unsat`,
  `ground_arith_eq_*`, …). The `Nat`/`WNat` postulated sorts and their
  injections (`nat2int`/`wnat2int`/`nat2wnat`) exist with the positivity
  collapse and 11 tests (`adsmt-ir-lower/tests/refinement_collapse.rs`).
  **Still absent: a kernel refinement/subset CONSTRUCTOR** — `TermKind` is
  still `Sort/Bound/Const/App/Lam/Pi/Let/Elim/Match/Fix`, so the
  domain-constraint / body-antecedent split stays a surface concern exactly as
  §2a′'s review said. That is an intent-preservation gap, not a soundness or a
  capability one, and it did NOT gate Phase 1b in practice.
- **Phase 1b — `adsmt-ir-lukb` parser + elaborator for Tier 0 + Tier 1. LANDED**
  (Int/Bool/EUF/quant/enums **plus** Real, real `/`, Int `div`/`mod`), with a
  round-trip pretty-printer, triggers carried as out-of-band metadata, the
  asymmetric `exists` lowering, and the top-level `const x: T` decl form.
  The crate is lexer + parser + ast + elab + printer + verdict, and it takes
  refinement types `{v: T | φ}` in type position plus predicate-polymorphic
  `'p`. **Measured on the 209-row verus corpus: parses 209/209, elaborates
  209/209** — every hypothesis and goal a kernel-checked `Prop`.
- **Phase 1c — verus AIR→successor printer for Tier 0 + Tier 1. LANDED**
  (verus-fork `748fc08fb`; `air/src/lukb.rs` + `-V emit-lukb`). Dual-emit + the
  structural (parse/elaborate) differential (`adsmt-ir-lukb`'s `check_lukb`
  example); validated end-to-end on a real `verus -V emit-lukb` run (full
  prelude → 301 well-formed lukb items, parses 100%, 5 `# fallback` comments at
  the Tier-2 boundary). **The verdict-differential is no longer gated —
  re-measured 2026-08-30.** `adsmt-ir-lukb/examples/lukb_solve.rs` runs the
  whole native path (`elaborate → lower → adsmt-engine`) with no delegation
  anywhere, and decides **90 of the 209** obligations `unsat` against the
  delegation's 171. Cross-tabulated, the native verdict set is a strict SUBSET:
  there is no row where native claims `unsat` and the delegation does not, so
  the sweep surfaces no native false-UNSAT candidate. Full table and the
  abstain attribution:
  `adsmt-delegate/corpus-triage/2026-08-30-native-only-lukb-verdicts.tsv`.

  That number is the real answer to "how much does adsmt depend on delegation":
  **81 rows, not 171.** See `adsmt-delegate/DELEGATION_TRUST_REDESIGN.md` §S1.
- **Phase 1b slice 7 — `data` + `fn=body` (the Phase-2 surface). LANDED**
  (`adsmt-ir-lukb`): `data Peano = zero | succ(pred: Peano)` /
  `data Lst = nil | cons(head: Int, tail: Lst)` → kernel `declare_inductive`
  (non-parametric/non-indexed; named-or-positional fields; selector names are
  surface sugar — the solver lowering synthesizes positional `{ctor}!sel{i}`);
  and `fn f(x: T): U = body` → kernel `define` (`Modality::Def`, δ-unfolded at
  lowering) vs the signature-only `postulate`. Lexer `data` kw + `|`; a
  **recursive** `fn` body is rejected (the kernel `fix` is a later slice — the
  self-reference is a sound "unknown symbol"). New keyword `Nat`/`Int`/… stay
  reserved arith sorts (a datatype uses a fresh name). 6 tests; round-trips. This
  retires the verus AIR→lukb producer's `# fallback (datatypes)` once the
  producer is retargeted (Phase 2 proper).
- **Phase 2 — native datatypes/defs** (the actual trigger win: drop the
  box/unbox/height `:pattern` axioms), gated on kernel #317 + CIC→HOL #325
  (datatype-eliminator lowering: the `Match` lowering LANDED, **and the
  #331/#334 verdict gate is CLOSED** — the engine DECIDES non-parametric/
  non-indexed Prop/Bool-valued matches via selector congruence + the bounded
  DPLL(T) refinement loop, z3-differential-validated to a ~0.1% conservative
  false-sat residual) + faces-in-workspace (DONE, `0f9b007`) + a full A/B
  z3-differential. The lukb surface for it (`data`/`fn=body`) is slice 7 above,
  **and the surface `if`/`match` terms LANDED 2026-07-03** (the verus-fork
  proposal: `if` → the `ite` prelude → the verified term-`ite` lowering; flat
  first-match `match` with guards + literal patterns → the kernel `Match`,
  strict exhaustiveness); remaining = the **VIR producer retarget** (emit
  native datatypes + selectors instead of the box/unbox/height axioms).
- **Phase 3+ — Tier 2 theory** (BitVec / Array), recursive defs, and the
  **theorem-package** layer (§7).

### 6a. Where the native path actually stops (measured 2026-08-30)

With the face and the lowering both complete for this corpus, the 119
non-`unsat` rows are ENGINE abstains, not surface or lowering gaps. Attributed:

| blocker | rows | slice |
|---|---|---|
| an uninterpreted theory atom | 58 | N3 landed but does not reach these; needs the arrangement |
| the DPLL(T) refinement bound | 58 | **N5** — the block clause is the negation of the WHOLE model, so one round kills one model; a real core is needed |
| a quantifier still unreached | 3 | N4 took this from 58 to 3 |

Two slices have landed against these: **N3** (LinArith admits a UF-application
operand as a Nelson-Oppen interface variable — the native twin of the delegated
engine's #429) and **N4** (quantifiers are hoisted out of `and`/`⟹`/`∨` so the
instantiation loop reaches them). Neither moved the verdict count; N4 moved the
BLOCKER, which is how the N5 target was identified.

An ablation (`2026-08-30-n0-axiom-family-ablation.tsv`) showed that removing the
`has_type` and fuel axiom families — 19.5% and 37.1% of the corpus's 45,013
axioms — changes nothing at all, so the "recognise the structure to shrink the
search" slices have a ceiling of zero until N5 lands.

## 7. Theorem packages (build-time-proven axiom libraries — user proposal, 2026-06-26)

A **theorem package** is a lu-kb module whose obligations are discharged at
**package build time** (via the adsmt-emit package manager — the makepkg-style
build-script model, [`adsmt_emit_system`]). The build **fails** if any
obligation is not discharged; once built, the package's results import as
**trusted, cert-backed axioms** that downstream modules use without re-proving.
Two kinds of trusted proposition:

1. **`theorem name:` — machine-discharged.** The solver must prove it at build
   time (refute `¬G`); it produces an adsmt cert and the build **fails** on
   `Unknown`/`Sat`. The machine proof is the warrant.
2. **`postulate name: … cite "<ref>":` — externally-justified.** Admitted as a
   trusted axiom with a **mandatory provenance citation** (a published human
   proof the solver cannot re-derive). The citation is the warrant; there is no
   machine cert, but the trust anchor is recorded and auditable.

**Built-ins (performance).** `pow`, `mod`, `odd`, `prime` are kernel/theory
primitives (native rules, not user axioms that would blow up MBQI) — which puts
the celebrated number-theory statements in the Tier-0/1 expressible fragment.

**Built-in numeric types — strict `Nat` / `WNat` distinction (user directive,
2026-06-26).** `Nat` is the **positive** integers `{1, 2, 3, …}` (0 **excluded**);
`WNat` ("범자연수", whole naturals) is `{0, 1, 2, …}` (0 **included**). Choosing
`Nat` vs `WNat` *is* the soundness boundary in §7.2.

> **Corrected by review (kernel-fit, 2026-06-26).** The adsmt-ir kernel today has
> **no `Int`/`Real` theory at all** (the SMT-LIB face returns
> `unsupported("the Int theory is a later slice")`; integer literals are
> rejected) and **no subtyping/cumulativity/coercion**. So `Nat ⊂ WNat ⊂ Int` is
> *not* a kernel relation: `Nat`/`WNat`/`Int` must be **postulated sorts** with
> explicit total injection constants (`nat2int`, `wnat2int`, …) the elaborator
> inserts, and arithmetic (`+`, `pow`) lives at `Int` so every `Nat`-binder use is
> wrapped. **This makes all of §7's number-theory examples Tier-1 (Int-theory)
> work that does not exist yet** — they are *writable* in the surface but not
> solver-checkable, and the whole §7 layer is gated on the adsmt-ir Int slice
> (#317). See §9.

### 7.1 The soundness gate (why this is delicate)

A `postulate` is a **trust anchor**: a *mis-stated* postulate is a FALSE axiom,
and a false axiom makes the whole theory inconsistent — `⊥` becomes provable, so
*every* later "proof" is vacuous (catastrophic unsoundness). So a theorem
package's build gate must, beyond discharging the `theorem`s:

- run a **consistency check** — the postulates + built-ins must be jointly
  satisfiable (no `⊥`), reusing the vacuity linter's `SAT(axioms)` machinery
  ([`asp_linter_design`]). A package that proves `false` **fails the build**.
- pin every `postulate`'s **statement** to its citation for human review — the
  machine can verify internal consistency, but not that the statement *matches*
  the cited theorem.

### 7.2 Worked examples — and the subtleties the gate is for

**Fermat's Last Theorem** (Wiles 1995) is about **positive** integers — `0`
trivialises it (`(0, k, k)` solves `0ⁿ + kⁿ = kⁿ`). With the strict `Nat` (0
excluded), `x y z: Nat` already means `≥ 1`, so **the user's original `iff`
encoding is sound as written** — no positivity guard needed:

```
postulate fermat_last_theorem cite "Wiles, Ann. of Math. 141 (1995)":
  forall (n: Nat). n >= 3 <==> not exists (x y z: Nat). pow(x,n) + pow(y,n) = pow(z,n)
```

The `iff` cleanly captures both directions: `n < 3` (i.e. `n ∈ {1, 2}`) has
infinitely many positive solutions, `n ≥ 3` has none. **This is exactly where
`Nat` vs `WNat` matters:** declare the binders `WNat` instead and the trivial
`(0, k, k)` solution makes `∃` true for every `n`, falsifying the postulate —
the soundness-gate consistency check would reject it.

**Goldbach's weak conjecture** (Helfgott 2013) is an **implication**: every odd
`n > 5` is a sum of three primes. The *converse* is false — `8 = 2 + 3 + 3` is a
sum of three primes yet even — so an `<==>` is an unsound over-claim (independent
of `Nat`/`WNat`). It also shows the §2a′ split cleanly: `> 5` is the **domain
constraint** (which `n`), while `odd(n)` is the **antecedent** of the body
implication (a hypothesis about that `n`):

```
postulate goldbach_weak cite "Helfgott, arXiv:1312.7748 (2013)":
  forall (n: Nat) > 5. odd(n) ==> exists (a b c: Nat) >= 2, prime(a), prime(b), prime(c). n = a + b + c
```

Both lean on the §2a′ refinement-constrained quantifiers — **the two proposals
compose** — Fermat's soundness turns on the strict `Nat`/`WNat` typing (§8), and
Goldbach's on keeping the `> 5` *constraint* apart from the `odd(n)` *antecedent*.

### 7.3 Proof-object integrity seal — anonymized 512-bit hash (user proposal, 2026-06-26)

Every packaged proposition ships a **512-bit digest of its anonymized proof
object** as a tamper-evidence (위변조 방지) seal, bundled in the package manifest:

1. **Canonicalize ("anonymize") the proof object.** For a `theorem`, the proof
   object is its adsmt cert; the build normalizes it to a deterministic byte form
   — strip all *non-semantic / identifying* metadata (timestamps, host, absolute
   paths, prover-run nonces, machine env, nondeterministic ids), and canonicalize
   ordering via hash-consing — so the bytes depend **only on the proof's
   mathematical content**. (Anonymization is what makes the digest *reproducible*:
   an independent re-derivation of the same proof yields the same canonical object
   → the same digest, so the hash certifies the *proof*, not the run.) A
   `postulate` has no machine proof, so its sealed object is the canonicalized
   *statement + citation* record.
2. **Hash with a 512-bit BLAKE3 digest** over the canonical bytes (user pick).
   BLAKE3's default output is 256-bit, so the 512-bit seal uses its **extendable
   output (XOF) mode** — `finalize_xof` → read 64 bytes. BLAKE3 is fast,
   parallel/tree-hashed, length-extension-free, and an XOF by construction;
   512-bit (vs the existing SHA-256 AOT-sha) for long-lived collision resistance
   of a permanent axiom library.
3. **Bundle + verify.** The digest goes in the package manifest. A consumer
   re-canonicalizes the shipped proof object and re-hashes; any mismatch = the
   proof was **tampered/forged** → the package is rejected. The digest is also the
   proof's **content address**, dovetailing the existing content-addressed
   adsmt-emit store ([`adsmt_emit_system`]).

**Integrity vs authenticity.** A bare hash gives *integrity* + content-identity
(this is THE canonical proof of this statement, unmodified), **not** *authenticity*
(who produced it). For authenticity, sign the digest (e.g. Ed25519 over the
512-bit hash) — a recorded future extension, not Phase-1b.

## 8. Decisions

**Settled from the user's chosen syntax (2026-06-26):** canonical equality `=` /
disequality `!=`, with lu-kb's `==` kept as a **legacy alias** (non-breaking,
§3a); quantifier binders space-shared per type and comma-grouped (`forall x y:
Int, k: Bool.`, §2a); dot `.` quantifier-body delimiter; sequent turnstile `|-`
(§2b). Implication / iff = ASCII `==>` / `<==>` (no collision with the `=>`
lambda arrow).

**Also settled (user, 2026-06-26):**

1. **Name = "lu-kb"** — kept as the name; this is simply its next version. Crate
   `adsmt-ir-lukb`, verus flag `-V emit-lukb`.
2. **First-cut scope = Tier 0 + Tier 1** (Int/Bool/EUF/quant/enums **plus** `Real`,
   real `/`, and Int `div`/`mod`) for Phase 1b. Tier 2 (BitVec/Array/recursive
   datatypes) falls back to SMT-LIB until later.
3. **Item name optional** — a nameless `goal:` / `axiom:` / `assume:` is allowed
   and auto-numbered (`goal#0`, …) for cert/error provenance.
4. **Strict `Nat` / `WNat`** — `Nat = {1,2,…}` (0 excluded), `WNat = {0,1,2,…}`
   (0 included). *(Surface/spec level. Review-corrected: these are postulated
   sorts with explicit injections, NOT kernel subtypes — the kernel has no
   `Int`/subtyping yet; §7 built-ins + §9.)*
5. **Constraint vs antecedent are distinct levels** — a binder **refinement
   constraint** (`(n: Nat) > 5`, before `.`) vs a body **antecedent**
   (`odd(n) ==> …`, after `.`). *(Review-corrected: the split is preserved in the
   surface AST + pretty-printer ONLY; the kernel term is the lowered `C ==> φ` /
   `C ∧ φ` — the kernel has no `{x:T|C}` constructor; §2a′ + §9.)*

**Settled from the review (user, 2026-06-26):**

6. **Proof-seal hash = BLAKE3** (§7.3), 512-bit via its XOF mode (64-byte output).
7. **Scope = build the adsmt-ir Int/Real slice FIRST** (§9 option c) — Phase 1b
   does *real* Tier-0/1 once the kernel has the Int theory, rather than narrowing
   or routing arith to fallback. Couples to kernel #317; the immediate next work
   item is the adsmt-ir Int/Real theory + the `Nat`/`WNat` postulated sorts +
   injections, then Phase 1b.

## 9. Adversarial review (2026-06-26) — findings & the scoping decision

A 4-lens adversarial review (grammar / soundness / kernel-fit / faithfulness),
grounded in the real lu-kb parser + adsmt-ir kernel, ran before Phase 1b. Outcome:

**Grammar — Phase-1b spec refinements (no user decision; fixed in this doc):**
the term parser is **net-new precedence-climbing** (lu-kb's is a flat single-binop
fold — §3b box); add lexer tokens `..` (range), `|-` (turnstile), and make
`forall/exists/axiom/assume/goal/in/if/then/else` **contextual** keywords (they're
common identifiers today — `exists`/`in` appear in lu-kb's own tests — so
reserving them would break existing sources; "non-breaking" only holds if
contextual); drop `&&`/`||` (lu-kb has only `and`/`or`); disambiguate the
quantifier-`.` from field-access-`.` in the parser; give refinement constraints a
self-delimiting parse so the constraint-comma ≠ binder-group-comma.

**Soundness — gate framing corrected (no user decision):** the `SAT(axioms)`
consistency check is **one-sided** — it can REJECT on a found refutation, but
`Sat`/`Unknown` must NOT be read as "consistent" (treat Unknown as needs-human-
sign-off). It does **not** auto-catch the WNat-Fermat / Goldbach-`<==>`
mis-statements (those need witness instantiation the solver may miss; `pow(x,n)`
with symbolic `n` is undecidable and the gate abstains). **Citation-vs-statement
human review + machine-checkable ground spot-checks** (e.g. discharge Goldbach at
n=7,9,11 as `theorem`s) are the load-bearing controls. Pin the built-in
`prime/odd/pow/mod` semantics. The two worked theorems are mathematically correct
under strict `Nat`.

**Kernel-fit — the real gating reality (THIS is the decision):** the adsmt-ir
kernel has **no `Int`/`Real` theory** (the SMT-LIB face returns "the Int theory is
a later slice"), **no subtyping/coercion**, and **no refinement/subset (`{x:T|C}`)
constructor**. Consequences: (a) the constraint/antecedent split is surface-only
(done, Decision 5); (b) **all arithmetic — Tier-0 `+ - * < >` over Int as well as
Tier-1 Real/div/mod — is gated on the adsmt-ir Int-theory slice (#317), which does
not exist yet.** So the **scope decision (§8, decision 2) "Tier 0 + Tier 1" is not buildable
at Phase 1b** until that slice lands. Triggers can't ride the kernel `Π` (carry
out-of-band as solver metadata); `exists` lowers asymmetrically (→ a postulated
`Exists T (λ…)`, `T:Type0`); add a top-level `const x: T` decl form (§3c) for the
free VC variables.

**→ SCOPING DECISION — RESOLVED (user, 2026-06-26): option (c).** Build the
**adsmt-ir Int/Real theory slice first** (couples to kernel #317), then do Phase
1b with real Tier-0/1. Highest fidelity, largest work; no arith-fallback crutch.
So the **immediate next work item is the adsmt-ir Int/Real theory** (+ the
`Nat`/`WNat` postulated sorts with explicit injections, the `pow`/`mod`/`odd`/
`prime` built-ins, triggers-as-solver-metadata, the `exists` asymmetric lowering,
and the top-level `const x: T` decl form) — *then* the `adsmt-ir-lukb` parser +
elaborator.

## 10. The unified verdict surface (AFT impact, 2026-06-30) — design / RFC

**Why this section exists.** The 2026-06-30 *Approximation-Fixpoint-Theory*
adoption gave the two sibling faces a **richer, un-collapsed full-mode verdict**,
and they are now SHAPED DIFFERENTLY:

- **SMT face** (`adsmt-ir-smtlib` → OxiZ): a 5-level **precision lattice**
  `SatLevel { DefiniteSat, PossiblySat, Unknown, PossiblyUnsat, DefiniteUnsat }`
  with `meet`/`collapse` (`oxiz-solver/.../types.rs`), surfaced via
  `OutputMode { Z3Compatible (collapse → sat/unsat/unknown), Full (the 5 tokens) }`.
- **ASP face** (`adsmt-ir-asp`): a 3-valued **approximation pair** — the
  well-founded model `ThreeValued { true_atoms = L*, false_atoms = B\U*,
  undefined_atoms = U*\L* }` — surfaced via `AspOutputMode { Z3Compatible,
  Full }`, where Full returns the sound 3-valued *partial* verdict on
  over-budget programs instead of abstaining.

The successor is the **unifying** third face. So its verdict surface — still
unbuilt (today `adsmt-ir-lukb` stops at `Elaborated{env,hypotheses,goals}`; no
output-mode, no verdict type, no `solve`) — must now carry BOTH. This is a
*raised bar*, not a regression: the AFT supplies exactly the confidence/partiality
metadata that makes the successor **strictly less lossy than SMT-LIB** (§0), but
only once a unified verdict carries it back to the producer (Verus).

### 10.1 The type — a SEPARATED PRODUCT, not a fused lattice

```
enum LuKbOutputMode { Z3Compatible /*default*/, Full }

struct UnifiedVerdict {
    smt: Option<SatLevel>,        // present iff SMT obligations were solved
    asp: Option<AspVerdict>,      // present iff rule obligations were solved
}                                 // (AspVerdict = the relevant slice of Solution:
                                  //  consistent + stable + well_founded:ThreeValued)
```

**Reject a fused 9-level lattice.** The two lattices answer *different questions* —
`SatLevel` is **precision** (is this verdict confirmed?), `ThreeValued` is
**partiality** (which atoms are decided?). A fusion loses both. The separated
product matches `UNIFIED_VERIFICATION_GATE.md`'s "each paradigm explains itself"
principle: keep them side by side, project on demand.

`UnifiedVerdict::collapse() -> SolverResult` (tri-state) is the z3-compatible
projection: `smt.map(collapse)` ⊓ `asp.map(collapse)` under the same precision-meet
(`PossiblySat`-vs-`PossiblyUnsat` etc. → `Unknown`); a present `Definite*`/exact
side wins, two unconfirmed opposite sides → `Unknown`. Full mode renders both
sub-verdicts verbatim (the 5 tokens + the true/false/undefined partition).

### 10.2 Hybrid programs (the merge the doc previously left open)

A genuinely mixed obligation (SMT theory atoms `x+y>0` AND Horn rules
`q :- p, not r`) yields BOTH a `SatLevel` and a `ThreeValued`. The two halves are
DIFFERENT sub-problems whose **conjunction** is the whole — so `collapse()` is the
3-valued **Kleene conjunction** of the two collapsed sides, NOT a `meet` (`meet`
combines verdicts about the SAME formula; here `meet(DefiniteSat,DefiniteUnsat)`
would wrongly give `Unknown` instead of `Unsat`). Kleene AND: `Unsat` on EITHER
side ⇒ whole `Unsat` (a refutation of either sub-problem refutes the whole —
always sound); `Sat` is the identity (an absent side imposes no constraint);
otherwise `Unknown`. A both-`Sat` hybrid is reported `Sat` under the
disjoint-atom (jointly-satisfiable) assumption — a shared-atom joint-model check
is the refinement. Full mode keeps BOTH sub-verdicts so a consumer sees *which*
paradigm was undecided. (Implemented + unit-tested in
`adsmt-ir-lukb/src/verdict.rs`: `TriState::and`, `UnifiedVerdict::collapse`.)

### 10.3 The §5 verdict-differential, made precise

§5's gate ("assert the successor verdict == the SMT-LIB oracle on the 54 vstd
obligations + corpus + randomized z3-diff before any successor verdict is
trusted") must state the **representation** in which equality holds: equality
**after `collapse()` to tri-state**. Full mode preserves the extra
precision/partiality *soundly but unchecked* during bring-up (SMT-LIB has no
5-level/3-valued oracle to diff against). Until the differential passes, SMT-LIB
stays the canonical wire and lukb coverage gaps fall back to SMT-LIB (never a
silent drop) — unchanged from §5.

### 10.4 Threading requirements (what must change to build this)

1. `adsmt-ir-lukb`: add `LuKbOutputMode`, `UnifiedVerdict`, and
   `solve_with_mode(elab, mode) -> UnifiedVerdict` routing kernel goals through
   lowering→OxiZ (SMT obligations) and/or elaboration→`adsmt-ir-asp::solve_with_mode`
   (rule obligations). Do this **in `adsmt-ir-lukb`**, not in
   `adsmt-shims/adsmt-shim-lu-kb` (that crate is the *legacy* lu-kb→adsmt-core cert
   bridge, a different purpose).
2. `adsmt-ir-lower` is verdict/mode/face-**opaque** today (`Lowered{datatypes,
   goals}` has no face label, no mode): thread the face origin + `mode` through
   `Lowered` (or a solve-Context param) so the boundary can render Full mode.
3. The SMT 5-level is currently **invisible to AD1's own CLI**: `adsmt-engine`'s
   boundary is tri-state (`SatResult`), and `adsmt-cli`'s OxiZ delegation
   text-parses only `sat`/`unsat`/`unknown` — it never sets `OutputMode::Full`
   nor reads `Context::last_level()`. Surfacing the 5-level to adsmt is an
   independent, high-value first step (does not need the successor).
4. Quantifier triggers are dropped at lukb elaboration (kernel Π can't hold them);
   they must be threaded out-of-band to the MBQI loop or the successor path loses
   trigger-guided instantiation (completeness, not soundness).

### 10.5 Bring-up & v1.0.0 scope — DECIDED (user, 2026-06-30)

**The unified verdict surface (10.1–10.4) IS a v1.0.0 deliverable** (user decision):
the lu-kb successor carries a *trusted* `UnifiedVerdict` in the first stable
release. So `#165` (RC2.H.2 sign-off) is now gated on: `UnifiedVerdict` +
`LuKbOutputMode` + `solve_with_mode` built (10.4), and the §5/10.3
verdict-differential (`UnifiedVerdict.collapse() == SMT-LIB oracle`) PASSING on
vstd + corpus + randomized z3-diff. The `adsmt-ffi` C ABI still stays frozen at
its 4 exit codes (Full mode is Rust-side / out-of-ABI).

**CLI trichotomy (user decision, 2026-06-30) — the home for the verdict surfaces.**
The single `lu-smt` binary splits into three, sharing one library core:

- **`lu-smt`** — the existing SMT-LIB v2 driver. Unchanged, paradigm-pure, frozen
  surface (it delegates to OxiZ; gains optional `--output-mode full` to surface
  the 5-level `SatLevel` it already receives — see 10.4 item 3).
- **`adsmtc`** — the **compiler**: parses/elaborates/lowers the lu-kb-successor
  surface (and the SMT-LIB / typed-ASP faces) to the kernel, runs the unified
  solve, and emits the `UnifiedVerdict` (z3-compat or Full). This is the home of
  the §10 unified verdict + the Verus-emit consumer.
- **`adsmtr`** — the **runtime + REPL**: interactive solving, the ASP Full-mode
  3-valued well-founded model (the experimental ASP driver folds in here, not into
  `lu-smt`), and the 5-level SMT verdict, with incremental push/pop.

This resolves the earlier "where does ASP Full-mode go" question: NOT bolted onto
`lu-smt`, but native to `adsmtr` (interactive) and `adsmtc` (batch/compile).

[`adsmt-ir`]: ../../adsmt-ir
[`adsmt_emit_system`]: ../../../.claude/projects/-home-ybi-AD1/memory/adsmt_emit_system.md
[`asp_linter_design`]: ../../../.claude/projects/-home-ybi-AD1/memory/asp_linter_design.md
