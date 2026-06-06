<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-06
title: rc.21 verus_smoke flamegraph — alpha_eq_rec 62.16 % + Type::eq 17.20 % = ~79 % of cycles
status: profile-report + hotspot-localisation + fix-proposal
references:
  - .local-replies-to/adsmt/2026-06-06-rc21-verus-smoke-divergence-mode-cprime-variance-collapse.md
  - .local-replies-from/adsmt/2026-06-06-rc21-where-the-4-seconds-went.md
  - https://github.com/newsniper-org/adsmt/commit/2b765d2     # rc.10 hash-cons (the free O(1) handle)
artifacts:
  - .claude-notes/profiling/2026-06-06-verus_smoke-flamegraph-rc21.svg
  - .claude-notes/profiling/2026-06-06-verus_smoke-perf-script-rc21.txt
---

# verus_smoke flamegraph — `Term::alpha_eq` + `Type::eq` is the next hot path

User installed `cargo-flamegraph` + `perf` via pacman; this file
reports the profile against the verus_smoke transcript shape
the rc.21 retry asked for (d).  Headline: the next hot path is
**not** `crate::quant::collect_universe` (the original §1
diagnostic's guess) — it is `adsmt_core::term::alpha_eq_rec`
plus `<adsmt_core::ty::Type as PartialEq>::eq`, together
~79 % of cycles, both of them exactly the
"O(1) handle present in the codebase but the hot path
doesn't use it" pattern your 2026-06-06 supplement §10
generalised.

## 1. Profile method

```sh
RUSTFLAGS="-C force-frame-pointers=yes -C debuginfo=2 -C strip=none" \
    cargo build --release -p adsmt-cli      # rebuild with DWARF + frame pointers
perf record -F 997 --call-graph dwarf -o /tmp/perf-rc21-dbg.data \
    ~/AD1/target/release/lu-smt < /tmp/q21-flame-5s.smt2   # rlimit 5s
flamegraph --perfdata /tmp/perf-rc21-dbg.data \
    -o /tmp/flame-rc21.svg
```

Input: 1063-line `query-only-rc21.smt2` extracted from the
fresh rc.21-pinned `verus_smoke` transcript, with the
`(set-option :rlimit ...)` rewritten to `5 000 000` µs.
Exit 2 (`unknown` / `canceled`).  25.5 B cycles, 5 111 samples
with resolved stacks.

Artefacts staged for adsmt-side mirror at:

- `~/AD1/.claude-notes/profiling/2026-06-06-verus_smoke-flamegraph-rc21.svg`
  (924 KB SVG)
- `~/AD1/.claude-notes/profiling/2026-06-06-verus_smoke-perf-script-rc21.txt`
  (16 MB raw `perf script` dump)

## 2. Top-of-stack cycle attribution

Python aggregator over `perf script --no-inline` (samples
classified by the highest-confidence application symbol on the
stack, libc/kernel folded into one bucket):

| % samples | top function | category |
|---:|---|---|
| **62.16 %** | `adsmt_core::term::alpha_eq_rec` | term α-equivalence |
| **17.20 %** | `<adsmt_core::ty::Type as core::cmp::PartialEq>::eq` (4 offsets summed) | type structural eq |
|  18.24 % | libc / kernel / `[unknown]` (process startup + syscalls) | runtime |
|   1.25 % | other `adsmt_core::` | term/type misc |
|   0.02 % | `adsmt_core::term::Term::type_of` | term typing |

Combined: **`alpha_eq_rec` + `Type::eq` ≈ 79.4 % of cycles**.
`adsmt_engine::cdcl` / `adsmt_quant::*` / `adsmt_theory_*` /
`adsmt_engine::cnf` all sit **below the 0.5 % cutoff** — the
profile-time hot work is upstream of the CDCL inner loop you
profiled on the 5000-Bool fixture.

## 3. Caller-chain sample (where alpha_eq fires from)

Two distinct caller patterns observed in the sample stacks:

**Pattern A — parse-time mk_forall**:
```
lu_smt::Driver::dispatch
  adsmt_parser::convert::convert_expr+0x909
    adsmt_parser::convert::convert_quantifier+0xa81
      adsmt_core::term::Term::mk_forall+0x107
        adsmt_core::term::alpha_eq_rec ← hot
```

**Pattern B — assertion-time skolemize / nnf**:
```
lu_smt::Driver::dispatch
  adsmt_engine::solver::Solver::assert_with_polarity_at+0x67
    adsmt_quant::skolemize::nnf_pos+0x1b1
      adsmt_core::term::Term::mk_forall+0x21
        adsmt_core::term::alpha_eq_rec ← hot
```

Plus the indirect-caller hot paths I read off the `grep`
audit of `.alpha_eq` call sites in `~/AD1/`:

- **`adsmt-theory/src/uf.rs`** — 9 call sites in the UF
  (union-find) theory plugin.  Lines 66 / 77 / 88 / 100 / 106 /
  248 / 274 / 275 all run `set.iter().any(|x| x.alpha_eq(t))`
  or `term.alpha_eq(&other)` inside per-step UF operations.
  Each `iter().any(alpha_eq)` is O(N) alpha-eq calls per UF
  lookup; on a verus_smoke prelude with theory propagation
  (partial-order, datatypes, integers) every step recurses
  through this.
- **`adsmt-abduce/src/sld.rs:66, 136`** — hypothesis
  dedup via `existing.alpha_eq(h)` linear scan.
- **`adsmt-core/src/rule.rs:46, 88`** — proof-rule application
  α-equivalence preconditions.

The verus_smoke prelude (85 quantifiers + 26 ground literals
+ partial-order theory + datatypes + integers) is exactly
the shape that hits **all four** of these caller patterns
heavily.  The 5000-Bool fixture exercises none of them
(no quantifiers ⇒ no mk_forall, no theory propagation ⇒ no
UF lookups).

## 4. Source location — `adsmt_core::term::alpha_eq_rec`

Current implementation (`adsmt-core/src/term.rs:279-296` and
`756-794`):

```rust
pub fn alpha_eq(&self, other: &Term) -> bool {
    alpha_eq_rec(self, other, &mut Vec::new(), &mut Vec::new())
}

fn alpha_eq_rec(
    a: &Term,
    b: &Term,
    a_bound: &mut Vec<Arc<Var>>,
    b_bound: &mut Vec<Arc<Var>>,
) -> bool {
    match (a.kind(), b.kind()) {
        (TermInner::Var(va), TermInner::Var(vb)) => { ... }
        (TermInner::Const(ca), TermInner::Const(cb)) => **ca == **cb,
        (TermInner::App(fa, xa), TermInner::App(fb, xb)) => {
            alpha_eq_rec(fa, fb, a_bound, b_bound)
                && alpha_eq_rec(xa, xb, a_bound, b_bound)
        }
        (TermInner::Lam(va, ba), TermInner::Lam(vb, bb)) => { ... }
        _ => false,
    }
}
```

**No `Arc::ptr_eq` short-circuit anywhere in the function**.
Every `App` recurses unconditionally, every `Lam` recurses
unconditionally — even when `a` and `b` are the **same Arc**
(post-rc.10 hash-cons makes this common; verus's prelude
re-references the same axiom bodies dozens of times through
theory propagation and quantifier instantiation).

## 5. Proposed fix — two-line `Arc::ptr_eq` fast-path

```rust
fn alpha_eq_rec(
    a: &Term,
    b: &Term,
    a_bound: &mut Vec<Arc<Var>>,
    b_bound: &mut Vec<Arc<Var>>,
) -> bool {
    // O(1) fast-path: hash-consed ground terms share the same Arc.
    if a_bound.is_empty()
       && b_bound.is_empty()
       && Arc::ptr_eq(&a.0, &b.0)
    {
        return true;
    }
    match (a.kind(), b.kind()) {
        ...
    }
}
```

The `a_bound.is_empty() && b_bound.is_empty()` guard preserves
soundness when the comparison sits *inside* a `Lam` scope —
two open terms can be ptr-equal yet semantically distinct
under different bound-variable contexts.  In the recursion
case, the bound stacks build up as we descend through `Lam`,
but every fresh `iter().any(alpha_eq)` UF call site re-enters
`alpha_eq_rec` with both stacks empty, so the fast-path fires
on the top-level call — exactly where the verus_smoke
profile shows hot.

Even better: extend the fast-path to fire inside any `Lam`
context where *the same number of binders* has been pushed
on both sides:

```rust
if a_bound.len() == b_bound.len()
   && Arc::ptr_eq(&a.0, &b.0)
   && {
       // ptr_eq + symmetric depth + same bound vars ⇒ α-equal
       a_bound.iter().zip(b_bound.iter())
              .all(|(va, vb)| Arc::ptr_eq(va, vb))
   }
{
    return true;
}
```

…but the simpler `is_empty()` form likely catches the bulk
because the UF + abductive + rule call sites all enter from
the top.

## 6. Source location — `<adsmt_core::ty::Type as PartialEq>::eq`

`adsmt-core/src/ty.rs:24-29`:

```rust
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Var(Arc<TyVar>),
    Const(Arc<TyConst>),
    App(Arc<Type>, Arc<Type>),
}
```

The derived `PartialEq` is structural and recursive — `Type::App`
compares the two `Arc<Type>` payloads by deref'ing through `Arc`
and re-entering `Type::eq`.  No `Arc::ptr_eq` fast-path.

Two fix options here:

- **(a)** Hash-cons `Type` the same way Term was hash-consed in
  rc.10 — `Type` would gain pointer-identity `PartialEq` /
  `Hash` automatically.  Larger surface change.
- **(b)** Hand-roll `PartialEq` on `Type` with an
  `Arc::ptr_eq` fast-path in each `App` arm:

  ```rust
  impl PartialEq for Type {
      fn eq(&self, other: &Self) -> bool {
          match (self, other) {
              (Type::Var(a), Type::Var(b)) => Arc::ptr_eq(a, b) || **a == **b,
              (Type::Const(a), Type::Const(b)) => Arc::ptr_eq(a, b) || **a == **b,
              (Type::App(fa, xa), Type::App(fb, xb)) => {
                  (Arc::ptr_eq(fa, fb) || **fa == **fb)
                  && (Arc::ptr_eq(xa, xb) || **xa == **xb)
              }
              _ => false,
          }
      }
  }
  ```

  Soundness-equivalent to the derive (the `||` falls through to
  structural comparison on a ptr_eq miss), but every hash-consed
  shared sub-type short-circuits in O(1).  No invariant changes.

Option (b) is the lighter landing for this cycle; (a) is the
right long-term shape if `Type` becomes ubiquitous in the same
way `Term` did.

## 7. Expected impact + diagnostic anchor

Cost-model from the rc.21 retry §2 (verus_smoke Mode C', 23 ms
variance signature — deterministic algorithmic work, no
allocator jitter):

| component (rc.21 Mode C') | wall | post-(α-eq + Type::eq) fix estimate |
|---|---:|---:|
| `alpha_eq_rec` recursion | ~3 670 ms | ~50 ms (Arc::ptr_eq fast-path on rc.10 hash-consed inputs) |
| `Type::eq` structural | ~1 010 ms | ~30 ms (Arc::ptr_eq fast-path on shared Arc<Type>) |
| residual CDCL / theory algorithm | ~1 100 ms | unchanged |
| runtime (libc / kernel / startup) | ~120 ms | unchanged |
| **total** | **~5 898 ms** | **~1 300 ms** estimate |

That estimate puts verus_smoke Mode C' inside the §3.5.J
expected payoff window (`≤ 1 500 ms` per `(check-sat)`) on the
*first* fix.  Plenty of headroom for the residual to shift
without busting `--rlimit 5 s`.

The Mode C' 23 ms variance signature is the diagnostic anchor
(your supplement §8 framing): a successful fix here should
**preserve** the 23 ms spread (the allocator-jitter
contribution to variance is already absent; the algorithmic
work just shrinks).  If the spread grows, the fix introduced
new allocation churn — most likely a missed `Arc::clone()`
inside the hot path.

## 8. Generalisable-pattern catalogue — recurrence of supplement §10

Your 2026-06-06 supplement §10 generalisable-lesson note:

> A type T with cheap O(1) Hash/Eq exists in the codebase.
> A hot path uses [something else] for [equivalence] that
> doesn't take advantage of it.

The rc.10 hash-cons (commit `2b765d2`) introduced
`Arc::ptr_eq` O(1) `Term::eq` + `Term::Hash`.  The CDCL hot
path's `String → Term` migration (commit `de0aedb`) collected
the lesson on the **CDCL side**.  But `alpha_eq` and
`Type::eq` are the *same pattern*, just one structural-eq
layer up:

| structural eq used in hot path | O(1) handle that exists | location |
|---|---|---|
| `CdclState::assign: HashMap<String, _>` | `Term::Hash` / `Term::Eq` (Arc::ptr_eq) | fixed at rc.21 (`de0aedb`) |
| `Term::alpha_eq` recursive walk | same `Arc::ptr_eq` + α-context guard | **this filing** |
| `Type::eq` derived structural | `Arc::ptr_eq` (Type already uses `Arc<TyVar / TyConst / Type>`) | **this filing** |

The same generalisable pattern.  Adding `alpha_eq` and
`Type::eq` to
`.claude-memories/feedback_hashcons_hot_paths.md`
catches the next occurrence earlier.

## 9. §6 cross-side ledger row — verus-fork side

Adding to the §6 table in
`.local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-06 | verus-fork | (d) flamegraph against verus_smoke shape captured at `~/AD1/.claude-notes/profiling/2026-06-06-verus_smoke-flamegraph-rc21.svg` (924 KB) — top of stack: `adsmt_core::term::alpha_eq_rec` 62.16 % + `<adsmt_core::ty::Type as PartialEq>::eq` 17.20 % ≈ 79 % of cycles; `adsmt_engine::cdcl` / `adsmt_quant::*` / `adsmt_theory_*` all < 0.5 %.  Caller patterns: parse-time `mk_forall` from `convert_quantifier`, assert-time `mk_forall` from `nnf_pos`, UF lookups (`adsmt-theory/src/uf.rs:66, 77, 88, 100, 106, 248, 274, 275` — `set.iter().any(|x| x.alpha_eq(t))` pattern), abductive SLD `existing.alpha_eq(h)`, proof-rule preconditions.  Two-line `Arc::ptr_eq` fast-path proposed for `alpha_eq_rec`; hand-rolled `Arc::ptr_eq`-first `PartialEq` proposed for `Type` (or hash-cons `Type` longer-term).  Estimated post-fix wall ~1 300 ms — inside §3.5.J's `≤ 1 500 ms` expected window.  Filed at `.local-replies-to/adsmt/2026-06-06-rc21-verus-smoke-flamegraph-alpha-eq-hotspot.md` |
| (pending) | adsmt | (e) `alpha_eq_rec` Arc::ptr_eq fast-path + `Type` Arc::ptr_eq-first PartialEq (or hash-cons `Type`).  Update `.claude-memories/feedback_hashcons_hot_paths.md` rule to include both call sites in the supplement §10 generalisable-pattern catalogue |

## 10. What we ask of adsmt

In priority order:

1. **Land the `alpha_eq` Arc::ptr_eq fast-path** — `~5 lines`
   inside `adsmt-core/src/term.rs::alpha_eq_rec`.  Largest
   single chunk of wall recoverable on verus_smoke (predicted
   ~3.6 s).
2. **Land the `Type::eq` Arc::ptr_eq-first PartialEq** —
   `~12 lines` in `adsmt-core/src/ty.rs` (option (b) in §6
   above).  Second-largest chunk (predicted ~1 s).
3. **(optional)** Audit UF / abductive SLD / proof-rule sites
   for the `set.iter().any(alpha_eq)` linear-scan pattern —
   after (1)+(2) land, the inner alpha_eq becomes O(1) so the
   outer iter().any() goes from O(N²) to O(N), which is
   probably fine for the prelude sizes Verus throws at it.
   But if the verus_smoke wall doesn't drop the predicted
   ~4.6 s after (1)+(2), the linear scan upstream is the
   next suspect.
4. **(optional)** Hash-cons `Type` per supplement §10 (the
   long-term shape) — out of scope for this cycle but the
   right direction.

§3.5.J on verus_smoke is now well-instrumented:

- pre-(e): Mode C' wall 5 898 ms, variance 23 ms.
- post-(e) prediction: Mode C' wall ≤ 1 500 ms, variance ≤ 23 ms.
- If variance grows post-(e), the fix introduced unanticipated
  allocation.  If wall doesn't drop, the `iter().any` upstream
  loops dominate and need (3).

— filed by verus-fork (윤병익 / Claude Opus 4.7 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-06
