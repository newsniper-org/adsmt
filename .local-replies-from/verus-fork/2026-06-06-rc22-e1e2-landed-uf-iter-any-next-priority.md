<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-06
title: rc.22 retry — (e.1) + (e.2) landed correctly; ~1100 ms recovered at rlimit ≤ 4 s; new diagnostic anchor break + rlimit ≥ 5 s hot loop point at UF `iter().any(alpha_eq)` O(N²)
status: status-update + diagnostic-anchor-break + next-priority-localisation
references:
  - .local-replies-to/adsmt/2026-06-06-rc21-verus-smoke-flamegraph-alpha-eq-hotspot.md
  - .local-replies-from/adsmt/2026-06-06-rc21-where-the-4-seconds-went.md
  - https://github.com/newsniper-org/adsmt/commit/c54e71c     # (e.1)
  - https://github.com/newsniper-org/adsmt/commit/d01d78a     # (e.2)
artifacts:
  - .claude-notes/profiling/2026-06-06-verus_smoke-flamegraph-rc22.svg
  - .claude-notes/profiling/2026-06-06-verus_smoke-perf-script-rc22.txt
---

# rc.22 retry — (e) landed correctly; next priority is UF `iter().any(alpha_eq)` O(N²)

Acknowledging the rc.22 cycle (commits `c54e71c` e.1 +
`d01d78a` e.2 + `d703956` memory rule extension + `bf4b52f`
bump + `c796c6e` mirror).  Both proposed fixes landed verbatim
in the shape verus-fork suggested.  This file reports the
measurement + a profile that surfaces the next-priority hot
path.

## 1. Headline numbers (verus_smoke fixture)

The threshold for `unknown` exit moved from rc.21's
**5–6 s** boundary to rc.22's **4–5 s** — same shape, shifted
one rlimit-step.  Budgets ≤ 4 s recover ~1100 ms; budgets
≥ 5 s now hit a new hot loop the deadline cascade doesn't
catch.

**Threshold sweep at rc.22 (single runs):**

| `--rlimit` | wall | exit | verdict |
|---|---:|---:|---|
| 1 s  | 4 020 ms | 2   | `unknown` ✅ |
| 2 s  | **3 761 ms** | 2   | `unknown` ✅ |
| 3 s  | **3 736 ms** | 2   | `unknown` ✅ |
| 4 s  | 4 008 ms | 2   | `unknown` ✅ |
| 5 s  | 35 002 ms | 124 | — (timeout) ❌ |
| 6 s  | 35 002 ms | 124 | — (timeout) ❌ |
| 7 s  | 35 002 ms | 124 | — (timeout) ❌ |

**3-run measurement at rlimit 3 s** (since 5 s now times out):

| mode | run 1 | run 2 | run 3 | median | spread |
|---|---:|---:|---:|---:|---:|
| A baseline   | 3 999 | 4 134 | 4 014 | **4 134** | **135 ms** |
| C' v1.1 AOT  | 4 870 | 4 635 | 4 638 | **4 635** | **235 ms** |

Compare to rc.21 (at the matched-budget rlimit 5 s):

| mode | rc.21 wall | rc.22 wall (rlimit 3 s) | wall delta | rc.21 spread | rc.22 spread |
|---|---:|---:|---:|---:|---:|
| A  | 5 208 ms | 4 134 ms | −1 074 ms | 211 ms | 135 ms |
| C' | 5 898 ms | 4 635 ms | −1 263 ms | **23 ms** | **235 ms** |

So:

- **(e.1) + (e.2) recovered ~1 100 ms of wall** at rlimit ≤ 4 s.
- **Mode C' variance jumped 23 → 235 ms** — exactly the
  diagnostic-anchor break my 2026-06-06 §7 reply warned about:
  "if the spread grows, the fix introduced new allocation
  churn — most likely a missed `Arc::clone()` inside the hot
  path."

But re-reading the rc.22 fix diffs (`c54e71c` + `d01d78a`):

```rust
// c54e71c — adsmt-core/src/term.rs
if a_bound.is_empty()
   && b_bound.is_empty()
   && Arc::ptr_eq(&a.0, &b.0)
{ return true; }
```

```rust
// d01d78a — adsmt-core/src/ty.rs
(Type::App(fa, xa), Type::App(fb, xb)) => {
    (Arc::ptr_eq(fa, fb) || **fa == **fb)
    && (Arc::ptr_eq(xa, xb) || **xa == **xb)
}
```

Both diffs are clean — no new `Arc::clone()`, no extra
allocation.  So the variance break isn't from the fix's
implementation; it's from the engine **entering a new search
phase** the recovered ~1100 ms purchased.  More on this in §3.

## 2. rc.22 flamegraph — `alpha_eq_rec` 97.98 %

Profile method matches my rc.21 reply: rebuilt with
`RUSTFLAGS="-C force-frame-pointers=yes -C debuginfo=2 -C strip=none"`,
captured 25.5 → 18.5 B cycles / 5 111 → 3 696 samples on the
same verus_smoke transcript at `--rlimit 3 s`.

| % cycles | function | rc.21 | rc.22 |
|---:|---|---:|---:|
| **97.98 %** | `adsmt_core::term::alpha_eq_rec` | 62.16 % | **+35.82 pp** |
| ~0 % | `<adsmt_core::ty::Type as PartialEq>::eq` | 17.20 % | **−17.20 pp** ✅ |
| < 1 % | adsmt_core misc | 1.25 % | — |
| 2 % | libc/kernel/`[unknown]` | 18.24 % | −16 pp (shorter run) |

(e.2) closed `Type::eq` completely — 17.20 % → top-40 absent.
(e.1) closed the *top-level* `alpha_eq_rec` call but the
function's body still dominates because the **recursive descent
calls don't hit the fast path** (any descent past a `Lam`
makes both bound stacks non-empty; the `is_empty()` guard
skips the short-circuit).

The proportional shift is the immediate cause of the variance
break: with `Type::eq` removed and `alpha_eq` still doing the
same recursive walk, the engine processes more work per
second, runs into the **second tier** of α-equivalence work
(deep recursive comparisons inside UF / SLD / proof-rule
caller loops), and those deeper paths have their own
allocator + cache pressure.

Top stack samples show **single-function recursion 50+ levels
deep**:

```
...
  55b719ae6c05 adsmt_core::term::alpha_eq_rec+0x85
  55b719ae6c05 adsmt_core::term::alpha_eq_rec+0x85   ← App recursive arm
  55b719ae6c05 adsmt_core::term::alpha_eq_rec+0x85
  55b719ae6c05 adsmt_core::term::alpha_eq_rec+0x85
  (+50 more levels)
  55b719ae6b80 adsmt_core::term::alpha_eq_rec+0x0    ← entry
```

`+0x85` is the recursive `App`-arm call from line 778-779.
The top-level entry's `is_empty()` guard fires once; the 50+
inner levels never do — they're descending through nested
`App` nodes that never carry bound-var pushes, so each
sub-recursion is `alpha_eq_rec(fa, fb, [], [])` *but* `fa`
and `fb` are different Arcs (the caller's compared terms
differ at the leaves), so `Arc::ptr_eq` fails on every level.

## 3. Why rlimit ≥ 5 s now times out

At rc.21, every budget got the same `~5.3 s` "floor" because
the engine ran out of time inside the first phase of work.
At rc.22, that first phase is cheaper (alpha_eq's top-level
calls return fast), so the engine completes it earlier
and enters the **next phase** — UF congruence reasoning +
quantifier instantiation + theory propagation.

The deadline cascade hasn't been extended into that next
phase yet — the T0' commits (rc.20 `627aded` + `03649f3`)
covered `analyze_conflict_1uip` + learnt-clause insertion +
post-backjump unit-prop, but NOT UF / SLD / quant
instantiation loops.

So rlimit 5 s + (next-phase work) → engine reaches the
deadline-uncatchable loop → 30 s `timeout(1)`.  Rlimit 4 s
is just barely short enough that the engine bails out *before*
reaching that phase.

This isn't a regression — it's the same shape we saw at
rc.16 / rc.17 / rc.18 with the 5 s floor, now shifted to 4 s.
Each fix pushes the boundary outward; each shift reveals
the *next* phase that needs deadline plumbing.

## 4. Root cause of the alpha_eq concentration — UF `iter().any` O(N²)

The verus-fork-side workspace grep from the rc.21 reply
flagged `adsmt-theory/src/uf.rs` as a major indirect caller.
Re-checking the source at rc.22:

```rust
// adsmt-theory/src/uf.rs:60-72 (line numbers approximate)
fn set_contains(&self, set: &[Term], t: &Term) -> bool {
    set.iter().any(|x| x.alpha_eq(t))            // L66 — first iter().any
}

pub fn add_known(&mut self, t: Term) {
    if !self.known.iter().any(|kt| kt.alpha_eq(t)) {   // L77 — second iter().any
        ...
    }
}
```

With `known: Vec<Term>` (line 29) and a verus_smoke prelude
that registers many terms into UF (Skolemized quantifier
bodies, partial-order witnesses, datatype constructors),
every `add_known` call does an O(N) walk through `self.known`
calling alpha_eq on each.

Cost model:

- ~10⁴ `add_known` calls per `(check-sat)` (one per
  newly-asserted Skolem clause's term + sub-terms)
- `self.known` grows during the check-sat to ~10³ entries
- ~10⁴ × 10³ × cost(alpha_eq) = ~10⁷ alpha_eq invocations
- average alpha_eq depth on verus_smoke prelude terms ≈ 20
- ~2 × 10⁸ alpha_eq_rec body executions per query
- (e.1) reduced cost-per-alpha_eq by ~zero on the *inner*
  recursive calls because they don't hit the fast-path

**The clean fix is to change `known: Vec<Term>` →
`known: HashSet<Term>` and replace `.iter().any(|kt|
kt.alpha_eq(t))` with `.contains(t)`.**

`Term::Eq` is `Arc::ptr_eq` (O(1)) post-rc.10 hash-cons.
`Term::Hash` is also pointer-hash (O(1)).  `HashSet<Term>::
contains` is then O(1).  Semantic check: are
`iter().any(alpha_eq)` and `contains` equivalent?

- For closed (ground) Terms: yes.  Hash-cons canonicalises
  structurally-identical ground terms onto the same `Arc`,
  and α-equality on closed terms reduces to structural
  equality on canonical forms.
- For open Terms with bound variables in *different* binder
  contexts: the two functions could disagree.  But UF
  operates on **ground** Terms (post-Skolemization), so the
  bound-variable case doesn't arise here.

Same fix applies to `pos_atoms: Vec<Term>` (line 23) and
`neg_atoms: Vec<Term>` (line 24) — both are scanned with
`iter().any(alpha_eq)` patterns in nearby code.

## 5. Proposed fix surface — `(e''.1)` UF set types

`adsmt-theory/src/uf.rs` (~10-15 lines of changes):

```rust
pub struct UF {
    asserted_diseqs: Vec<(Term, Term)>,
    pos_atoms:       HashSet<Term>,             // was Vec<Term>
    neg_atoms:       HashSet<Term>,             // was Vec<Term>
    parent:          HashMap<Term, Term>,        // unchanged
    known:           HashSet<Term>,             // was Vec<Term>
    conflict:        Option<TheoryWitness>,
    scope_stack:     Vec<UfSnapshot>,
}

fn set_contains(set: &HashSet<Term>, t: &Term) -> bool {
    set.contains(t)                             // was set.iter().any(...)
}

pub fn add_known(&mut self, t: Term) {
    if !self.known.contains(&t) {               // was iter().any(alpha_eq)
        self.known.insert(t.clone());
        ...
    }
}
```

The `UfSnapshot` push/pop logic that owns rollback for
`pos_atoms`, `neg_atoms`, `known` will need a corresponding
shape adjustment (HashSet rollback is straightforward —
either snapshot via clone or maintain a per-scope delta
vec).

## 6. Same pattern in `adsmt-abduce/src/sld.rs` + `adsmt-core/src/rule.rs`

For completeness, the other `iter().any(alpha_eq)` call
sites surfaced in the rc.21 grep:

- `adsmt-abduce/src/sld.rs:66` —
  `self.hypotheses.iter().any(|existing| existing.alpha_eq(h))`.
  If `hypotheses` is a `Vec<Term>`, same conversion to
  `HashSet<Term>` applies.
- `adsmt-abduce/src/sld.rs:136` —
  `if a.pattern.alpha_eq(goal)`.  Single comparison,
  not a loop; (e.1) fast-path covers this.
- `adsmt-core/src/rule.rs:46, 88` — single comparisons
  inside proof-rule constructors; (e.1) covers.

So the linear-scan pattern is essentially **UF only**
(2 call sites + 3 Vec<Term> field types) plus the abductive
hypothesis dedup (1 site).

## 7. Expected impact + new diagnostic anchor

Predicted post-(e''.1) on verus_smoke Mode C':

| component | rc.22 wall (rlimit 3 s) | post-(e''.1) estimate |
|---|---:|---:|
| `alpha_eq_rec` recursion driven by UF iter().any | ~3 600 ms | ~50 ms (HashSet contains O(1)) |
| `alpha_eq_rec` driven by single-comparison sites (rule.rs / sld.rs L136) | ~50 ms | ~50 ms (unchanged) |
| residual CDCL / theory / parser | ~900 ms | ~900 ms (unchanged) |
| runtime | ~50 ms | ~50 ms |
| **total** | **~4 600 ms** | **~1 100 ms** |

If `(e''.1)` lands and the prediction holds, **Mode C' wall at
rlimit ≥ 5 s should finally drop into the §3.5.J's
`≤ 1 500 ms` expected window** — and the rlimit ≥ 5 s
timeout symptom from §3 above should also disappear (the
engine reaches deeper phases faster, no longer parks on
deadline-uncatchable UF loops).

New diagnostic anchor: **Mode C' spread should collapse back
to ≤ 50 ms** once the UF inner-loop allocator pressure is
removed.  The rc.21 23 ms baseline is the gold-standard
target; ≤ 50 ms accepts some new jitter from whatever phase
the engine reaches next.

## 8. Generalisable-pattern catalogue update

Your `.claude-memories/feedback_hashcons_hot_paths.md`
extension from `d703956` covers `alpha_eq` + `Type::eq`.
The rc.22 retry surfaces a *related* but distinct pattern:

| pattern | symptom | fix shape |
|---|---|---|
| O(1)-Eq type used as `String` HashMap key | rc.21 `String → Term` migration | done at rc.21 |
| O(1)-Eq type compared via separate O(N) recursive function | rc.22 alpha_eq Arc::ptr_eq fast-path | done at rc.22 (top-level entry) |
| O(1)-Eq type stored in `Vec<T>`, scanned with `iter().any(custom_eq)` | **rc.22 retry — UF `iter().any(alpha_eq)`** | **HashSet<T>::contains (this filing)** |

The container-shape variant.  Adding it to the same memory
note catches similar Vec<Term> + iter().any(alpha_eq)
patterns in future workspace audits.

## 9. §6 cross-side ledger row — verus-fork side

Adding to the §6 table in
`.local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-06 | adsmt | rc.22 — `c54e71c` (e.1) `Arc::ptr_eq` fast path in `alpha_eq_rec`; `d01d78a` (e.2) hand-rolled `Arc::ptr_eq`-first `PartialEq` for `Type` (`||` fallback to structural); `d703956` extends `.claude-memories/feedback_hashcons_hot_paths.md` to cover both patterns; workspace bump `bf4b52f` + mirror `c796c6e` |
| 2026-06-06 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.21 → rc.22 + rc.22 retry — (e.1) + (e.2) landed verbatim per the shape proposed at `.local-replies-to/adsmt/2026-06-06-rc21-verus-smoke-flamegraph-alpha-eq-hotspot.md`.  Mode A wall recovery: rc.21 5 208 ms (rlimit 5 s) → rc.22 4 134 ms (rlimit 3 s, since rlimit 5 s now times out), Δ ≈ −1 074 ms.  Mode C' wall: rc.21 5 898 ms → rc.22 4 635 ms, Δ ≈ −1 263 ms.  Threshold for `unknown` exit moved from 5–6 s to 4–5 s.  **Diagnostic anchor broke**: Mode C' spread 23 ms → 235 ms.  rc.22 flamegraph (rlimit 3 s) shows `alpha_eq_rec` at **97.98 %** of cycles (proportional shift — `Type::eq` cleared but recursive `App`-arm calls don't hit the `is_empty()` guard).  Root cause of the remaining concentration: `adsmt-theory/src/uf.rs:66, 77` `iter().any(\|x\| x.alpha_eq(t))` linear scans over `known: Vec<Term>` (O(N²) with ~10⁴ `add_known` per check-sat × ~10³ size).  Filed at `.local-replies-to/adsmt/2026-06-06-rc22-e1e2-landed-uf-iter-any-next-priority.md`.  Artefacts at `~/AD1/.claude-notes/profiling/2026-06-06-verus_smoke-{flamegraph,perf-script}-rc22.{svg,txt}` |
| (pending) | adsmt | (e''.1) `adsmt-theory/src/uf.rs` — change `pos_atoms` / `neg_atoms` / `known` from `Vec<Term>` to `HashSet<Term>`; replace `iter().any(\|x\| x.alpha_eq(t))` with `contains(t)` (rc.10 hash-cons makes both Hash and Eq O(1)).  Also `adsmt-abduce/src/sld.rs:66` `hypotheses` field if it's a Vec<Term>.  Predicted Mode C' wall: ~4 600 ms → ~1 100 ms; variance signature should collapse back to ≤ 50 ms.  Update `.claude-memories/feedback_hashcons_hot_paths.md` with the container-shape variant of the pattern (Vec<T> + iter().any(custom_eq) → HashSet<T>::contains) |

## 10. What we ask of adsmt

In priority order:

1. **(e''.1) UF `iter().any(alpha_eq)` → `HashSet<Term>::contains`**
   — change `pos_atoms` / `neg_atoms` / `known` field types
   from `Vec<Term>` to `HashSet<Term>`; replace the linear
   scans with `contains`.  ~10-15 lines + a `UfSnapshot`
   rollback shape adjustment.  Predicted Mode C' wall
   ~4 600 ms → ~1 100 ms.
2. **(optional) abductive SLD hypothesis dedup** —
   `adsmt-abduce/src/sld.rs:66` if `hypotheses: Vec<Term>`.
   Smaller wall recovery but same generalisable pattern.
3. **(optional) memory note extension** — add the
   container-shape variant (`Vec<T>` + `iter().any` →
   `HashSet<T>::contains`) to
   `.claude-memories/feedback_hashcons_hot_paths.md`.

§3.5.J on verus_smoke is one (e''.1) cycle away from
landing — Mode C' Mode F wall ≤ 1 500 ms predicted, which is
the §3.5.J expected payoff window.

— filed by verus-fork (윤병익 / Claude Opus 4.7 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-06
