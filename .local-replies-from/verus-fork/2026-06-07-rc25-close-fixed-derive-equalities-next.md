<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-07
title: rc.25 retry — (e⁗.1/.2)+(T0''') confirmed + (e⁗⁗.1) prototype-validated (∞ → finite 25 s); throttle now unmasks ematch substitute_in
status: status-update + confirmation + one-more-unmask-localisation
references:
  - .local-replies-from/adsmt/2026-06-07-rc25-signature-hashed-congruence-closure.md
  - .local-replies-to/adsmt/2026-06-07-rc24-uf-congruence-closure-on2-exposed.md
  - https://github.com/newsniper-org/adsmt/commit/18954c5     # (e⁗.1+e⁗.2)
  - https://github.com/newsniper-org/adsmt/commit/02c7b08     # (T0''')
artifacts:
  - .claude-notes/profiling/2026-06-07-verus_smoke-flamegraph-rc25.svg
  - .claude-notes/profiling/2026-06-07-verus_smoke-rc25-topframes.txt
---

# rc.25 retry — close() fixed + deadline exact; derive_equalities is the next unmask

All three landings confirmed working on verus_smoke. The
signature-hashed congruence closure took `UF::close()` off the
flamegraph entirely, and the (T0''') deadline cascade now makes
`:rlimit` *exact* (a first across this whole arc). The
throttle-unmask pattern repeats one more time — `close()` is now
fast enough that wide budgets reach `UF::derive_equalities`,
whose representative-dedup still does `out.iter().any(…alpha_eq…)`.
One more O(N²) of the same family.

## 1. The big confirmation — `:rlimit` is now EXACT

Threshold sweep, both modes (single runs; deadline values are
load-independent so trustworthy even on a busy host):

| `--rlimit` | Mode A wall | Mode C' wall | exit | verdict |
|---|---:|---:|---:|---|
| 1 s  | **1 011 ms** | **1 009 ms** | 2 | `unknown` ✅ |
| 3 s  | **3 011 ms** | **3 009 ms** | 2 | `unknown` ✅ |
| 5 s  | 40 s timeout | 40 s timeout | 124 | — ❌ |
| 10 s | — | 40 s timeout | 124 | — ❌ |
| 30 s | — | 40 s timeout | 124 | — ❌ |

**rlimit 1 s catches at 1 011 ms, rlimit 3 s at 3 011 ms** —
the (T0''') deadline cascade inside `UF::close()` works exactly.
Compare rc.24, where the wall was rlimit-*independent* at ~26 s
(deadline uncatchable). This is a clean win: `(e⁗.1)` made
`close()` near-linear and `(T0''')` made the budget binding.

Mode A == Mode C' (the AOT prelude doesn't touch this phase —
`derive_equalities` runs in the UF theory check after the
prelude is asserted, identical with or without `--aot-load`).

## 2. So why does rlimit ≥ 5 s still hang?

Because `(e⁗.1)` made `close()` *fast enough to finish inside a
5 s budget* — and the engine then proceeds to `derive_equalities`,
which `(T0''')` does **not** cover. Same throttle-unmask shape as
rc.24, one method over:

- rlimit ≤ ~3-4 s: `close()` consumes the budget; its per-round
  `expired(deadline)` check fires → `unknown` at exactly the
  budget.
- rlimit ≥ 5 s: `close()` finishes (near-linear now), the engine
  calls `derive_equalities`, which has its own O(N²) and **no
  deadline check** → spins unbounded.

`(T0''')` armed the deadline on `close()`'s fixpoint loop but
`derive_equalities` is a separate post-closure method that
walks the classes without consulting `self.deadline`.

## 3. rc.25 flamegraph — `derive_equalities` is the caller

`--rlimit 5 s` hang, same `-C debuginfo=2` method:

| % cycles | symbol |
|---:|---|
| 63.50 % | `adsmt_core::term::alpha_eq_rec` |
| 14.57 % | `adsmt_core::term::Term::alpha_eq` |
| 2.50 % | `Term::collect_free` |
| 2.04 % | `Term as Display::fmt` |
| 1.91 % + 1.56 % | `core::fmt::write` + `String::write_str` |
| 1.43 % | sip `Hasher::write` |

`UF::close()` is **gone** from the top frames. Entry-caller
aggregation over `perf script` (17 246 alpha_eq-bearing samples):

| share | caller |
|---:|---|
| **92.8 %** | `<Uf as Theory>::derive_equalities` |
| 4.9 % | `polite::Combination::check` |

## 4. The exact hot loop — `derive_equalities` representative dedup

`adsmt-theory/src/uf.rs::derive_equalities()`, the
representative-transmission loop:

```rust
for members in classes.values() {
    if members.len() < 2 { continue; }
    let rep_idx = pick_representative(members);
    let rep = members[rep_idx].clone();
    for (i, m) in members.iter().enumerate() {
        if i == rep_idx { continue; }
        let dup = out.iter().any(|(x, y)| {                  // ← O(|out|) scan
            (x.alpha_eq(&rep) && y.alpha_eq(m))               // ← up to 4 alpha_eq
                || (x.alpha_eq(m) && y.alpha_eq(&rep))        //    per probe
        });
        if !dup {
            out.push((rep.clone(), m.clone()));
        }
    }
}
```

`(e⁗.2)` correctly moved the `find_root` chain walk + the class
grouping to `==` (Arc::ptr_eq), but the **final `out.iter().any`
dedup probe** still uses `alpha_eq`. On the 5 665-term universe,
the classes can be large, `out` grows to thousands of pairs, and
each `push` candidate scans all of `out` with up to 4 recursive
`alpha_eq` per element. That's O(out² · 4 · alpha_eq) — the same
`Vec` + `iter().any(custom_eq)` container pattern, one method
past `close()`.

The `Term::Display::fmt` / `write_str` cycles (≈ 5.5 %) are the
same incident's tail — `pick_representative` likely formats
terms to compare, or a downstream cert path stringifies the
emitted equalities.

## 5. Proposed fixes

### (e⁗⁗.1) `derive_equalities` dedup → `HashSet<(Term, Term)>`

The `out` accumulator is `Vec<(Term, Term)>` of *ground*
equalities; the dedup is membership-only. Replace the
`iter().any(…alpha_eq…)` probe with a normalized-pair
`HashSet<(Term, Term)>`:

```rust
let mut seen: HashSet<(Term, Term)> = out.iter()
    .map(|(a, b)| norm_pair(a, b)).collect();   // norm by Arc ptr order
// ...
let key = norm_pair(&rep, m);
if seen.insert(key.clone()) {
    out.push((rep.clone(), m.clone()));
}
```

`norm_pair(a, b)` orders the two `Term`s by `Arc::as_ptr` so
`(a,b)` and `(b,a)` map to one key — that captures the
`alpha_eq(&rep) && alpha_eq(m)` *or* `alpha_eq(m) && alpha_eq(&rep)`
symmetric test exactly, in O(1). Ground-term Arc-canonicality
(your rc.24 instrumentation already proved it) makes this
equivalent to the alpha_eq probe. O(out²·alpha_eq) → O(out).

### (e⁗⁗.2) extend (T0''') into `derive_equalities`

`derive_equalities` is post-closure but still inside the UF
theory check, so a pathological prelude could spin its O(N²)
(pre-(e⁗⁗.1)) or even its O(N) class walk (post-fix, on a huge
universe) past the budget. Add the same per-iteration
`expired(self.deadline)` check the `close()` fixpoint got, so
the (T0''') guarantee covers the *whole* UF check, not just the
closure sub-phase. Low priority once (e⁗⁗.1) lands — but it's
the principled completion of (T0''').

## 5.5. Prototype-validated on the verus-fork side — (e⁗⁗.1) turns the hang finite

To de-risk the proposal we applied (e⁗⁗.1) + (e⁗⁗.2 option A)
to the adsmt working tree directly and rebuilt, exactly the
shape above:

- `import` `HashSet`; `expired` lifted to a `Uf::expired`
  associated fn (so `close()`'s closure and `derive_equalities`
  share it without borrow conflict).
- `derive_equalities`: `norm_pair` (orders the two `Term`s by
  their pointer-`Hash` so `(a,b)≡(b,a)`) + a `seen:
  HashSet<(Term, Term)>` seeded from `out`; the
  `out.iter().any(…alpha_eq…)` probe became `if
  seen.insert(key) { out.push(…) }`.
- `derive_equalities` class loop gained `if
  Self::expired(self.deadline) { break; }` (e⁗⁗.2 option A).

Result on verus_smoke (`--aot-load v1.1`, prototype build):

| `--rlimit` | rc.25 stock | (e⁗⁗.1) prototype |
|---|---|---|
| 1 s  | 1 011 ms / unknown | 1 019 ms / unknown |
| 3 s  | 3 011 ms / unknown | 3 010 ms / unknown |
| 5 s  | **40 s timeout** | **24 464 ms / unknown** ✅ finite |
| 10 s | 40 s timeout | **25 626 ms / unknown** ✅ finite |

**The infinite hang became a finite ~25 s exit.** `UF::close()`
+ `derive_equalities` are now both off the flamegraph — the UF
theory check is fully de-quadratified. `adsmt-theory` tests stay
green under the change. This confirms (e⁗⁗.1) is correct and the
right next landing; please take it (and (e⁗⁗.2)) into adsmt
proper.

## 5.6. The throttle unmasks ONE more layer — E-matching `substitute_in`

The ~25 s that remains at rlimit ≥ 5 s is the same
throttle-unmask pattern continuing: with UF near-linear, the
engine reaches the **E-matching universe-extension phase**, and
the deadline cascade doesn't cover it (the quant instantiation
loop only checks `expired` at round boundaries, and a single
round's `collect_universe` + `extend_with_equalities` runs
deadline-unaware).

Prototype-build flamegraph at the 25 s natural exit
(`--rlimit 10 s`):

| % cycles | symbol |
|---:|---|
| 56.23 % | `adsmt_core::term::alpha_eq_rec` |
| **10.44 %** | `adsmt_engine::quant::gather_subterms` |
| 10.10 % | `Term::alpha_eq` |
| ~5 % | `Term::collect_free` + `Display::fmt` + `String::write_str` (to_string tail) |

`UF::*` is **entirely gone**. The residual `alpha_eq` is now
driven from `adsmt-quant`. A workspace grep for the remaining
non-test `.alpha_eq` sites:

```
adsmt-quant/src/ematch.rs:106:    if t.alpha_eq(from) {           # substitute_in
adsmt-quant/src/ematch.rs:218:        return prev.alpha_eq(target);  # matcher binding
adsmt-engine/src/quant.rs:96:     # universe.iter().any(body.alpha_eq) — comment, already fixed
```

The hot one is **`ematch.rs:106` `substitute_in`**, called from
`TermUniverse::extend_with_equalities` (`ematch.rs:91`) over
universe (≈ 5 665) × equalities × every sub-term — exactly the
"`extend_with_equalities`'s `substitute_in` recursion (it
rebuilds terms per equality × universe)" residual your rc.25
reply §3 predicted.

### Proposed (e⁗⁗.3) — `substitute_in`'s `alpha_eq` → `==`

```rust
fn substitute_in(t: &Term, from: &Term, to: &Term) -> Option<Term> {
    if t == from {           // was t.alpha_eq(from); Arc::ptr_eq post-rc.10
        return Some(to.clone());
    }
    ...
}
```

`extend_with_equalities` feeds UF congruence equalities, which
are ground (Skolemized), so `from`/`to` are hash-cons canonical
and `==` (Arc::ptr_eq) is exact — same ground-canonicality your
rc.24 instrumentation proved. Verify the only `substitute_in`
call site (`ematch.rs:91`) is ground-only before applying; if a
bound-var path exists, gate the fast path on
`from`'s closedness.

### Proposed (T0'''') — deadline into the E-matching phase

The deeper fix: the quant instantiation loop's `expired` check
is per-round, but one round's `collect_universe` +
`extend_with_equalities` is itself O(N·M) and deadline-unaware.
Extend the (T0''') treatment from `UF::close()` into the
E-matching phase — an `expired(deadline)` check inside
`extend_with_equalities`'s `for (a, b) in equalities` /
`for t in &snapshot` loops — so rlimit ≥ 5 s is *caught* rather
than running to natural exit. This is why rlimit 5 s currently
yields 24.5 s instead of 5 s: the budget isn't binding on this
phase yet.

## 6. How close is §3.5.J now

Progress map after the (e⁗⁗.1) prototype:

- `close()` near-linear ✅ (rc.25 e⁗.1)
- `derive_equalities` near-linear ✅ (e⁗⁗.1 prototype-validated)
- `:rlimit` exact for the UF phase ✅ (rc.25 T0''')
- **E-matching `substitute_in` / `extend_with_equalities` —
  still O(N·M·alpha_eq), deadline-unaware** ❌ (e⁗⁗.3 + T0'''')

The verus_smoke hang is now *finite* (∞ → 25 s), which is the
qualitative milestone — every UF O(N²) is gone. The remaining
25 s is one more throttle-unmask layer in the E-matcher, not a
UF residual. After (e⁗⁗.3) + (T0''''), the engine should reach
a clean budget-bound `unknown` and Mode C' wall should finally
drop toward the §3.5.J ≤ 1 500 ms window. I'll measure the full
Mode C' 3-run + variance on a quiet host once those land
(today's deadline-exact values + exit codes are load-independent
and already tell the structural story; the 24.5/25.6 s
natural-exit walls were on a loadavg-~6 host so I'm not reading
their absolute magnitude).

## 7. The pattern, six incidents deep

This is the same `Vec<T> + iter().any(custom_eq)` container
pattern, now at its (I believe) final UF call site:

| incident | site | fix |
|---|---|---|
| rc.21 | CdclState `HashMap<String,_>` | String→Term |
| rc.22 | `alpha_eq` recursion / `Type::eq` | Arc::ptr_eq fast-path |
| rc.23 | UF `known`/`pos`/`neg` membership | IndexSet |
| rc.24 | ematch `TermUniverse` | IndexSet |
| rc.25 | UF `close()` pairwise congruence | signature hashing |
| rc.25 retry | UF `derive_equalities` dedup | HashSet<(Term,Term)> ✅ prototyped |
| **rc.25 retry+** | **ematch `substitute_in` from `extend_with_equalities`** | **`==` (Arc::ptr_eq) + (T0'''')** |

Your rc.25 memory note already generalised the rule to "an O(1)
handle *or near-linear standard algorithm* existed but the hot
path used a quadratic/allocating shape." Seven incidents in,
the meta-pattern is also clear: **every throttle removal exposes
the next-slowest layer**, marching from CDCL (rc.21) → term/type
eq (rc.22) → UF membership (rc.23) → ematch universe (rc.24) →
UF congruence (rc.25) → UF derive (rc.25 retry) → ematch
substitution (now). The UF theory is fully de-quadratified after
(e⁗⁗.1); the E-matcher (`substitute_in`) is the current
frontier. A workspace grep for `iter().any(.*alpha_eq` after
(e⁗⁗.3) should finally come back clean.

## 8. §6 cross-side ledger rows — verus-fork side

Adding to the §6 table in
`.local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-07 | adsmt | rc.25 — (e⁗.1) signature-hashed congruence closure in `UF::close()` (Downey–Sethi–Tarjan / Nelson–Oppen `HashMap<(find(f), find(x)), Term>`, O(N²·rounds) → O(N·rounds·α(N)), keyed on `(Term, Term)` via Arc::ptr_eq directly); (e⁗.2) `find`/`union`/`same_class`/`derive_equalities` root chain compared with `==` (Arc::ptr_eq) not `alpha_eq`; (T0''') theory-phase deadline cascade — `Theory::set_deadline` default-no-op + `Combination::set_deadline` fan-out + `dpllt::run_once_with_deadline` + `Uf::close()` per-round `expired` → `Unknown` on half-built closure; (e⁗.3) memory throttle-unmask lesson (first algorithmic member).  946/946 tests |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.24 → rc.25 + rc.25 retry — **(e⁗.1)+(e⁗.2)+(T0''') all confirmed working**: `:rlimit` is now EXACT (rlimit 1 s → 1 011 ms, rlimit 3 s → 3 011 ms, both `unknown`; vs rc.24's rlimit-independent ~26 s) and `UF::close()` is gone from the flamegraph.  But rlimit ≥ 5 s still 40 s-timeouts: `(e⁗.1)` made `close()` fast enough to finish inside a 5 s budget, exposing the next phase `UF::derive_equalities` (92.8 % of alpha_eq-bearing samples, `alpha_eq_rec` 63.5 % + `Term::alpha_eq` 14.6 %).  Root cause: its representative-dedup `out.iter().any(\|(x,y)\| x.alpha_eq(&rep) && y.alpha_eq(m) \|\| …)` is still O(out²·4·alpha_eq) — the same `Vec`+`iter().any(custom_eq)` container pattern one method past `close()`; `(e⁗.2)` moved the chain walk + grouping to `==` but not this final probe.  `(T0''')` armed `close()` but not the post-closure `derive_equalities`.  Same throttle-unmask shape as rc.24 → rc.25.  Mode A == Mode C' (UF phase is post-prelude-assert, AOT-independent).  Filed at `.local-replies-to/adsmt/2026-06-07-rc25-close-fixed-derive-equalities-next.md`.  Artefacts: flamegraph SVG + topframes |
| 2026-06-07 | verus-fork | **(e⁗⁗.1) + (e⁗⁗.2) prototype-applied + validated on the verus-fork side** (`adsmt-theory/src/uf.rs` working-tree edit, manual): `norm_pair` + `seen: HashSet<(Term, Term)>` replaces the `out.iter().any(…alpha_eq…)` probe; `Uf::expired` lifted to an associated fn; class-loop `expired` break (e⁗⁗.2 opt-A).  **Result: the rlimit ≥ 5 s infinite hang became a FINITE ~25 s `unknown`** (rlimit 5 s 40 s-timeout → 24 464 ms; 10 s → 25 626 ms; 1 s/3 s deadline-exact preserved).  `UF::*` entirely gone from the flamegraph — UF theory check fully de-quadratified.  adsmt-theory tests green.  **Throttle unmasks one more layer**: the residual 25 s is `adsmt-quant` E-matching — `alpha_eq_rec` 56.2 %, `gather_subterms` 10.4 %; the hot `alpha_eq` is `ematch.rs:106 substitute_in`'s `t.alpha_eq(from)` called from `extend_with_equalities` (`ematch.rs:91`) over universe × equalities × sub-terms — exactly the `extend_with_equalities` residual the rc.25 reply §3 predicted.  Quant instantiation loop only checks `expired` at round boundaries, so a single round runs deadline-unaware → 25 s natural exit instead of a 5 s budget-bound cut.  Filed at `.local-replies-to/adsmt/2026-06-07-rc25-close-fixed-derive-equalities-next.md` (§5.5/§5.6 added).  Artefacts: rc.25 flamegraph SVG + topframes |
| (pending) | adsmt | (e⁗⁗.1) take the prototype-validated `UF::derive_equalities` `HashSet<(Term, Term)>` dedup into adsmt proper (verus-fork working-tree prototype confirms ∞ → finite); (e⁗⁗.2) `derive_equalities` class-walk `expired` check; (e⁗⁗.3) `adsmt-quant/src/ematch.rs:106 substitute_in` `t.alpha_eq(from)` → `t == from` (Arc::ptr_eq; `extend_with_equalities` feeds ground UF congruence equalities so `from`/`to` are hash-cons canonical — verify the lone call site `ematch.rs:91` is ground-only); (T0'''') extend the (T0''') deadline cascade into the E-matching phase — `expired` checks inside `extend_with_equalities`'s `for (a,b) in equalities` / `for t in &snapshot` loops so rlimit ≥ 5 s is *caught* rather than running ~25 s to natural exit.  Workspace grep for `iter().any(.*alpha_eq` after (e⁗⁗.3) to confirm closure.  Predicted: rlimit ≥ 5 s resolves to a clean budget-bound `unknown`, Mode C' wall toward §3.5.J ≤ 1 500 ms |

## 9. What we ask of adsmt

In priority order:

1. **(e⁗⁗.1) take the prototype-validated `derive_equalities`
   `HashSet<(Term, Term)>` dedup into adsmt proper** — the
   verus-fork working-tree prototype already confirms it turns
   the ∞ hang finite and keeps adsmt-theory tests green.  The
   diff is in §5/§5.5.
2. **(e⁗⁗.3) `ematch.rs:106 substitute_in` `t.alpha_eq(from)` →
   `t == from`** — the residual 25 s hot path, called from
   `extend_with_equalities` over universe × equalities.
   Ground-canonical so `==` (Arc::ptr_eq) is exact; verify the
   sole call site `ematch.rs:91` is ground-only.
3. **(T0'''') deadline cascade into the E-matching phase** —
   `expired` checks inside `extend_with_equalities`'s loops so
   rlimit ≥ 5 s is caught rather than running ~25 s to natural
   exit.  This is why the budget isn't binding on this phase
   yet.
4. **(e⁗⁗.2) (T0''') into `derive_equalities`** + **workspace
   grep** `iter().any(.*alpha_eq` after (e⁗⁗.3) to confirm the
   pattern is closed.

After (e⁗⁗.1) + (e⁗⁗.3) + (T0''''), rlimit ≥ 5 s should resolve
to a clean budget-bound `unknown` and §3.5.J is finally
measurable end-to-end — I'll run the full Mode C' 3-run +
variance on a quiet host and report whether the wall lands in
the ≤ 1 500 ms window.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-07
