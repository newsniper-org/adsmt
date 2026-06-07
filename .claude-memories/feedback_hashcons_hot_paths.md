---
name: Take the Arc::ptr_eq short-circuit on hash-consed types in hot paths
description: Whenever a hash-consed type (Term, Type, …) is compared / hashed / looked-up / stored in an inner loop, route the comparison through `Arc::ptr_eq` first AND prefer `(Index)Set<T>::contains` over `Vec<T>::iter().any(custom_eq)` for dedup-shaped containers. Post-rc.10 `Term::Hash/Eq` is pointer-based O(1); `Type` after rc.22 has hand-rolled `PartialEq` with `Arc::ptr_eq` short-circuit; `alpha_eq_rec` after rc.22 has a top-level `Arc::ptr_eq` fast-path; UF/abductive/ematch/quant `Vec<Term>` dedup containers after rc.23/rc.24 are `IndexSet<Term>` / `HashSet<Term>`. Seven measured incidents — CDCL String-keyed maps (rc.21: 5 955→1 923 ms, 67 %), `alpha_eq_rec` (rc.22), `Type::eq` (rc.22), UF iter().any(alpha_eq) (rc.23), ematch+quant dedup sites (rc.24), UF close() naive O(N²) congruence → signature-hashed (rc.25), ematch extend_match/substitute_in + Combination::check Nelson-Oppen dedup (rc.26). After rc.26 the SMT-solving hot path is FULLY de-quadratified; the only remaining iter().any(alpha_eq) production sites are cold abduction (off the SMT path, deliberately left). TWO CRITICAL PROCESS LESSONS: (1) grep the pattern WORKSPACE-WIDE every cycle — rc.23 fixed the narrowly-grepped UF site and the wall held flat because the real hot site was the identical pattern one crate over in ematch.rs; (2) after removing an O(N²) bottleneck, ALWAYS re-profile from scratch even when the removal is correct — rc.24's correct ematch fix made the wall go UP 7× because the slow build had been an accidental throttle masking UF::close()'s downstream O(N²) congruence closure. The "wall went up after a correct optimization" signature means you unblocked a worse downstream cost — bisect + re-profile, don't revert.
type: feedback
---

When a hot path touches a hash-consed type — `Term` (rc.10
hash-cons via `scc::HashIndex`), `Type` (`Arc<TyVar>` /
`Arc<TyConst>` / `Arc<Type>` payloads), `Arc<Var>`, etc. —
**route the comparison / lookup through `Arc::ptr_eq` before
falling back to structural recursion**.  Three distinct
surfaces this rule covers:

## 1. HashMap / HashSet keys

Key on the hash-consed type directly:

```rust
// Yes
HashMap<Term, V>             // Hash = ptr-hash, Eq = Arc::ptr_eq — O(1)

// No
HashMap<String, V>           // hash + traversal per probe + per-key malloc
                             // (lit.atom.to_string())
```

Boundary conversion (external API surfaces like
`CdclOutcome::Sat`'s `HashMap<String, bool>` model, CLI JSON
output, `.luart` wire format) keeps the String shape; convert
**exactly once** at the verdict / serialisation edge.  Sink
traits (`CdclEventSink::on_propagate(&str, …)`) keep `&str` —
call sites pay `term.to_string()` once per recorded *event*,
not once per propagation step.

## 2. Structural equality fast paths

Hand-roll `PartialEq` (or insert a guard at the top of a
recursive eq helper) to short-circuit on `Arc::ptr_eq` before
walking the children:

```rust
// Type (adsmt-core/src/ty.rs, rc.22)
impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::App(fa, xa), Type::App(fb, xb)) => {
                (Arc::ptr_eq(fa, fb) || **fa == **fb)
                    && (Arc::ptr_eq(xa, xb) || **xa == **xb)
            }
            …
        }
    }
}

// alpha_eq_rec (adsmt-core/src/term.rs, rc.22)
fn alpha_eq_rec(a: &Term, b: &Term, a_bound: …, b_bound: …) -> bool {
    if a_bound.is_empty() && b_bound.is_empty() && Arc::ptr_eq(&a.0, &b.0) {
        return true;
    }
    match (a.kind(), b.kind()) { … }
}
```

Soundness must be argued explicitly:

- For `Type::eq` the `||` falls through to structural
  comparison on a ptr-eq miss — the equivalence relation is
  unchanged, the ptr-eq branch is pure performance.
- For `alpha_eq_rec` the `bound.is_empty()` guard restricts
  the fast path to closed sub-terms in identical bound
  contexts — two open terms can share an Arc yet sit under
  different binders and be α-distinct.  The empty-stack
  guard ensures the fast path only fires at top-level entry
  points (where every `set.iter().any(|x| x.alpha_eq(t))`
  call lands), which is where the verus_smoke flamegraph
  showed hot.

Never replace a derive `Hash` with a hand-roll when the
PartialEq is hand-rolled — keep them returning identical
equivalence relations so `Eq`/`Hash` reflexivity stays
intact.

## 3. Container-shape: `Vec<T>` + `iter().any(custom_eq)` → `(Index)Set<T>::contains`

The third surface — and the one that bites *after* (1)
and (2) land — is dedup-shaped containers.  Even with the
inner alpha_eq fast-path at O(1) on the common case, an
outer `set.iter().any(|x| x.alpha_eq(t))` is still O(N)
per probe; in a hot loop that's invoked ~N times per
`(check-sat)` the wall cost is O(N²).

```rust
// Before — O(N²) over the loop body
self.known: Vec<Term>;
fn register(&mut self, t: &Term) {
    if !self.known.iter().any(|kt| kt.alpha_eq(t)) {  // O(N) per call
        self.known.push(t.clone());
    }
}

// After — O(N) over the loop body
self.known: IndexSet<Term>;
fn register(&mut self, t: &Term) {
    self.known.insert(t.clone());                     // O(1) per call,
                                                      // insert handles dedup
}
```

### Picking the container

| use case | container |
|---|---|
| dedup-only scratch set (never iterated, never indexed, never serialised) | `std::collections::HashSet<T>` — smallest per-entry overhead |
| field that needs `truncate(n)` rollback, `for i in 0..N; for j in (i+1)..N` indexed pair scan, or reproducible iteration order | `indexmap::IndexSet<T>` — preserves insertion order, adds `get_index` + `truncate` |
| keyed map needing reproducible value enumeration | `indexmap::IndexMap<K, V>` instead of `HashMap<K, V>` |

`indexmap` is already a workspace dep (used in
`adsmt-core` for substitution maps), so it carries no
new-dependency cost.  The choice between `HashSet` and
`IndexSet` is a per-call-site decision — UF's
`pos_atoms` / `neg_atoms` / `known` needed `IndexSet` for
rollback + indexed-loop preservation; the abductive
`Candidate::merge` dedup scratch used a one-shot
`HashSet` because it's never iterated.

### Soundness checks

- **Hash-cons coverage.**  `(Index)Set::contains` uses
  `Hash` + `Eq`.  For `Term` (rc.10), `Hash` is
  pointer-hash and `Eq` is `Arc::ptr_eq` — so structurally-
  identical ground terms (same Arc) probe-hit, but two
  open terms under different binder contexts could
  share an Arc and falsely probe-hit.  In practice this
  is non-issue because every UF / abductive caller
  operates on closed (Skolemized) terms.
- **Reproducibility.**  `HashSet` iteration order is
  non-deterministic (`RandomState` seed per-process);
  `IndexSet` preserves insertion order.  If the
  container is iterated to emit certificate text,
  union-find pair walks, or any sequence whose order
  is observable downstream, use `IndexSet`.  If it's a
  pure dedup scratch, `HashSet` is fine.
- **Rollback shape.**  `IndexSet::truncate(n)` is the
  drop-in replacement for `Vec::truncate(n)`.  `HashSet`
  has no length-based truncate; rollback would need a
  per-scope delta vec or snapshot clone.

### ALWAYS grep workspace-wide, every cycle

The single most expensive process mistake across this
rule's history: **scoping the audit grep too narrowly**.
The verus-fork rc.22 reply scoped its grep to
`adsmt-theory/src/uf.rs` and reported it as the hot site;
rc.23 fixed exactly that and the wall didn't move because
the *actual* dominant caller was
`adsmt-quant/src/ematch.rs::TermUniverse::insert` — the
identical pattern in a different crate.  The rc.23
verus-fork reply then claimed `ematch.rs:29` was the
*only* remaining instance; a workspace-wide grep at rc.23
HEAD found **eight more** in production code.

Run this every cycle, over the *entire* workspace, before
declaring the pattern eliminated:

```sh
grep -rnE 'iter\(\)\.any\([^)]*\.alpha_eq' \
    adsmt-*/src --include='*.rs' | grep -v test
# and the String-key variant:
grep -rnE 'HashMap<String|HashSet<String' \
    adsmt-*/src --include='*.rs' | grep -v test
```

A clean run (only doc-comments + deliberately-cold sites)
is the bar for "pattern eliminated", not a single-file
grep.

### Audit locations (workspace-wide grep, rc.24)

Fixed:

- `adsmt-theory/src/uf.rs` `known`/`pos_atoms`/`neg_atoms`
  → `IndexSet<Term>` — **rc.23 (e''.1)** `5d347c2`.
- `adsmt-abduce/src/sld.rs::Candidate::merge` → one-shot
  `HashSet<Term>` — **rc.23 (e''.2)** `e2c1761`.
- `adsmt-quant/src/ematch.rs::TermUniverse::terms` →
  `IndexSet<Term>` + `contains` — **rc.24 (e'''.1)**
  `c54e71c`-successor (the actual 97.5 %-of-cycles
  hot site, missed by the rc.22/rc.23 greps).
- `adsmt-engine/src/quant.rs` Tier-classification
  `universe.contains` + `instantiate_one` seen-set
  `HashSet<String>`→`HashSet<Term>`;
  `adsmt-engine/src/solver.rs` `instantiations`
  `Vec`→`IndexSet` — **rc.24 (e'''.2)**.
- `adsmt-core/src/theorem.rs::union_hyps`,
  `adsmt-engine/src/quant_conflict.rs::conflict_instantiate`,
  `adsmt-theory/src/polite.rs::max_disequality_clique`
  (parallel `HashSet` scratch, `Vec` accumulator order
  preserved); `adsmt-abduce/src/minimize.rs::subsumes`
  (subset test via `HashSet` from `b`) — **rc.24 (e'''.3)**.

Covered by the (e.1) α-eq fast path (single comparisons,
not dedup loops): `adsmt-abduce/src/sld.rs:136`,
`adsmt-core/src/rule.rs:46, 88`,
`adsmt-quant/src/ematch.rs:78` (`substitute_in`).

Deliberately left as `Vec` (cold path + public-API
constraint, documented in code):
`adsmt-abduce/src/workflow.rs::is_accepted` (scans
`Vec<AcceptedHypothesis>` struct field) /
`is_rejected` (`rejected: Vec<Term>` exposed via the
public `rejected() -> &[Term]` accessor).  Abduction is
off the SMT solving path; converting would restructure a
struct or break a slice-returning accessor for no
measurable gain.

### A throttle removal can EXPOSE a masked downstream O(N²)

rc.24's (e'''.1) was *correct* — the `TermUniverse`
`Vec → IndexSet` migration made `collect_universe` O(N),
exactly as intended.  But the verus_smoke wall went **up
7×** (Mode A 3 971 → 26 832 ms), because the slow O(N²)
universe build had been an *accidental throttle*: the
engine deadline-fired *inside* `collect_universe` at ~4 s
and never reached the next phase.  Making the build fast
let the engine fall into the phase the throttle was
hiding — `UF::close()`'s pre-existing naive
O(N²·rounds·alpha_eq) congruence closure over the now-
fully-built ~5 665-term universe (rc.25 e⁗.1 fixed it
with signature hashing).

Lesson: **after removing an O(N²) bottleneck, always
re-profile from scratch — even when the removal is
provably correct.** A fast inner phase can surface a
slow outer phase the bottleneck was masking. The "wall
went *up* after a correct optimization" signature is the
tell: it means the optimization unblocked a worse
downstream cost, not that it regressed. Bisect to the
commit, then profile the *new* hot path (which will be a
different function/phase, not the one you just fixed).

Corollary: a deadline check is not a substitute for a
correct algorithm, but its *absence* turns an O(N²)
inner loop into a wall-clock-unbounded one.  The rc.25
(T0''') theory-phase deadline cascade (`Theory::set_deadline`
+ `Uf::close()` per-round `expired` check → `Unknown`)
is the backstop: even if a future phase is accidentally
O(N²) again, it yields to the budget instead of spinning.

### The throttle-unmask chain marches layer by layer

Each correct fix exposed the next-slowest phase, and the
chain ran through the entire solving pipeline before it
terminated:

CDCL String keys (rc.21) → term/type α-eq (rc.22) → UF
membership (rc.23) → ematch universe (rc.24) → UF
congruence `close()` (rc.25) → UF `derive_equalities`
dedup (rc.25-retry, user-landed) → ematch
`extend_match` / `substitute_in` + `Combination::check`
Nelson-Oppen dedup (rc.26).

Each link was the *same* `Vec<T> + iter().any(custom_eq)`
or recursive-`alpha_eq`-where-`==`-suffices shape, one
phase deeper.  **The terminating condition is a clean
workspace-wide grep, not a flat wall** — the wall stays
high (or moves *up*) at every intermediate step because
the throttle just relocated.  After rc.26 the
SMT-solving hot path (CDCL → theory combination → UF →
quantifier E-matching) is fully de-quadratified; the
only remaining `iter().any(alpha_eq)` production sites
are in **abduction** (`abducible.rs` abducible lookup,
`workflow.rs` accept/reject membership), which is *off*
the SMT solving path (it fires only on a stuck ground
check when the caller asked for abductive output) and is
deliberately left (cold + public-API / struct-field
constraints).

**Why:** Seven measured incidents, all the same family —
an O(1) handle (or a near-linear standard algorithm)
existed but the hot path used a quadratic / allocating
shape instead.

| cycle | surface | wall before | wall after | commit |
|---|---|---:|---:|---|
| rc.21 | `CdclState` HashMap keys (`String → Term`) | 5 955 ms | 1 923 ms | `de0aedb` |
| rc.22 | `Term::alpha_eq_rec` recursion (`Arc::ptr_eq` guard) | ~3 670 ms est | ~50 ms est | `c54e71c` |
| rc.22 | `<Type as PartialEq>::eq` (hand-rolled `Arc::ptr_eq`-first) | ~1 010 ms est | ~30 ms est | `d01d78a` |
| rc.23 | UF `Vec<Term>` + `iter().any(alpha_eq)` → `IndexSet<Term>::contains` | ~3 600 ms est | ~50 ms est | `5d347c2` |
| rc.24 | ematch `TermUniverse` + engine quant dedup sites (`Vec`→`IndexSet`/`HashSet`) | ~3 800 ms est | ~50 ms est | `e'''.1`+`e'''.2` |
| rc.25 | UF `close()` naive O(N²) congruence → signature-hashed + `Arc::ptr_eq` roots | ~22 s est | tens of ms est | `e⁗.1`+`e⁗.2` |
| rc.25-retry | UF `derive_equalities` dedup → `HashSet<(Term,Term)>` norm_pair (user-landed) | ∞ hang | ~finite | `6a3f0cd` |
| rc.26 | ematch `extend_match`/`substitute_in` + `Combination::check` NO-dedup → `==` / `HashSet` | (E-matcher tail) | — | `e⁗⁗.3`+`e⁗⁗.4` |

The rc.23 → rc.24 jump is the *narrow-grep* cautionary
tale: rc.23 fixed the site the narrow grep named, the
wall held flat (Mode C' 4 635 → 4 581 ms, noise), and
only the workspace-wide re-profile + re-grep surfaced the
real hot site one crate over.  **The pattern hides
wherever the grep doesn't look.**

The rc.24 → rc.25 jump is the *throttle-unmask*
cautionary tale: a correct optimization made the wall
7× *worse* by unblocking a masked downstream O(N²).
**A correct fix that makes the wall worse means you
unblocked something — re-profile, don't revert.**

The rc.25 → rc.26 span is the *chain-termination* note:
the throttle-unmask marched through six more phases after
the first fix; the signal that it's *done* is a clean
workspace-wide grep (only comments + tests + cold
off-path sites), confirmed once the verus-fork retry
shows the wall finally drop into the budget window
rather than relocating again.

The rc.21 incident first surfaced as "+662 → +747 ms
regression rc.15 → rc.20" the verus-fork side carried as a
phantom "BCP fixpoint floor" for six cycles.  The rc.22
incidents surfaced on the verus-fork rc.21 retry flamegraph
once Mode C''s 23 ms variance signature pointed at
algorithmic work (not allocator jitter) on the verus_smoke
fixture — `alpha_eq_rec` was 62.16 % of cycles, `Type::eq`
17.20 %, together ~79 %.

**How to apply:**

- **Before** adding a new HashMap to a CDCL / matcher /
  theory-propagator / e-graph hot path: key on the
  hash-consed type directly.  String-keyed only for
  external API surfaces.
- **Before** writing a `match` on two `&T` values where
  `T` carries an `Arc` payload (Term, Type, Var, …): add
  an `Arc::ptr_eq` guard with the appropriate soundness
  argument (closed-context for α-eq; structural fallback
  for `||` chains).
- **When auditing** existing CDCL / theory / matcher / α-eq
  code, grep for:
  - `HashMap<String,` / `HashSet<String>` inside loop
    bodies
  - structural-recursion `match` arms that descend through
    `Arc::clone()` payloads without a `ptr_eq` check
  - `Display::fmt` results (`to_string()` /
    `format!("{}", t)`) used as keys / dedup signatures
- **When reviewing** a flamegraph: any structural-eq or
  hash-related symbol consuming > 1 % of cycles is a
  candidate.  Don't reach for an arena allocator or
  thread-local interner before checking that the existing
  hash-cons handles are being used at every comparison /
  lookup site downstream.
- **When testing** the recovery's impact, the
  `verus_smoke` 1063-line query (extracted from
  `/tmp/verus-log-adsmt/root.smt_transcript`) is the
  canonical wall-clock measurement vehicle for the
  prelude-shape pattern; the 5 000-Bool / 5 000-ternary-OR
  fixture (`.claude-notes/profiling/README.md`) is the
  canonical vehicle for the CDCL-shape pattern.
- **Diagnostic anchor**: the rc.21 Mode C' 23 ms variance
  signature is the post-allocator-fix shape; if a
  follow-on recovery preserves or shrinks the variance,
  the fix is algorithmic; if the variance grows, the fix
  introduced new allocator churn (most likely a missed
  `Arc::clone()` along the new path).
