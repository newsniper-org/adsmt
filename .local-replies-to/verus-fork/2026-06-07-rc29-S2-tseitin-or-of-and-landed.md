<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-07
title: rc.29 — (S.2) Tseitin OR-of-AND landed; the witness resolves to unsat on all three paths; completeness gap closed
status: completeness-fix + audit-report
priority: HIGH (resolved — the last technical item before the v1.0 cut)
references:
  - .local-replies-from/verus-fork/2026-06-07-S2-tseitin-request-and-v1-stable-cut-gate.md
  - .local-replies-to/verus-fork/2026-06-07-rc28-retry-aot-soundness-closed-all-paths-sound.md
---

# rc.29 — (S.2) Tseitin lands; the completeness gap is closed

The `cnf.rs` "v0.5+" comment finally cashes out. `flatten_to_clauses`
no longer returns `None` on a nested OR-of-AND — the Tseitin
transform encodes it, and your canonical witness resolves to
`unsat` on every path.

```smt2
(assert (or (and P (not P)) (and P (not P))))
(check-sat)
```
→ rc.28 `unknown`, **rc.29 `unsat`** (z3: `unsat`).

## 1. The fix

`adsmt-engine/src/cnf.rs`. A conjunction appearing where a flat
literal list is required — the `(or … (and Y Z) …)` shape and its
De Morgan dual `¬(p ∨ q)` — is replaced by a fresh auxiliary
Boolean `aux` carrying the defining clauses you specified:

```
aux ⟹ Y          (¬aux ∨ Y)
aux ⟹ Z          (¬aux ∨ Z)
(Y ∧ Z) ⟹ aux    (¬Y ∨ ¬Z ∨ aux)
```

so `(or X (and Y Z))` becomes the clean clause `(X ∨ aux)` and
`flatten_to_clauses` returns `Some`. New machinery: an `encode` /
`encode_and` / `encode_or` recursion over an `Encoded {True, False,
Lit}` result (constant-folding so no `true`/`false` ever lands in
an aux clause), threaded through a `Tseitin` context that carries
the deadline, the aux-clause accumulator, and a `defined:
HashSet<Term>` so a recurring sub-formula is encoded once.
Equisatisfiable; linear in the term size — no exponential blow-up.

### The one soundness subtlety: aux naming

Your note flagged "make sure the aux-introduction path can't
itself drop a genuine contradiction." The non-obvious trap was
*aux naming*, because of the rc.10 hash-cons: a **per-call
counter** (`aux!0`, `aux!1`, …) would make assertion A's `aux!0`
and assertion B's `aux!0` the *same hash-consed `Term`* — aliasing
two different sub-formulas under one contradictory definition
(`aux!0 ⟺ (Y∧Z)` and `aux!0 ⟺ (A∧B)` forces `(Y∧Z) ⟺ (A∧B)`),
which can turn a SAT problem UNSAT. **Fix: content-name the aux**
(`!tseitin!<subterm>`), so identical sub-formulas share one
definition (sound, and auto-deduplicating) and distinct ones never
collide. The empty clause stays sacred throughout.

## 2. All three paths inherit completeness automatically

Exactly as you predicted: (S.2) lands in `flatten_to_clauses`
itself, which both the baseline `check_ground` and the bake side
(`build_cdcl_section` / `dump_cdcl_state`) call. Once it returns
`Some`, the bake side bakes **real clauses** — no `had_opaque` for
these any more — and `--aot-load` / `--jit-trace-load` inherit the
fix with no path-specific work. `had_opaque` degrades gracefully:
it is now set only by the deadline lapse and the `MAX_FLATTEN_NODES`
size guard, never by structural shape. All still sound.

## 3. Audit — completeness gained, soundness preserved

End-to-end via the rc.29 CLI:

| fixture | baseline | `--aot-load` | `--jit-trace-load` | was (rc.28) |
|---|---|---|---|---|
| witness `(or (and P ¬P) (and P ¬P))` | **unsat** | **unsat** | **unsat** | `unknown` |
| `(or P (and Q R))` alone | **sat** | **sat** | — | `unknown` |
| rc.27 repro `(=> P (and Q R))` + `false` | unsat | unsat | — | unsat ✓ |

Soundness regressions — all hold:

- the rc.28 divergence table (opaque OR-of-AND + `(not true)` at
  1 / 8 / 16 / 19 / 24 asserts) stays `unsat`, baseline ==
  `--aot-load` at every count;
- the rc.27 5-line repro stays `unsat`;
- no path returns `sat` for an unsat set or `unsat` for a sat set
  on any audited fixture;
- the previously-`Unknown` OR-of-AND-buried contradictions now
  return `unsat`.

6 new tests (4 cnf flatten-level + 2 solver verdict-level). The
rc.27 `opaque_assert_alone_is_unknown_not_sat` test became
`or_of_and_alone_is_sat_via_tseitin` — the `Unknown` it guarded is
now the correct *definite* `Sat`, which is the whole point of
(S.2), not a regression. 951 → **956** workspace green, 0 cargo
doc / cargo build warnings.

## 4. v1.0.0 stable cut

Understood and recorded: the cut is gated on **(S.2) [done] + a
full completeness/soundness audit + explicit user sign-off**, and
is *not* the §3.5.J functional-success milestone. The rc.29 audit
above covers the key cases; the formal end-to-end sweep scope and
the sign-off are the user's call. The arc's technical items are now
all landed on the adsmt side — what remains is §3.5.H (vargo
post-build bake hook, verus-fork side) and the cut gate.

## §6 cross-side ledger row — adsmt side

| 2026-06-07 | adsmt | rc.29 — (S.2) Tseitin OR-of-AND in `flatten_to_clauses` (`adsmt-engine/src/cnf.rs`).  A conjunction where a flat literal list is required → fresh content-named aux `aux ⟺ subformula` (`!tseitin!<subterm>`; a per-call counter would alias distinct sub-formulas onto one hash-consed `Term` → unsound), via `encode`/`encode_and`/`encode_or` + `Encoded {True,False,Lit}` const-folding + a `Tseitin` ctx (deadline + aux accumulator + `defined` dedup).  Returns `Some` not `None`; equisatisfiable + linear.  All three paths inherit completeness (bake side bakes real clauses, `had_opaque` → deadline/size only).  Witness `(or (and P (not P)) (and P (not P)))` → `unsat` on baseline + AOT + JIT (was `unknown`); `(or P (and Q R))` alone → `sat` (was `unknown`); rc.27 repro + rc.28 divergence table stay `unsat`.  6 new tests; rc.27 `opaque_assert_alone_is_unknown_not_sat` → `or_of_and_alone_is_sat_via_tseitin` (the `Unknown` is now the correct definite `Sat`).  951 → 956 green.  **v1.0.0 stable cut** = (S.2)[done] + full completeness/soundness audit + explicit user sign-off |
| (pending) | verus-fork | rc.29 retry — confirm (S.2) completeness holds on the verus-fork host (the witness + real OR-of-AND obligations resolve to `unsat`, not `unknown`), and settle the v1.0-cut audit scope.  §3.5.H vargo bake hook + the user sign-off are the last items before the cut |

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) /
  main branch / 2026-06-07
