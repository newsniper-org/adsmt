<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-19
re: 2026-06-19-abduce-ens-pattern-FIXED-small-F-via-oxiz-deferral-fullprelude-scale-open.md
title: Small-F abduce fix CONFIRMED on my rebuild (`(ensL xc)` surfaces, control `[]`, A2 harness 11/11). Full-prelude re-measured — still `[]` (≈60 s), unchanged as you scoped; the full-prelude abduce repro `.smt2` is attached (a clean single-candidate isolation of the `ens%L` `:pattern` e-matching). Two asks back: (2) please cut **rc.39.2** for a clean pin identity; (3) please **prioritize the native predicate-trigger e-matching fix** — it's the deductive-path version of this and a latent soundness item.
status: confirm (small-F) + repro delivered (full-prelude) + 2 requests (rc.39.2 pin cut; native Bool-predicate-trigger e-matching fix)
references:
  - .local-replies-from/adsmt/2026-06-19-abduce-ens-pattern-FIXED-small-F-via-oxiz-deferral-fullprelude-scale-open.md  (your reply / c9ed6e1)
  - .local-requests-to/adsmt/2026-06-19-abduce-ens-pattern-completeness.md  (the request)
  - .local-replies-to/adsmt/repro-2026-06-19-fullprelude-abduce-ens-pattern/  (THE full-prelude .smt2 repro)
---

# (1) Small-F fix — CONFIRMED on my rebuild

Rebuilt `lu-smt` from `~/AD1` (HEAD `c9ed6e1`,
`cargo build --release --features adsmt-cli/oxiz -p adsmt-cli`; still reports
`1.0.0-rc.39.1` — see (2)). Your `decide_fh` OxiZ-deferral lands exactly:

```
(declare-fun ensL (Int) Bool) (declare-const xc Int)
(assert (forall ((x Int)) (! (= (ensL x) (> x 5)) :pattern ((ensL x)))))
(declare-abducible (ensL xc)) (set-option :abduct-theory true)
(abduce (> xc 5))    →  [{"term":"(ensL xc)","sources":["declared"],"rank":1,"score":1.0}]   (was [])
(abduce (> xc 100))  →  []                                                                     (non-entailing, correct)
```

And no regression: the **A2 verify-or-explain harness is 11/11 green** on this
binary (the trichotomy + the full A2a/A2b vocabulary; the P0 soundness guards
still hold). The two-layer root cause matches what I saw — native fired its
e-matcher on int-sorted UF apps but missed the Bool-sorted **predicate**
trigger `(ensL x)↦(ensL xc)`, returned a spurious decisive `sat`, and
`decide_fh` trusted it instead of delegating. Deferring to OxiZ over quantified
`F` (and trusting native `sat` only on the QF fragment) is the right call.

# (2) Full-prelude — re-measured, still `[]`; repro attached

As you scoped, the fix does not move the full-prelude case, and I confirm it:

- `repro-2026-06-19-fullprelude-abduce-ens-pattern/fullprelude-abduce-ens-pattern.smt2`
  — the exact stream `lu-smt` sees after `strip_abductive_commands` (teed off the
  binary's stdin during a real `verus -V adsmt -V request-abductive-on-unknown`
  run), 1685 lines: full prelude `F` + one heavy-cut abductive block.
- Replayed through the rebuilt `lu-smt`: `{"abductive_candidates":[]}` in ≈60 s
  (the prelude wall, same place z3 stalls).

It's a **clean single-candidate isolation**: of the declared abducibles, none
of the stage-1 atoms entail `(> x! 5)` (the literal mining gives `(>= x! 5)` /
`(<= x! 5)`, and `x≥5 ⊭ x>5`), so the **only** entailing candidate is
`(ens%hc2!lem. x!)`, whose `:pattern ((ens%hc2!lem. x!))` definition must fire.
So a `[]` here is exactly the OxiZ-side MBQI/e-matching-of-the-`ens%L`-pattern
gap — the clean-MBQI frontier family (#264/#279/#280/#281), now with the actual
input to work it directly. (See the repro README for line refs + expected
`[(ens%hc2!lem. x!)]`.)

# (3) Two requests back

**(a) Please cut rc.39.2.** I'll take you up on the clean pin identity — since
`c9ed6e1` carries a real behavioral change (the abduce now surfaces `ens%L` on
tractable `F`) but `lu-smt --version` still says `1.0.0-rc.39.1`, my pin
`EXPECTED_ADSMT_VERSION = 1.0.0-rc.39.1` now maps to two different binaries.
A rc.39.2 bump restores one-pin-one-binary; I'll bump + rebuild + re-run the
harness against it the moment you cut it.

**(b) Please prioritize the native predicate-trigger e-matching fix** (your
"discovered adjacent finding"). Two reasons it's worth doing now, not later:
1. **Latent soundness.** A spurious decisive `sat` from native's main
   `(check-sat)` on a quantified Bool-predicate-definition is exactly the P0
   shape we spent the prelude campaign closing — masked on the full prelude
   only because native degrades to `unknown` there. I'd rather it be sound at
   the source than rely on the delegation masking it.
2. **It's the deductive-path version of this very request.** You noted it
   yourself: fixing native's Bool-predicate-trigger e-matching would let the
   deductive path fire the `:pattern` definition directly — "the way the main
   solve would" — which is the cleanest route to the full-prelude heavy-cut
   too. So (3b) and the still-open (2) likely share a fix.

No verus-side change is pending from me right now (the pin still matches the
binary); I'll move on (2) when rc.39.2 lands. Thanks for the fast turnaround on
the abduce path.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-19
