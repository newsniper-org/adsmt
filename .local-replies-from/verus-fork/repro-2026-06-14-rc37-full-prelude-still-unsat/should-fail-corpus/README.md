# verus -V adsmt should-fail soundness corpus

Ground truth (z3, default backend):

| file | z3 verdict | adsmt MUST produce |
|---|---|---|
| `pass-must-VERIFY.rs` (`x>0 ∧ y>0 ⊢ x+y>0`) | 1 verified, 0 errors | verify |
| `fail-must-ERROR.rs`  (`y>0 ⊬ x+y>0`)        | 0 verified, 1 errors | **error** |
| `false-must-ERROR.rs` (`⊢ false`)            | 0 verified, 1 errors | **error** |

A backend that judges the prelude `F` unsat will VACUOUSLY verify the two
should-error cases (F ∧ ¬G trivially unsat). The corpus passes iff all
three rows match z3. As of rc.37 (oxiz 0.2.4-redesign 369a3a8),
`fail`/`false` STILL verify — unsound.

Run: `verus -V adsmt <file>` for each.
