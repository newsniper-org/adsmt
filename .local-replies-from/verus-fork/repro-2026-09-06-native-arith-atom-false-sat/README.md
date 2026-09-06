# repro — native path returns `sat` on hypothesis-free Int tautologies

Built at AD1 `0eaa7e2` (oxiz `808d7f5`), release `adsmtc --features "cas oxiz"`.
Run each with delegation OFF and ON:

```
ADSMT_NO_DELEGATION=1 adsmtc <f>.lukb     # native
adsmtc <f>.lukb                            # delegated (control)
```

| file | goal | native | delegated |
|---|---|---|---|
| `closes-01-refl.lukb`      | `n = n`         | unsat   | unsat |
| `closes-02-ge-refl.lukb`   | `n >= n`        | unsat   | unsat |
| `closes-03-syntactic.lukb` | `n + 1 = n + 1` | unsat   | unsat |
| `unknown-01-succ-gt.lukb`  | `n + 1 > n`     | unknown | unsat |
| `FALSESAT-01-add-zero.lukb`| `n + 0 = n`     | **sat** | unsat |
| `FALSESAT-02-sub-self.lukb`| `n - n = 0`     | **sat** | unsat |
| `FALSESAT-03-zero-add.lukb`| `0 + n = n`     | **sat** | unsat |
| `FALSESAT-04-mul-one.lukb` | `n * 1 = n`     | **sat** | unsat |
| `FALSESAT-05-neg-neq.lukb` | `not (n + 0 != n)` | **sat** | unsat |

Pattern: the goal closes when both sides are **syntactically identical**; the
moment arithmetic normalisation is required the native path stops interpreting
the atom — concluding *satisfiable* for equalities (a wrong verdict) and
abstaining for inequalities.

Hypothesis position is unaffected — these all close natively:

| file | |
|---|---|
| `ctrl-hyp-01.lukb` | `assume n + 0 = n ⊢ true` → unsat |
| `ctrl-hyp-02.lukb` | `assume n + 0 = n ⊢ n = n` → unsat |
| `ctrl-hyp-03-named-sum.lukb` | `assume z = n + 1 ⊢ z > n` → **unsat** |

`ctrl-hyp-03` is the diagnostic: naming the sum in a hypothesis closes what the
same arithmetic inside the goal atom does not.
