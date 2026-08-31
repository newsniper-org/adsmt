<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# Proposal 5 (`:pattern` threading) — killed by measurement, 2026-08-31

The Zipperposition/Satallax research ranked "thread the elaborated lu-kb
trigger map into the native engine" 5th, and its adversarial critic re-ranked
it UP, arguing the real gap was pattern ARITY: `partition_quantifiers` peels one
binder per round via `dest_forall` against `QUANTIFIER_ROUNDS = 3`, while
`lower_with_triggers` already lowers the whole telescope in one step and
`lukb_solve.rs` throws that away by passing `TriggerMap::new()`.

Every structural claim there is TRUE. The conclusion is not, and four probes
take it apart. Run them with `target/release/examples/lukb_solve`.

```
p5-two-binder.lukb        ∀x y. Add(x,y) = x+y  trigger Add(x,y)   -> unknown (wall A)
p5-one-binder.lukb        ∀x.   Dbl(x)   = x+x  trigger Dbl(x)     -> unknown (wall A)
p5-hand-instantiated.lukb no quantifier at all, the instance written out
                                                                    -> unknown (arith equality)
p5-no-uf.lukb             no UF wrapper either:  s! = a! + b!       -> unknown (arith equality)
```

z3 and cvc5 answer `unsat` on all four.

The ONE-binder control fails identically to the two-binder one, so arity is not
it. The HAND-INSTANTIATED probe fails with no quantifier present at all, so
instantiation is not it. And the last probe fails with no UF in sight, so the
wrapper is not it either.

What is left is the actual blocker: **`LinArith` cannot represent a linear
equality over three variables.** Its store is bounds plus a two-variable pool
(`x = y ± k`); `s = a + b` has no slot. Threading triggers would have delivered
instances into an arithmetic solver that cannot use them.

## What the measurement DID find

Classifying all 66 dropped arithmetic equalities from the 209-row native sweep
(`../2026-08-31-n64-native-false-sat-verdicts.tsv`) by top-level shape:

```
62   var = UF-application      (r! = Add a! b!,  tmp%1 = Mul x! x!,  SZ = const_int …)
 4   UF-application = var
 0   UF-application = arithmetic expression
 0   pure multi-variable linear
```

All 66 are `variable = opaque application`. That is precisely the shape N3
already made representable FOR COMPARISONS by minting a Nelson-Oppen interface
variable per UF-application operand: intern the application as `%if#N%` and
`r! = Add(a!,b!)` becomes `r! = %if#N%`, a TWO-variable equality the existing
pool handles.

So the slice worth building is not trigger threading — it is extending N3's
interface-variable interning from comparisons to positive equalities, keeping
N3's direction posture: record the equality, still return `AssertResult::Ignored`
so the backstop stays armed. Arithmetic gains refutation power (the `unsat`
direction these proof obligations want) without licensing a `sat` over an
arrangement nothing discharges — which is the trade #434 shows the delegated
side getting wrong.
