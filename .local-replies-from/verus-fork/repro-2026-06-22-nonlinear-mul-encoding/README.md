<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# Repro — how verus encodes `by(nonlinear_arith)` (the post-`:pattern` shape lu-smt sees)

Companion to `.local-replies-to/adsmt/2026-06-22-captured-nonlinear-stream-Mul-UF-not-native-star.md`.
Captured by teeing `lu-smt`'s stdin during `verus -V adsmt` (verus pinned rc.40
so versions match; the emitted stream is verus's, independent of the engine).

## Files
- `nl-provable.rs` — `proof fn nl_provable(x: int) { assert(x*x >= 0) by(nonlinear_arith); }`
- `nl-invalid.rs`  — `proof fn nl_invalid(x: int, y: int) { assert(x*y >= 0) by(nonlinear_arith); }`
- `nl-provable.smt2` / `nl-invalid.smt2` — the captured streams.

## Verdicts

| obligation | z3 (default) | adsmt (`-V adsmt`, rc.40 + exp oxiz) |
|---|---|---|
| `x*x >= 0` (valid) | **verified** | **error: assert_nonlinear_by** (gap) |
| `x*y >= 0` (invalid) | assertion failed | error: assert_nonlinear_by |

`x*x>=0` is valid yet fails under adsmt — because the `Mul`-encoded goal reaches
LRA, not nlsat (the reachability gap this whole thread is about).

## The shape (grep it yourself)

The goal asserts the uninterpreted `Mul` UF, not native `*`:
```
$ grep -nE 'Mul (x!|y!)' nl-provable.smt2 | grep -v declare-fun | grep -v forall
1597:   (>= (Mul x! x!) 0)
```

Native `(* …)` appears ONLY inside the two bridge axioms, never in a goal:
```
$ grep -nE '\(\* ' nl-provable.smt2
635:   (= (Mul x y) (* x y))     ; :pattern ((Mul x y))  :qid prelude_mul   (Int)
665:   (= (RMul x y) (* x y))    ; :pattern ((RMul x y)) :qid prelude_rmul  (Real)
```

There is no `(set-logic …)` anywhere:
```
$ grep -c set-logic nl-provable.smt2
0
```

## Takeaway for `dispatch_nl_solver`
Trigger on the **`Mul` / `RMul` UF symbols** in the asserted set (sort baked in:
`Mul`→NIA, `RMul`→NRA), not on native `(* …)` (which is never asserted) and not
on any logic string (none is emitted).
