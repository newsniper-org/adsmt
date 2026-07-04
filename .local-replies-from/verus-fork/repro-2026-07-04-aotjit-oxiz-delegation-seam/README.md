# repro — AOT/JIT vs the OxiZ-delegation seam (rc.42)

Derivation: `verus -V adsmt -V emit-lukb --log-all diff.rs` (the diff.rs of
repro-2026-07-03-fuel-unfolding-mbqi-gap/) → `.verus-log/root.smt2`
(1848 lines; prelude = 1..1728, 5 push/pop queries = 1729..1848).

## Steps
```
sed -n '1,1728p'    root.smt2 > prelude.smt2
sed -n '1729,1848p' root.smt2 > queries.smt2
lu-smt --aot-bake --aot-output prelude.luart prelude.smt2       # 12 ms, 28 KB

# [1] baseline / AOT / AOT+JIT on the FULL stream — verdicts unsat x5 everywhere,
#     walls statistically identical (3337 / 3345 / 3342 ms median-of-3):
lu-smt root.smt2
lu-smt --aot-load prelude.luart root.smt2
lu-smt --aot-load prelude.luart --jit-trace-emit-slim t.lutrace root.smt2
lu-smt --aot-load prelude.luart --jit-trace-load t.lutrace root.smt2

# [2] single-query replay (the §3.5.J designed window) — also no fire (589≈579 ms):
sed -n '1729,1753p' root.smt2 > q1.smt2 ; cat prelude.smt2 q1.smt2 > single1.smt2
lu-smt --aot-load prelude.luart --jit-trace-emit-slim t1.lutrace single1.smt2
lu-smt --aot-load prelude.luart --jit-trace-load t1.lutrace single1.smt2

# [3] §3.5.H suppression simulation — decls kept, prelude asserts elided:
python3 strip-prelude-asserts.py prelude.smt2 > prelude-decls-only.smt2
cat prelude-decls-only.smt2 queries.smt2 > suppressed-stream.smt2
lu-smt --aot-load prelude.luart suppressed-stream.smt2
#   → sat, unsat, sat, unsat, unsat in 8 ms — ob1/ob3 spurious `sat`,
#     NO unknown-symbol warnings: the 202 pre-asserted axioms never reach the solve.
```

`aotjit-bench.sh` runs the full matrix (median-of-3) including the lukb-path
(adsmtc/adsmtr) baselines and the verus-level env configs.
