#!/usr/bin/env bash
# AOT/JIT with-vs-without comparison on the -V emit-lukb fixture family (diff.rs).
# Part A: lukb path (adsmtc + adsmtr) — no AOT/JIT surface exists → cold baseline only.
# Part B: lu-smt standalone on the dual-emitted .smt2 — full AOT (.luart) / JIT (.lutrace) matrix.
set -u
cd /tmp/lukb-fidelity
AD=/home/ybi/AD1/target/release
LOG=.verus-log/root.smt2

ms() { date +%s%3N; }
# median-of-3 wall for "cmd... " → prints "med1 med2 med3 → median" and sets MED
run3() { # run3 <label> <expected-exit> <cmd...>
  local label=$1 exp=$2; shift 2
  local t=() code=0
  for i in 1 2 3; do
    local s=$(ms); "$@" >/dev/null 2>&1; code=$?; local e=$(ms)
    t+=($((e - s)))
  done
  IFS=$'\n' sorted=($(sort -n <<<"${t[*]// /$'\n'}")); unset IFS
  MED=${sorted[1]}
  printf '%-34s %6s ms  (runs: %s,%s,%s; exit %d%s)\n' "$label" "$MED" "${t[0]}" "${t[1]}" "${t[2]}" "$code" \
    "$([ "$code" -eq "$exp" ] && echo ' ✓' || echo " ✗ EXPECTED $exp")"
}

echo "=================== PART A — lukb path (NO AOT/JIT surface; cold each run) ==================="
for bin in adsmtc adsmtr; do
  total=0
  for i in 1 2 3 4 5; do
    run3 "  $bin ob$i.lukb" 1 $AD/$bin ob$i.lukb
    total=$((total + MED))
  done
  printf '%-34s %6s ms\n' "  ── $bin TOTAL (5 obligations)" "$total"
done

echo
echo "=================== PART B — lu-smt on the dual-emitted .smt2 (AOT/JIT matrix) ==================="
# split prelude/queries at the first (push)
sed -n '1,1728p'   "$LOG" > prelude.smt2
sed -n '1729,1848p' "$LOG" > queries.smt2
echo "prelude: $(wc -l < prelude.smt2) lines | queries: $(wc -l < queries.smt2) lines, $(grep -c '(check-sat)' queries.smt2) check-sats"

# verdict reference: whole file (exit code is last verdict; unsat=1)
echo "--- verdicts (must be unsat x5 everywhere) ---"
base_v=$($AD/lu-smt "$LOG" 2>/dev/null | grep -c '^unsat')
echo "baseline whole-file        : unsat x$base_v"

# AOT bake (one-time cost, measured separately)
s=$(ms); $AD/lu-smt --aot-bake --aot-output prelude.luart prelude.smt2 >/dev/null 2>&1; bake_code=$?; e=$(ms)
echo "aot bake: $((e - s)) ms (exit $bake_code) → $(ls -la prelude.luart 2>/dev/null | awk '{print $5}') bytes"
aot_v=$($AD/lu-smt --aot-load prelude.luart queries.smt2 2>/dev/null | grep -c '^unsat')
echo "aot-load + queries         : unsat x$aot_v"

# JIT slim-trace emit (on top of AOT), then replay
$AD/lu-smt --aot-load prelude.luart --jit-trace-emit-slim t.lutrace queries.smt2 >/dev/null 2>&1
echo "jit slim trace             : $(ls -la t.lutrace 2>/dev/null | awk '{print $5}') bytes"
jit_v=$($AD/lu-smt --aot-load prelude.luart --jit-trace-load t.lutrace queries.smt2 2>/dev/null | grep -c '^unsat')
echo "aot+jit replay             : unsat x$jit_v"

echo "--- walls (median of 3) ---"
run3 "  WITHOUT (whole-file stream)" 1 $AD/lu-smt "$LOG"
run3 "  WITH AOT (--aot-load+queries)" 1 $AD/lu-smt --aot-load prelude.luart queries.smt2
run3 "  WITH AOT+JIT (replay)" 1 $AD/lu-smt --aot-load prelude.luart --jit-trace-load t.lutrace queries.smt2
echo
echo "=================== PART C — verus-level (-V adsmt; §3.5.H suppression absent → documented double-pay) ==================="
source /home/ybi/verus-fork/tools/activate 2>/dev/null
VERUS=/home/ybi/verus-fork/source/target-verus/release/verus
run3 "  verus WITHOUT AOT env" 0 env VERUS_ADSMT_PATH=$AD/lu-smt $VERUS -V adsmt --num-threads 1 diff.rs
run3 "  verus WITH VERUS_ADSMT_AOT_LUART" 0 env VERUS_ADSMT_PATH=$AD/lu-smt VERUS_ADSMT_AOT_LUART=/tmp/lukb-fidelity/prelude.luart $VERUS -V adsmt --num-threads 1 diff.rs
run3 "  verus WITH AOT+JIT envs" 0 env VERUS_ADSMT_PATH=$AD/lu-smt VERUS_ADSMT_AOT_LUART=/tmp/lukb-fidelity/prelude.luart VERUS_ADSMT_JIT_TRACE=/tmp/lukb-fidelity/t.lutrace $VERUS -V adsmt --num-threads 1 diff.rs
echo "verus verdict sanity: $(env VERUS_ADSMT_PATH=$AD/lu-smt VERUS_ADSMT_AOT_LUART=/tmp/lukb-fidelity/prelude.luart $VERUS -V adsmt --num-threads 1 diff.rs 2>&1 | grep 'verification results')"
