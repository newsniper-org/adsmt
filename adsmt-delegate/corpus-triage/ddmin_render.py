#!/usr/bin/env python3
"""#404 ddmin: shrink a render while preserving (z3=unsat AND oxiz!=unsat).
Only (assert ...) lines are minimized; declarations + (set-logic)/(check-sat)
are kept verbatim (unused declares are harmless)."""
import os, subprocess, sys

SRC = sys.argv[1]
OUT = sys.argv[2]
Z3_T = 10
OX_T = 15
OXIZ = os.environ.get("OXIZ", "external/oxiz/target/release/oxiz")

lines = open(SRC).read().splitlines()
fixed_head = [l for l in lines if not l.startswith("(assert")]
# preserve order: rebuild = non-assert prefix ordering matters (declares before
# use; check-sat last). Simplest: keep the original line order, with a keep-set
# over assert indices.
assert_idx = [i for i, l in enumerate(lines) if l.startswith("(assert")]

def build(keep):
    ks = set(keep)
    return "\n".join(
        l for i, l in enumerate(lines) if not l.startswith("(assert") or i in ks
    ) + "\n"

def objective(keep):
    script = build(keep)
    try:
        z = subprocess.run(["z3", "-in", f"-T:{Z3_T}"], input=script,
                           capture_output=True, text=True, timeout=Z3_T + 3)
    except subprocess.TimeoutExpired:
        return False
    if "unsat" not in [t.strip() for t in z.stdout.splitlines()]:
        return False
    try:
        o = subprocess.run([OXIZ], input=script, capture_output=True,
                           text=True, timeout=OX_T)
    except subprocess.TimeoutExpired:
        return True  # oxiz can't close it in time — counts as not-unsat
    toks = [t.strip() for t in o.stdout.splitlines()]
    return "unsat" not in toks

keep = list(assert_idx)
assert objective(keep), "the full render must already satisfy the objective"

granularity = 2
while len(keep) > 1:
    chunk = max(1, len(keep) // granularity)
    reduced = False
    i = 0
    while i < len(keep):
        cand = keep[:i] + keep[i + chunk:]
        if cand and objective(cand):
            keep = cand
            print(f"  -> {len(keep)} asserts", flush=True)
            reduced = True
        else:
            i += chunk
    if not reduced:
        if chunk == 1:
            break
        granularity *= 2

open(OUT, "w").write(build(keep))
print(f"final: {len(keep)} asserts -> {OUT}")
