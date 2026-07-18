#!/usr/bin/env python3
"""Re-sweep the pinned corpus manifest against the current adsmtc; report per-class deltas.

Sweep-protocol v2 (2026-07-18, agreed with verus-fork): the harness pins
`OXIZ_MBQI_GUARD_MS=90000`, aligning the engine's internal budget with the
90 s per-row wall — pass a different guard as argv[1] (`default` = leave the
engine's built-in 4 s guard) for transition/dual sweeps. Idle-machine-only,
per `feedback_scripted_tallies`.

Env: ADSMT_CORPUS (manifest dir), ADSMTC (binary) — same as triage_unknowns.py.
"""
import collections
import csv
import os
import subprocess
import sys
import time

CORPUS = os.environ.get(
    "ADSMT_CORPUS",
    os.environ["HOME"]
    + "/verus-fork/.local-replies-to/adsmt/corpus-2026-07-04-lukb-per-obligation",
)
AD = os.environ.get("ADSMTC", os.environ["HOME"] + "/AD1/target/release/adsmtc")

GUARD = sys.argv[1] if len(sys.argv) > 1 else "90000"
env = dict(os.environ)
if GUARD != "default":
    env["OXIZ_MBQI_GUARD_MS"] = GUARD

rows = list(csv.reader(open(f"{CORPUS}/manifest.tsv"), delimiter="\t"))
hdr, data = rows[0], rows[1:]

flips, saturators = [], []
newclass = collections.Counter()
for r in data:
    if "/" not in r[0]:
        continue
    fx, ob = r[0].split("/")
    path = f"{CORPUS}/{fx}/{ob}.lukb"
    pinned_v, pinned_class = r[2], r[7]
    if pinned_class == "solver-timeout":
        newclass["solver-timeout(skipped)"] += 1
        continue
    t0 = time.monotonic()
    try:
        p = subprocess.run([AD, path], capture_output=True, text=True, timeout=90, env=env)
        code = p.returncode
    except subprocess.TimeoutExpired:
        code = -1
    ms = int((time.monotonic() - t0) * 1000)
    v = {0: "sat", 1: "unsat", 2: "unknown"}.get(code, "timeout")
    cls = "verified" if v == "unsat" else ("solver-timeout" if v == "timeout" else "unknown-or-bail")
    newclass[cls] += 1
    if v == "timeout":
        saturators.append(r[0])
    if (pinned_v == "unsat") != (v == "unsat"):
        flips.append((r[0], pinned_v, v, ms))

print(f"=== guard={GUARD} — class distribution (pinned: 104 verified / 68 s-unk / 33 bail / 4 timeout; 143-ledger @ b4518db) ===")
for k, n in sorted(newclass.items()):
    print(f"  {k}: {n}")
regr = [f for f in flips if f[1] == "unsat"]
conv = [f for f in flips if f[1] != "unsat"]
print(f"\nconversions vs PINNED (→unsat): {len(conv)}   REGRESSIONS vs PINNED (unsat lost): {len(regr)}")
for f in regr:
    print("  REGRESSION:", f)
byfx = collections.Counter(f[0].split("/")[0] for f in conv)
print("conversions by fixture:", dict(byfx))
for f in sorted(conv):
    print(f"  CONV: {f[0]}  ({f[1]} → {f[2]}, {f[3]} ms)")
print("\n=== saturators (full-budget burn, named) ===")
for s in saturators:
    print(f"  SATURATOR: {s}")
print("\n=== negative controls ===")
for nc in sorted(os.listdir(f"{CORPUS}/negative-controls")):
    if not nc.endswith(".lukb"):
        continue
    p = subprocess.run(
        [AD, f"{CORPUS}/negative-controls/{nc}"], capture_output=True, text=True, timeout=90, env=env
    )
    v = {0: "sat", 1: "unsat", 2: "unknown"}.get(p.returncode, "?")
    print(f"  {nc}: {v}")
