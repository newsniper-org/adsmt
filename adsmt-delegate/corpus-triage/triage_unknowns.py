#!/usr/bin/env python3
"""#404 triage: for every solver-unknown/timeout corpus row, capture the
delegation render (ADSMT_DELEGATE_DEBUG=1) and run z3 on it. Classify:
  z3=unsat  -> a REAL completeness target (z3 closes it, we abstain)
  z3=sat    -> designed-non-verifying (abduct family) or genuine sat
  z3=unknown/timeout -> hard for everyone (deprioritize)
Output: per-row TSV + a family summary.
"""
import csv, os, re, subprocess, sys, time
from collections import Counter

CORPUS = os.environ.get(
    "ADSMT_CORPUS",
    ".local-replies-from/verus-fork/corpus-2026-07-04-lukb-per-obligation",
)
ADSMTC = os.environ.get("ADSMTC", "target/release/adsmtc")
ADSMTC_TIMEOUT = 35.0
Z3_TIMEOUT = 20.0

rows = []
with open(os.path.join(CORPUS, "manifest.tsv")) as f:
    for r in csv.DictReader(f, delimiter="\t"):
        rows.append(r)

# current unknowns = pinned solver-unknown/timeout + the 14 new post-#403
# unknowns (pinned stage-bail rows that now reach the solver and abstain).
targets = [r["obligation"] for r in rows if r["class"] in ("solver-unknown", "solver-timeout", "stage-bail")]

def z3_verdict(script):
    try:
        p = subprocess.run(["z3", "-in", f"-T:{int(Z3_TIMEOUT)}"], input=script,
                           capture_output=True, text=True, timeout=Z3_TIMEOUT + 5)
    except subprocess.TimeoutExpired:
        return "z3-timeout"
    for line in p.stdout.splitlines():
        t = line.strip()
        if t in ("sat", "unsat", "unknown"):
            return t
    return "z3-noverdict"

print("obligation\tadsmtc\tz3\twall_ms\trender_bytes", flush=True)
fam = Counter()
for ob in targets:
    path = os.path.join(CORPUS, ob + ".lukb")
    env = dict(os.environ, ADSMT_DELEGATE_DEBUG="1")
    t0 = time.monotonic()
    try:
        p = subprocess.run([ADSMTC, path], capture_output=True, text=True,
                           timeout=ADSMTC_TIMEOUT, env=env)
        verdict = (p.stdout.strip().splitlines() or [""])[-1]
    except subprocess.TimeoutExpired as e:
        p = e
        verdict = "timeout"
    ms = (time.monotonic() - t0) * 1000
    if verdict in ("unsat", "sat"):
        # decided now (converted rows) — not a target
        print(f"{ob}\t{verdict}\t-\t{ms:.0f}\t-", flush=True)
        continue
    # extract the render from stderr (the delegate-debug dump)
    err = p.stderr if isinstance(p.stderr, str) else (p.stderr or b"").decode("utf-8", "replace")
    # the debug dump prints the full script; grab everything that looks like
    # consecutive s-expression lines between the dump markers, else all
    # paren-leading lines.
    m = re.search(r"\[dbg\] script:\n(.*)", err, re.S)
    script = m.group(1) if m else "\n".join(
        l for l in err.splitlines() if l.startswith("(")
    )
    # cut at the next non-sexpr debug marker, if any
    script = "\n".join(
        l for l in script.splitlines() if not l.startswith("[")
    )
    if "(check-sat)" not in script:
        script += "\n(check-sat)\n"
    z3v = z3_verdict(script) if script.strip() else "no-render"
    family = ob.split("/")[0]
    fam[(family, verdict, z3v)] += 1
    print(f"{ob}\t{verdict}\t{z3v}\t{ms:.0f}\t{len(script)}", flush=True)

print("\n== family x (adsmtc, z3) ==")
for (family, v, z), n in sorted(fam.items()):
    print(f"{family}\t{v}\t{z}\t{n}")
