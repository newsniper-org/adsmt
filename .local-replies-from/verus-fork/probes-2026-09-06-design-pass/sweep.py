#!/usr/bin/env python3
"""Native-only (no delegation, no SMT-LIB) sweep of the per-obligation corpus,
with failure-stage attribution from ADSMT_LUKB_DEBUG."""
import os, glob, subprocess, time, csv, sys, tempfile

ROOT = "/home/ybi/verus-fork/.local-replies-to/adsmt/corpus-2026-07-04-lukb-per-obligation"
ADSMTC = os.path.expanduser("~/AD1/target/release/adsmtc")
OUT = sys.argv[1]
CERTROOT = sys.argv[2]
TIMEOUT = 90

env = dict(os.environ)
env["ADSMT_NO_DELEGATION"] = "1"
env["ADSMT_LUKB_DEBUG"] = "1"
env.pop("ADSMT_DELEGATE", None)

rows = []
files = [f for f in sorted(glob.glob(os.path.join(ROOT, "*", "*.lukb")))]
for f in files:
    rel = os.path.relpath(f, ROOT)[:-5]
    cd = os.path.join(CERTROOT, rel.replace("/", "__"))
    os.makedirs(cd, exist_ok=True)
    t0 = time.time()
    try:
        p = subprocess.run([ADSMTC, "--emit-cert-dir", cd, f], env=env,
                           capture_output=True, text=True, timeout=TIMEOUT)
        out, err, rc = p.stdout.strip(), p.stderr.strip(), p.returncode
    except subprocess.TimeoutExpired:
        out, err, rc = "TIMEOUT", "", -1
    ms = int((time.time() - t0) * 1000)
    verdict = out.splitlines()[-1].strip() if out else "(no output)"
    if "wrote" in verdict:
        verdict = "(no verdict)"
    stage = "solve"
    if "elaborate failed" in err: stage = "elaborate"
    elif "lower failed" in err:   stage = "lower"
    elif out == "TIMEOUT":        stage = "timeout"
    ncert = len(glob.glob(os.path.join(cd, "*.cert.*")))
    ngoal = sum(1 for l in open(f, encoding="utf-8") if l.strip().startswith("goal:"))
    rows.append(dict(obligation=rel, verdict=verdict, stage=stage, certs=ncert,
                     goals=ngoal, wall_ms=ms,
                     diag=err.replace("\n", " | ")[:200]))

with open(OUT, "w", newline="", encoding="utf-8") as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()), delimiter="\t")
    w.writeheader(); w.writerows(rows)
print("wrote", OUT, len(rows), "rows")
