#!/usr/bin/env python3
"""Per-obligation .lukb corpus builder.

For each Verus fixture:
  1. plain `verus` run  -> z3 oracle (N verified, M errors)
  2. `verus -V adsmt -V emit-lukb --log-all` -> .verus-log/root.lukb
  3. split root.lukb on '# ── obligation ──' markers -> prelude + per-obligation files
  4. run adsmtc on each -> verdict + wall
  5. manifest.tsv rows
"""
import os, re, shutil, subprocess, sys, time
from pathlib import Path

VERUS = "/home/ybi/verus-fork/source/target-verus/release/verus"
LUSMT = "/home/ybi/AD1/target/release/lu-smt"
ADSMTC = "/home/ybi/AD1/target/release/adsmtc"
OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("/tmp/lukb-corpus/out")
WORK = Path("/tmp/lukb-corpus/work")
MARKER = "# ── obligation ──"

env = dict(os.environ, VERUS_ADSMT_PATH=LUSMT)

def sh(cmd, cwd=None, timeout=120):
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout + p.stderr, int((time.monotonic() - t0) * 1000)
    except subprocess.TimeoutExpired:
        return -1, "TIMEOUT", int((time.monotonic() - t0) * 1000)

def verdict_line(out):
    m = re.search(r"verification results:: (\d+) verified, (\d+) errors", out)
    return (int(m.group(1)), int(m.group(2))) if m else (None, None)

def main(fixtures):
    OUT.mkdir(parents=True, exist_ok=True)
    rows = []
    for fx in fixtures:
        fx = Path(fx).resolve()
        stem = fx.stem
        wd = WORK / stem
        shutil.rmtree(wd, ignore_errors=True); wd.mkdir(parents=True)
        shutil.copy(fx, wd / fx.name)

        _, z3out, _ = sh([VERUS, fx.name], cwd=wd)
        z3v, z3e = verdict_line(z3out)
        _, adout, _ = sh([VERUS, "-V", "adsmt", "-V", "emit-lukb", "--log-all", fx.name], cwd=wd)
        adv, ade = verdict_line(adout)

        log = wd / ".verus-log" / "root.lukb"
        if not log.is_file():
            rows.append([stem, "-", "NO-LUKB-EMITTED", "-", "-", f"z3={z3v}v/{z3e}e", f"lusmt={adv}v/{ade}e"])
            continue
        text = log.read_text()
        idx = text.find(MARKER)
        prelude, tail = text[:idx], text[idx:]
        blocks = [MARKER + b for b in tail.split(MARKER) if b.strip()]

        # Within a block, items BEFORE (and incl.) the goal line are the query's
        # scoped items; items AFTER the goal are GLOBAL decls emitted post-pop
        # (ens%/req% fns, fuel_nat% consts, their axioms) that belong to the
        # CONTEXT of every LATER obligation. Obligation K's self-contained file =
        # prelude + tails(1..K-1) + head(K).
        heads, tails = [], []
        for block in blocks:
            lines = block.splitlines(keepends=True)
            gi = next((j for j, ln in enumerate(lines) if ln.startswith("goal")), len(lines) - 1)
            heads.append("".join(lines[: gi + 1]) + "\n")
            tails.append("".join(lines[gi + 1 :]))
        fxdir = OUT / stem
        fxdir.mkdir(parents=True, exist_ok=True)
        for i, block in enumerate(blocks, 1):
            ob = fxdir / f"ob{i:02d}.lukb"
            ob.write_text(prelude + "".join(tails[: i - 1]) + heads[i - 1])
            goal = next((ln.strip() for ln in block.splitlines() if ln.startswith("goal")), "?")
            code, aout, ms = sh([ADSMTC, str(ob)], timeout=90)
            v = {0: "sat", 1: "unsat", 2: "unknown"}.get(code, "timeout" if code == -1 else f"exit{code}")
            rows.append([f"{stem}/ob{i:02d}", str(len(blocks)), v, str(ms), goal[:90],
                         f"z3={z3v}v/{z3e}e", f"lusmt={adv}v/{ade}e"])
            print(f"  {stem}/ob{i:02d}: {v} ({ms} ms)")
    man = OUT / "manifest.tsv"
    with man.open("w") as f:
        f.write("obligation\tblocks\tadsmtc\twall_ms\tgoal\tz3_fixture\tlusmt_fixture\n")
        for r in rows:
            f.write("\t".join(r) + "\n")
    n = len([r for r in rows if "/" in r[0]])
    u = len([r for r in rows if r[2] == "unsat"])
    print(f"\ncorpus: {n} obligations, {u} unsat/verified, manifest -> {man}")

if __name__ == "__main__":
    fixtures = sys.stdin.read().split()
    main(fixtures)
