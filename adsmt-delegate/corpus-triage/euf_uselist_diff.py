#!/usr/bin/env python3
"""EUF use-list trail differential (#39).

The fix only ARMS inside a push scope (`use_trail_limits` non-empty), so a
differential that never pushes cannot exercise it. Every generated script is
therefore incremental: nested `(push)`/`(pop)` with `(check-sat)` at several
depths, over a congruence-heavy signature (uninterpreted sort + unary/binary
uninterpreted functions + Int-valued functions so the arithmetic and EUF
solvers exchange interface equalities).

Three arms, two of them on the SAME binary so sibling drift cannot be blamed:
  A  oxiz, trail ON  (the fix)
  B  oxiz, trail OFF (`OXIZ_EUF_NO_USELIST_TRAIL=1`, the leaking pre-fix path)
  Z  z3               (ground truth)

A-vs-B divergence means the fix CHANGED an answer — it must be zero.
A-vs-Z divergence in the `unsat`/`sat` directions is a soundness signal.
`unknown` from oxiz is never a mismatch.
"""
import os
import random
import subprocess
import sys

OXIZ = os.environ.get("OXIZ", "/home/ybi/.claude/jobs/5ec69da0/tmp/w39/oxiz-uselist")
SEEDS = int(sys.argv[1]) if len(sys.argv) > 1 else 600
SEED0 = int(sys.argv[2]) if len(sys.argv) > 2 else 39


def gen(rng):
    L = ["(set-logic ALL)", "(declare-sort U 0)"]
    nc = rng.randint(3, 6)
    consts = [f"c{i}" for i in range(nc)]
    for c in consts:
        L.append(f"(declare-fun {c} () U)")
    funs = [f"f{i}" for i in range(rng.randint(2, 4))]
    for f in funs:
        L.append(f"(declare-fun {f} (U) U)")
    bfuns = [f"g{i}" for i in range(rng.randint(1, 3))]
    for g in bfuns:
        L.append(f"(declare-fun {g} (U U) U)")
    ifuns = [f"h{i}" for i in range(rng.randint(1, 3))]
    for h in ifuns:
        L.append(f"(declare-fun {h} (U) Int)")
    L.append("(declare-fun n () Int)")

    def term(d=0):
        if d >= 2 or rng.random() < 0.35:
            return rng.choice(consts)
        r = rng.random()
        if r < 0.5:
            return f"({rng.choice(funs)} {term(d + 1)})"
        return f"({rng.choice(bfuns)} {term(d + 1)} {term(d + 1)})"

    def iterm():
        r = rng.random()
        if r < 0.4:
            return f"({rng.choice(ifuns)} {term()})"
        if r < 0.6:
            return "n"
        if r < 0.8:
            return str(rng.randint(-4, 4))
        return f"(+ ({rng.choice(ifuns)} {term()}) {rng.randint(-3, 3)})"

    def atom():
        r = rng.random()
        if r < 0.45:
            return f"(= {term()} {term()})"
        if r < 0.65:
            return f"(not (= {term()} {term()}))"
        if r < 0.85:
            return f"(= {iterm()} {iterm()})"
        return f"({rng.choice(['<', '<=', '>', '>='])} {iterm()} {iterm()})"

    def formula():
        r = rng.random()
        if r < 0.55:
            return atom()
        if r < 0.7:
            return f"(or {atom()} {atom()})"
        if r < 0.85:
            return f"(=> {atom()} {atom()})"
        return f"(and {atom()} {atom()})"

    # Base assertions, then nested push/pop scopes with check-sats at depth.
    for _ in range(rng.randint(2, 5)):
        L.append(f"(assert {formula()})")
    L.append("(check-sat)")
    depth = 0
    for _ in range(rng.randint(3, 8)):
        r = rng.random()
        if r < 0.45 or depth == 0:
            L.append("(push 1)")
            depth += 1
            for _ in range(rng.randint(1, 4)):
                L.append(f"(assert {formula()})")
            L.append("(check-sat)")
        else:
            L.append("(pop 1)")
            depth -= 1
            L.append(f"(assert {formula()})")
            L.append("(check-sat)")
    while depth > 0:
        L.append("(pop 1)")
        depth -= 1
    L.append("(check-sat)")
    L.append("(exit)")
    return "\n".join(L) + "\n"


def verdicts(out):
    return [w for w in out.split() if w in ("sat", "unsat", "unknown")]


def run(cmd, path, env=None, t=25):
    e = dict(os.environ)
    e["OXIZ_MBQI_GUARD_MS"] = "4000"
    if env:
        e.update(env)
    try:
        p = subprocess.run(cmd + [path], capture_output=True, text=True, timeout=t, env=e)
        return verdicts(p.stdout)
    except subprocess.TimeoutExpired:
        return None


def main():
    tmp = "/tmp/claude-1000/-home-ybi-AD1/5ec69da0-44f6-4502-8273-a98a682a7a55/scratchpad/euf_diff.smt2"
    ab_mismatch = az_unsat = az_sat = 0
    checked = ab_checked = 0
    for s in range(SEED0, SEED0 + SEEDS):
        rng = random.Random(s)
        open(tmp, "w").write(gen(rng))
        a = run([OXIZ], tmp)
        b = run([OXIZ], tmp, {"OXIZ_EUF_NO_USELIST_TRAIL": "1"})
        if a is None:
            continue
        if b is not None:
            ab_checked += 1
            if a != b:
                ab_mismatch += 1
                print(f"AB-MISMATCH seed={s}\n  trailON ={a}\n  trailOFF={b}")
        z = run(["z3"], tmp)
        if z is None or len(z) != len(a):
            continue
        checked += 1
        for va, vz in zip(a, z):
            if va == "unsat" and vz == "sat":
                az_unsat += 1
                print(f"FALSE-UNSAT seed={s}: oxiz={a} z3={z}")
            elif va == "sat" and vz == "unsat":
                az_sat += 1
                print(f"FALSE-SAT   seed={s}: oxiz={a} z3={z}")
    print(f"\nseeds={SEEDS} from {SEED0}")
    print(f"A-vs-B compared={ab_checked}  mismatches={ab_mismatch}")
    print(f"A-vs-z3 compared={checked}  false-unsat={az_unsat}  false-sat={az_sat}")


main()
