#!/usr/bin/env python3
"""Int case-split differential (#433, the non-convex arith⇄EUF completion).

The feature asserts `bounds ⇒ (t = lo ∨ … ∨ t = hi)` before accepting a model,
so the risky direction is a NEW `unsat` — a clause that over-constrains (wrong
polarity on a condition literal, a bound read off the wrong trail scope, an
integer endpoint mis-rounded from a rational atom) refutes a satisfiable
script. Every generated script therefore mixes the trigger shape (narrow
asserted spans on EUF-shared Int terms, partially-agreeing images) with
push/pop scopes, negated bound atoms, rational bound constants, and spans
straddling the 12 cap.

Three arms, two on the SAME binary so sibling drift cannot be blamed:
  A  oxiz, split ON  (the feature)
  B  oxiz, split OFF (`OXIZ_NO_INT_CASE_SPLIT=1`, the historical gap)
  Z  z3               (ground truth)

A-vs-Z `sat`-vs-`unsat` in either direction is a soundness signal; `unknown`
from oxiz is never a mismatch. A-vs-B may legitimately differ ONLY as
B=`sat`/A=`unsat` where Z=`unsat` (the gap being closed); any other A-vs-B
divergence is the feature changing an answer it must not touch.
"""
import os
import random
import subprocess
import sys

OXIZ = os.environ.get("OXIZ", "/home/ybi/AD1/external/oxiz/target/release/oxiz")
SEEDS = int(sys.argv[1]) if len(sys.argv) > 1 else 800
SEED0 = int(sys.argv[2]) if len(sys.argv) > 2 else 433


def gen(rng):
    L = ["(set-logic QF_UFLIA)"]
    nx = rng.randint(1, 3)
    xs = [f"x{i}" for i in range(nx)]
    for x in xs:
        L.append(f"(declare-fun {x} () Int)")
    L.append("(declare-fun a () Int)")
    L.append("(declare-fun b () Int)")
    funs = [f"f{i}" for i in range(rng.randint(1, 2))]
    for f in funs:
        L.append(f"(declare-fun {f} (Int) Int)")

    def bound_atoms(x):
        lo = rng.randint(-3, 3)
        span = rng.choice([1, 1, 2, 2, 3, 5, 11, 12, 13, 20])
        hi = lo + span
        lo_style = rng.randrange(3)
        if lo_style == 0:
            L.append(f"(assert (<= {lo} {x}))")
        elif lo_style == 1:
            L.append(f"(assert (not (<= {x} {lo - 1})))")  # x > lo-1  ⇒  x >= lo
        else:
            # rational endpoint: x >= lo - 1/2  ⇒  x >= lo (integer x)
            L.append(f"(assert (>= (* 2 {x}) {2 * lo - 1}))")
        hi_style = rng.randrange(3)
        if hi_style == 0:
            L.append(f"(assert (<= {x} {hi}))")
        elif hi_style == 1:
            L.append(f"(assert (not (<= {hi + 1} {x})))")  # x < hi+1  ⇒  x <= hi
        else:
            L.append(f"(assert (<= (* 2 {x}) {2 * hi + 1}))")  # x <= hi + 1/2
        return lo, hi

    def image_facts(x, lo, hi, f):
        # Pin the images of SOME points to `a` (sometimes all, sometimes not),
        # and sometimes pin one to `b` with a != b left open or asserted.
        agree_all = rng.random() < 0.5
        for v in range(lo, hi + 1):
            if agree_all or rng.random() < 0.7:
                L.append(f"(assert (= ({f} {v}) a))")
            elif rng.random() < 0.5:
                L.append(f"(assert (= ({f} {v}) b))")
        if rng.random() < 0.6:
            L.append(f"(assert (not (= ({f} {x}) a)))")
        else:
            L.append(f"(assert (= ({f} {x}) b))")
            if rng.random() < 0.5:
                L.append("(assert (not (= a b)))")

    use_push = rng.random() < 0.4
    checks = 1
    if use_push:
        # Scope-local bounds: the split clause must not leak across the pop.
        x = rng.choice(xs)
        f = rng.choice(funs)
        L.append("(push 1)")
        lo, hi = bound_atoms(x)
        image_facts(x, lo, hi, f)
        L.append("(check-sat)")
        L.append("(pop 1)")
        outside = rng.randint(-40, 40)
        L.append(f"(assert (= {x} {outside}))")
        if rng.random() < 0.5:
            L.append(f"(assert (= ({f} {outside}) b))")
        L.append("(check-sat)")
        checks = 2
    else:
        for x in xs:
            if rng.random() < 0.8:
                lo, hi = bound_atoms(x)
                if rng.random() < 0.9:
                    image_facts(x, lo, hi, rng.choice(funs))
        # cross-variable link occasionally (entailed-not-asserted spans stay
        # out of scope; this only checks they do no harm)
        if nx >= 2 and rng.random() < 0.4:
            L.append(f"(assert (= {xs[0]} (+ {xs[1]} 1)))")
        L.append("(check-sat)")
    return "\n".join(L) + "\n", checks


def run(cmd, env, path):
    try:
        p = subprocess.run(
            cmd + [path], capture_output=True, text=True, timeout=30, env=env
        )
        return [
            l.strip()
            for l in p.stdout.splitlines()
            if l.strip() in ("sat", "unsat", "unknown")
        ]
    except subprocess.TimeoutExpired:
        return ["timeout"]


def main():
    base = os.environ.copy()
    base["OXIZ_MBQI_GUARD_MS"] = "8000"
    off = dict(base, OXIZ_NO_INT_CASE_SPLIT="1")
    tmp = "/tmp/claude-1000/icsdiff.smt2"
    os.makedirs(os.path.dirname(tmp), exist_ok=True)
    n_soundness = n_ab = n_closed = 0
    for i in range(SEEDS):
        rng = random.Random(SEED0 + i)
        script, checks = gen(rng)
        with open(tmp, "w") as fh:
            fh.write(script)
        va = run([OXIZ], base, tmp)
        vb = run([OXIZ], off, tmp)
        vz = run(["z3"], base, tmp)
        if len(va) != checks or len(vz) != checks:
            continue
        for k in range(checks):
            a, b_, z = va[k], vb[k] if k < len(vb) else "?", vz[k]
            if {a, z} == {"sat", "unsat"}:
                n_soundness += 1
                print(f"SOUNDNESS seed={SEED0 + i} check#{k}: A={a} Z={z}")
                print(script)
            elif a != b_ and not (b_ == "sat" and a == "unsat" and z == "unsat"):
                n_ab += 1
                print(f"A/B seed={SEED0 + i} check#{k}: A={a} B={b_} Z={z}")
                print(script)
            elif b_ == "sat" and a == "unsat" and z == "unsat":
                n_closed += 1
        if (i + 1) % 100 == 0:
            print(
                f"[{i + 1}/{SEEDS}] soundness={n_soundness} ab={n_ab} "
                f"gap-closed={n_closed}",
                flush=True,
            )
    print(
        f"DONE seeds={SEEDS} soundness={n_soundness} ab-divergence={n_ab} "
        f"gap-closed-instances={n_closed}"
    )
    sys.exit(1 if (n_soundness or n_ab) else 0)


if __name__ == "__main__":
    main()
