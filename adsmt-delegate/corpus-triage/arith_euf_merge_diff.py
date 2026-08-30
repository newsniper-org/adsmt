#!/usr/bin/env python3
"""Arith->EUF entailed-merge differential (#434).

Targets the mechanism `model_based_combination` uses to close the loop between
the two theories: when arith ENTAILS a term's value, merge that term with the
canonical EUF node for the constant, fire congruence, and report any resulting
disequality conflict.

Two things about that path make a randomized differential mandatory rather than
nice-to-have:

  * it MINTS MERGES, so a wrong version answers `unsat` on a satisfiable script
    — a false proof, the fatal direction here;
  * the conflict clause it builds is assembled from a Farkas reason set, and a
    reason set that omits the literal the entailment actually rested on yields
    a clause that is FALSE GLOBALLY. That is not hypothetical: it is exactly
    the bug this harness was written to catch, where a probe run against an
    already-infeasible arith state reported every term as "fixed" with a
    one-element bogus reason set.

Generated shapes deliberately mix ENTAILED values (a unit equality, or a narrow
span the #433 case split can force) with MERELY MODEL-EQUAL ones (a span with
two live choices), because the whole correctness question is telling those two
apart.

Three arms, two on the SAME binary:
  A  oxiz as configured
  B  oxiz with `OXIZ_NO_INT_CASE_SPLIT=1` (no forcing => far fewer entailments)
  Z  z3 (ground truth)

A-vs-Z in either direction is a soundness signal; `unknown` from oxiz never is.
B is reported for attribution only — B being weaker than A is expected.
"""
import os
import random
import subprocess
import sys

OXIZ = os.environ.get("OXIZ", "/home/ybi/AD1/external/oxiz/target/release/oxiz")
SEEDS = int(sys.argv[1]) if len(sys.argv) > 1 else 600
SEED0 = int(sys.argv[2]) if len(sys.argv) > 2 else 434


def gen(rng):
    L = ["(set-logic QF_UFLIA)"]
    xs = [f"x{i}" for i in range(rng.randint(2, 3))]
    for x in xs:
        L.append(f"(declare-fun {x} () Int)")
    vals = [f"v{i}" for i in range(rng.randint(2, 3))]
    for v in vals:
        L.append(f"(declare-fun {v} () Int)")
    funs = [f"h{i}" for i in range(rng.randint(1, 2))]
    for f in funs:
        L.append(f"(declare-fun {f} (Int) Int)")

    anchor = xs[0]
    lo = rng.randint(-2, 4)
    style = rng.randrange(3)
    if style == 0:
        # ENTAILED outright: a unit equality.
        pin = rng.randint(lo, lo + 3)
        L.append(f"(assert (= {anchor} {pin}))")
        span_lo, span_hi = pin, pin
    elif style == 1:
        # Forceable: a narrow asserted span the case split can enumerate.
        span = rng.choice([1, 2, 3])
        L.append(f"(assert (<= {lo} {anchor}))")
        L.append(f"(assert (<= {anchor} {lo + span}))")
        span_lo, span_hi = lo, lo + span
    else:
        # NOT forceable: a span wider than the cap, so nothing is entailed.
        L.append(f"(assert (<= {lo} {anchor}))")
        L.append(f"(assert (<= {anchor} {lo + 20}))")
        span_lo, span_hi = lo, lo + 20

    # Cross-links: the other variables are tied to the anchor by shifts, so
    # their values are entailed exactly when the anchor's is.
    linked = []
    for x in xs[1:]:
        d = rng.randint(-3, 3)
        if rng.random() < 0.5:
            L.append(f"(assert (= {x} (+ {anchor} {d})))")
        else:
            L.append(f"(assert (= {anchor} (+ {x} {-d})))")
        linked.append((x, d))

    # Function facts over a window of literals around the reachable range, plus
    # the linked variables themselves. Partial agreement is the point.
    for f in funs:
        window = range(span_lo - 3, span_hi + 4)
        for k in window:
            if rng.random() < 0.45:
                L.append(f"(assert (= ({f} {k}) {rng.choice(vals)}))")
        for x, _ in linked or [(anchor, 0)]:
            if rng.random() < 0.8:
                L.append(f"(assert (= ({f} {x}) {rng.choice(vals)}))")
        if rng.random() < 0.6:
            L.append(f"(assert (= ({f} {anchor}) {rng.choice(vals)}))")

    # Disequalities between the value constants — without them almost nothing
    # is unsat and the harness would only ever exercise the `sat` direction.
    for i in range(len(vals)):
        for j in range(i + 1, len(vals)):
            if rng.random() < 0.7:
                L.append(f"(assert (not (= {vals[i]} {vals[j]})))")
    if rng.random() < 0.4:
        L.append(f"(assert (= {rng.choice(vals)} {rng.randint(-2, 6)}))")

    L.append("(check-sat)")
    return "\n".join(L) + "\n"


def run(env, path):
    try:
        p = subprocess.run(
            [env.pop("__BIN__")] + [path], capture_output=True, text=True,
            timeout=30, env=env,
        )
        for l in p.stdout.splitlines():
            if l.strip() in ("sat", "unsat", "unknown"):
                return l.strip()
        return "none"
    except subprocess.TimeoutExpired:
        return "timeout"


def main():
    base = dict(os.environ, OXIZ_MBQI_GUARD_MS="8000")
    tmp = "/tmp/claude-1000/aemdiff.smt2"
    os.makedirs(os.path.dirname(tmp), exist_ok=True)
    bad_unsat = bad_sat = 0
    for i in range(SEEDS):
        rng = random.Random(SEED0 + i)
        script = gen(rng)
        with open(tmp, "w") as fh:
            fh.write(script)
        a = run(dict(base, __BIN__=OXIZ), tmp)
        z = run(dict(base, __BIN__="z3"), tmp)
        if a == "unsat" and z == "sat":
            bad_unsat += 1
            print(f"FABRICATED-UNSAT seed={SEED0 + i}\n{script}", flush=True)
        elif a == "sat" and z == "unsat":
            bad_sat += 1
            b = run(dict(base, __BIN__=OXIZ, OXIZ_NO_INT_CASE_SPLIT="1"), tmp)
            print(f"missed-unsat seed={SEED0 + i} (split-off arm: {b})", flush=True)
        if (i + 1) % 100 == 0:
            print(
                f"[{i + 1}/{SEEDS}] fabricated-unsat={bad_unsat} missed-unsat={bad_sat}",
                flush=True,
            )
    print(f"DONE seeds={SEEDS} fabricated-unsat={bad_unsat} missed-unsat={bad_sat}")
    sys.exit(1 if bad_unsat else 0)


if __name__ == "__main__":
    main()
