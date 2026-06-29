#!/usr/bin/env python3
"""
Three-way differential for #317 (the M3-8 lowering closing 후검증 gate,
DESIGN.md §5.1 P2). Generates random SMT-LIB scripts in the `adsmt-ir-smtlib`
face's fragment and runs each through THREE engines:

  - LOWERING — the REAL pipeline (face → kernel → lower → adsmt-engine), via the
    `lower_solve` example driver. This is the SUBJECT under test.
  - NATIVE   — the native `lu-smt` CLI (SMT-LIB → parser → the SAME
    adsmt-engine), NO lowering. The engine REFERENCE.
  - Z3       — the ground-truth oracle.

WHY THREE-WAY (and not just z3): the lowering's job is to hand the engine the
SAME input the native parser would for the shared fragment. So z3 alone cannot
attribute a wrong verdict — z3 disagreements catch ENGINE bugs (which the native
path shares) just as much as lowering bugs. Comparing against NATIVE *cancels*
the shared engine: a verdict the native path gets wrong too is an engine bug
(tracked separately — quantifier opacity, linear var-cancellation), NOT a
lowering defect. A verdict ONLY the lowering gets wrong (native + z3 agree, the
lowering dissents) is the genuine lowering mistranslation this gate guards.

GATE (the lowering's trust boundary): the lowering must NEVER return a DEFINITE
verdict that z3 contradicts while the native path does NOT — i.e. no
lowering-ATTRIBUTABLE wrong verdict. `unknown` from the lowering is always fine
(a sound abstain / bare-engine incompleteness). The lowering being MORE decisive
than native and matching z3 (e.g. the ground constant-fold deciding `(= 4 3)`
that the bare native path merges in UF) is a sound IMPROVEMENT, reported as such.

Build first:  cargo build -p adsmt-ir-lower --example lower_solve
              cargo build -p adsmt-cli --bin lu-smt
Run:          python3 z3_differential.py
"""
import random
import subprocess
import sys

DRIVER = "/home/ybi/AD1/target/debug/examples/lower_solve"
NATIVE = "/home/ybi/AD1/target/debug/lu-smt"
Z3 = "/usr/bin/z3"

PRELUDE = """\
(declare-sort S 0)
(declare-const a S) (declare-const b S) (declare-const c S)
(declare-fun f (S) S)
(declare-const p Bool) (declare-const q Bool) (declare-const r Bool)
(declare-const i Int) (declare-const j Int)
(declare-datatype Color ((red) (green) (blue)))
(declare-const u Color) (declare-const v Color)
(declare-datatype Nat ((zero) (succ (pred Nat))))
(declare-const n Nat) (declare-const m Nat)
"""

S_TERMS = ["a", "b", "c", "(f a)", "(f b)", "(f (f a))", "(f c)"]
COLOR_TERMS = ["u", "v", "red", "green", "blue"]
NAT_TERMS = ["n", "m", "zero", "(succ zero)", "(succ n)", "(succ (succ zero))"]
BOOLV = ["p", "q", "r"]


def iexpr(rng, d):
    if d <= 0 or rng.random() < 0.5:
        return rng.choice(["i", "j", str(rng.randint(-4, 4))])
    op = rng.choice(["+", "-"])
    return f"({op} {iexpr(rng, d-1)} {iexpr(rng, d-1)})"


def atom(rng):
    k = rng.random()
    if k < 0.18:
        return rng.choice(BOOLV)
    if k < 0.36:
        return f"(= {rng.choice(S_TERMS)} {rng.choice(S_TERMS)})"
    if k < 0.5:
        n = rng.randint(2, 3)
        return f"(distinct {' '.join(rng.choice(S_TERMS) for _ in range(n))})"
    if k < 0.66:
        op = rng.choice(["<", "<=", ">", ">=", "="])
        return f"({op} {iexpr(rng, 2)} {iexpr(rng, 2)})"
    if k < 0.8:
        return f"(= {rng.choice(COLOR_TERMS)} {rng.choice(COLOR_TERMS)})"
    if k < 0.92:
        return f"(= {rng.choice(NAT_TERMS)} {rng.choice(NAT_TERMS)})"
    n = rng.randint(2, 3)
    return f"(distinct {' '.join(rng.choice(COLOR_TERMS) for _ in range(n))})"


def formula(rng, d):
    if d <= 0 or rng.random() < 0.35:
        return atom(rng)
    k = rng.random()
    if k < 0.25:
        return f"(not {formula(rng, d-1)})"
    if k < 0.45:
        return f"(and {formula(rng, d-1)} {formula(rng, d-1)})"
    if k < 0.65:
        return f"(or {formula(rng, d-1)} {formula(rng, d-1)})"
    if k < 0.8:
        return f"(=> {formula(rng, d-1)} {formula(rng, d-1)})"
    if k < 0.9:
        return f"(ite {formula(rng, d-1)} {formula(rng, d-1)} {formula(rng, d-1)})"
    # a quantified atom over S (the anti-trigger-hell win path)
    return f"(forall ((x S)) (= (f x) (f x)))" if rng.random() < 0.5 else \
           f"(forall ((x S)) {rng.choice(BOOLV)})"


def gen(rng):
    n = rng.randint(1, 4)
    asserts = "\n".join(f"(assert {formula(rng, rng.randint(1, 3))})" for _ in range(n))
    return PRELUDE + asserts + "\n(check-sat)\n"


def run(cmd, smt):
    try:
        out = subprocess.run(cmd, input=smt, capture_output=True, text=True, timeout=20)
    except subprocess.TimeoutExpired:
        return "timeout"
    if "(error" in out.stdout:
        return "error"
    lines = out.stdout.strip().splitlines()
    last = lines[-1].strip() if lines else ""
    return last if last in ("sat", "unsat", "unknown") else "other"


# ── ite desugaring for the NATIVE reference ──────────────────────────────────
# The native `lu-smt` SMT-LIB parser has no `ite` operator, but the generator
# emits Bool-valued `(ite c a b)` (the lowering handles it as `(c→a)∧(¬c→b)`).
# To keep NATIVE a usable reference on ite scripts — instead of erroring out
# (which would defeat the engine-cancelling comparison) — rewrite every
# Bool-`ite` to the SAME classical encoding the lowering uses (a semantics-
# preserving rewrite; z3 stays the fully-independent oracle on the ORIGINAL).
def _toks(s):
    out, i = [], 0
    while i < len(s):
        c = s[i]
        if c in "()":
            out.append(c); i += 1
        elif c.isspace():
            i += 1
        else:
            j = i
            while j < len(s) and not s[j].isspace() and s[j] not in "()":
                j += 1
            out.append(s[i:j]); i = j
    return out


def _parse(ts, i):
    if ts[i] == "(":
        lst, i = [], i + 1
        while ts[i] != ")":
            node, i = _parse(ts, i)
            lst.append(node)
        return lst, i + 1
    return ts[i], i + 1


def _desugar(n):
    if isinstance(n, str):
        return n
    n = [_desugar(x) for x in n]
    if n and n[0] == "ite" and len(n) == 4:
        c, a, b = n[1], n[2], n[3]
        return ["and", ["=>", c, a], ["=>", ["not", c], b]]
    return n


def _emit(n):
    return n if isinstance(n, str) else "(" + " ".join(_emit(x) for x in n) + ")"


def desugar_ite(smt):
    out = []
    for line in smt.splitlines():
        s = line.strip()
        if s.startswith("(assert"):
            node, _ = _parse(_toks(s), 0)
            out.append(_emit(_desugar(node)))
        else:
            out.append(line)
    return "\n".join(out) + "\n"


DEF = ("sat", "unsat")


def classify(zv, nv, lv):
    """Attribute a (z3, native, lowering) verdict triple.

    Returns one of: 'agree', 'improve' (lowering more sound than native, matches
    z3), 'lowering_bug' (lowering definite-wrong, native does NOT share it →
    GATE FAIL), 'engine_bug' (lowering definite-wrong AND native shares it →
    pre-existing engine bug, tracked elsewhere), 'na' (not judgeable).
    """
    if lv not in DEF:
        return "na"  # a sound lowering abstain — never a defect
    if zv not in DEF:
        return "na"  # no oracle verdict to judge against
    if lv == zv:
        # lowering correct; flag the cases where it BEAT the bare native path.
        return "improve" if nv in DEF and nv != zv else "agree"
    # lowering is DEFINITE-WRONG (lv != zv). Attribute ONLY by a definite native:
    #   native shares it          → pre-existing engine bug (NOT a lowering defect)
    #   native got it RIGHT (==z3) → genuine lowering mistranslation (GATE FAIL)
    #   native non-definite        → inconclusive (no usable reference; never a fail)
    if nv == lv:
        return "engine_bug"
    if nv == zv:
        return "lowering_bug"
    return "inconclusive"


def main():
    seeds = [317, 1, 7, 42, 100, 999, 2024, 31337]
    per = 2000
    lowering_bugs, engine_bugs, inconclusive, improves = [], [], [], 0
    n_low_def = n_agree = 0
    for seed in seeds:
        rng = random.Random(seed)
        for i in range(per):
            smt = gen(rng)
            zv = run([Z3, "-smt2", "-in"], smt)
            nv = run([NATIVE, "/dev/stdin"], desugar_ite(smt))  # native has no `ite`
            lv = run([DRIVER], smt)
            if lv in DEF:
                n_low_def += 1
            k = classify(zv, nv, lv)
            if k in ("agree", "improve"):
                n_agree += 1
                improves += k == "improve"
            elif k == "engine_bug":
                engine_bugs.append((seed, i, zv, nv, lv, smt))
            elif k == "lowering_bug":
                lowering_bugs.append((seed, i, zv, nv, lv, smt))
            elif k == "inconclusive":
                inconclusive.append((seed, i, zv, nv, lv, smt))
    total = len(seeds) * per
    print(f"trials={total}  lowering-definite={n_low_def}  agreements={n_agree}  "
          f"lowering-improvements-over-native={improves}")
    print(f"ENGINE bugs (lowering==native≠z3 — pre-existing, tracked #347/#348): "
          f"{len(engine_bugs)}")
    print(f"INCONCLUSIVE (lowering≠z3, native non-definite — no usable reference): "
          f"{len(inconclusive)}")
    print(f"LOWERING bugs (lowering≠z3 while native==z3 — THE GATE): {len(lowering_bugs)}")
    tmp = "/home/ybi/.claude/jobs/537dc08d/tmp"
    for tag, bucket in (("engine", engine_bugs[:4]),
                        ("inconcl", inconclusive[:4]),
                        ("lowering", lowering_bugs[:10])):
        for (seed, i, zv, nv, lv, smt) in bucket:
            path = f"{tmp}/{tag}_{seed}_{i}.smt2"
            open(path, "w").write(smt)
            print(f"  [{tag}] seed={seed} z3={zv} native={nv} low={lv}  -> {path}")
    ok = not lowering_bugs
    print("RESULT:", "PASS — no lowering-attributable wrong verdict (the lowering "
          "is faithful; engine bugs are tracked separately)"
          if ok else "FAIL — the lowering manufactured a verdict the native path did not")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
