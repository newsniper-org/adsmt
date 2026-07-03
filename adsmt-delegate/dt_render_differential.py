#!/usr/bin/env python3
"""#392 — datatype-render delegation randomized z3-differential.

Generates random datatype-bearing .lukb programs (the supported surface:
data/const/fn/axiom/goal, match, if, forall+trigger), runs release adsmtc
(--output-mode full, ADSMT_DELEGATE_DEBUG=1), captures the delegation's
rendered SMT-LIB from stderr, and gates:

  P0 SPURIOUS_UNSAT : adsmt definite-unsat  AND  z3(render) = sat
  P0 SPURIOUS_SAT   : adsmt definite-sat    AND  z3(render) = unsat
  RENDER_INVALID    : z3 reports a parse/sort error on the render

Only DEFINITE adsmt verdicts are gated (possibly-*/unknown are lattice-
honest abstentions). Disagreeing cases are saved under FAILDIR.

Usage: python3 dt_render_differential.py [N=2000] [START_SEED=0]
Env:   ADSMTC (default: <repo>/target/release/adsmtc — build with
       `cargo build --release -p adsmtc --features "cas oxiz"`),
       Z3 (default: z3 on PATH), DT_DIFF_DIR (work dir, default: mkdtemp).
"""
import random, subprocess, sys, os, re, tempfile

_REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ADSMTC = os.environ.get("ADSMTC", os.path.join(_REPO, "target", "release", "adsmtc"))
Z3 = os.environ.get("Z3", "z3")
TMP = os.environ.get("DT_DIFF_DIR") or tempfile.mkdtemp(prefix="dt-render-diff-")
FAILDIR = os.path.join(TMP, "dt_diff_failures")
os.makedirs(FAILDIR, exist_ok=True)

INT_LITS = ["0", "1", "2", "3"]


class Gen:
    def __init__(self, seed):
        self.r = random.Random(seed)
        self.lines = []
        self.datatypes = {}  # name -> [(ctor, [(field, type)])]
        self.consts = {}  # name -> type
        self.fns = {}  # name -> ([argtypes], ret)

    def fresh_dt(self, i):
        r = self.r
        name = f"D{i}"
        nc = r.randint(2, 3)
        ctors = []
        for j in range(nc):
            cname = f"c{i}{j}"
            fields = []
            # ~40% of non-first ctors carry 1-2 fields
            if j > 0 and r.random() < 0.4:
                for k in range(r.randint(1, 2)):
                    ft = r.choice(["Int", "Bool", name] + list(self.datatypes))
                    fields.append((f"f{i}{j}{k}", ft))
            ctors.append((cname, fields))
        self.datatypes[name] = ctors
        rhs = " | ".join(
            c if not fs else f"{c}({', '.join(f'{fn}: {ft}' for fn, ft in fs)})"
            for c, fs in ctors
        )
        self.lines.append(f"data {name} = {rhs}")

    def ctor_term(self, dt, depth=0):
        """A ground constructor term of datatype dt."""
        r = self.r
        ctors = self.datatypes[dt]
        # at depth, prefer nullary to terminate
        pool = [c for c in ctors if not c[1]] if depth >= 2 else ctors
        if not pool:
            pool = [c for c in ctors if not c[1]] or ctors
        cname, fields = r.choice(pool)
        if not fields:
            return cname
        args = []
        for _, ft in fields:
            args.append(self.term_of(ft, depth + 1))
        return f"{cname}({', '.join(args)})"

    def term_of(self, ty, depth=0):
        r = self.r
        cands = [n for n, t in self.consts.items() if t == ty]
        if ty == "Int":
            pool = INT_LITS + cands
            return r.choice(pool)
        if ty == "Bool":
            return r.choice(["true", "false"] + cands)
        if cands and r.random() < 0.4:
            return r.choice(cands)
        return self.ctor_term(ty, depth)

    def formula(self):
        """A ground(ish) Bool formula over the declared vocabulary."""
        r = self.r
        kind = r.random()
        dts = list(self.datatypes)
        boolfns = [(f, a) for f, (a, ret) in self.fns.items() if ret == "Bool"]
        intfns = [(f, a) for f, (a, ret) in self.fns.items() if ret == "Int"]
        if kind < 0.35 and dts:
            dt = r.choice(dts)
            a, b = self.term_of(dt), self.term_of(dt)
            eq = f"{a} = {b}"
            return f"not ({eq})" if r.random() < 0.4 else eq
        if kind < 0.55 and boolfns:
            f, args = r.choice(boolfns)
            call = f"{f}({', '.join(self.term_of(t) for t in args)})"
            return f"not {call}" if r.random() < 0.3 else call
        if kind < 0.75 and intfns:
            f, args = r.choice(intfns)
            call = f"{f}({', '.join(self.term_of(t) for t in args)})"
            op = r.choice([">=", ">", "=", "<="])
            return f"{call} {op} {r.choice(INT_LITS)}"
        if dts:
            # match goal over a datatype const/term
            dt = r.choice(dts)
            scrut = self.term_of(dt)
            arms = []
            for cname, fields in self.datatypes[dt]:
                if not fields:
                    arms.append(f"{cname} => {r.choice(['true', 'false'])}")
                else:
                    vs = [f"v{n}" for n in range(len(fields))]
                    body = "true"
                    # compare a bound field when it's a datatype/Int
                    fn0, ft0 = fields[0]
                    if ft0 in self.datatypes:
                        body = f"{vs[0]} = {self.ctor_term(ft0, 2)}"
                    elif ft0 == "Int":
                        body = f"{vs[0]} >= 0"
                    arms.append(f"{cname}({', '.join(vs)}) => {body}")
            return f"match {scrut} {{ {', '.join(arms)} }}"
        x, y = self.term_of("Int"), self.term_of("Int")
        return f"{x} >= {y}"

    def program(self):
        r = self.r
        for i in range(r.randint(1, 2)):
            self.fresh_dt(i)
        dts = list(self.datatypes)
        for i in range(r.randint(1, 3)):
            ty = r.choice(dts + ["Int"])
            self.consts[f"k{i}"] = ty
            self.lines.append(f"const k{i}: {ty}")
        for i in range(r.randint(0, 2)):
            nargs = r.randint(1, 2)
            args = [r.choice(dts + ["Int"]) for _ in range(nargs)]
            ret = r.choice(["Bool", "Int"])
            self.fns[f"g{i}"] = (args, ret)
            sig = ", ".join(f"x{n}: {t}" for n, t in enumerate(args))
            self.lines.append(f"fn g{i}({sig}): {ret}")
        for _ in range(r.randint(0, 3)):
            if r.random() < 0.15 and self.fns:
                # a quantified axiom with trigger, over ONE datatype/Int arg fn
                f, (args, ret) = r.choice(list(self.fns.items()))
                if len(args) == 1:
                    v = "q"
                    call = f"{f}({v})"
                    body = call if ret == "Bool" else f"{call} >= 0"
                    self.lines.append(
                        f"axiom: forall {v}: {args[0]}. {body} trigger {call}"
                    )
                    continue
            self.lines.append(f"axiom: {self.formula()}")
        # goal, sometimes with hypotheses
        if r.random() < 0.4:
            hyp = self.formula()
            self.lines.append(f"goal g: {hyp} |- {self.formula()}")
        else:
            self.lines.append(f"goal g: {self.formula()}")
        return "\n".join(self.lines) + "\n"


def run_case(seed):
    src = Gen(seed).program()
    path = os.path.join(TMP, "dt_case.lukb")
    with open(path, "w") as f:
        f.write(src)
    try:
        p = subprocess.run(
            [ADSMTC, "--output-mode", "full", path],
            capture_output=True, text=True, timeout=30,
            env={**os.environ, "ADSMT_DELEGATE_DEBUG": "1", "ADSMT_LUKB_DEBUG": "1"},
        )
    except subprocess.TimeoutExpired:
        return src, "timeout", None, None
    verdict = None
    for l in p.stdout.strip().splitlines():
        l = l.strip()
        if l.startswith("smt "):
            verdict = l.split(None, 1)[1]
    if "elaborate failed" in p.stderr or "lower failed" in p.stderr:
        return src, "gen-error", None, None
    # last rendered script block in stderr
    script = None
    m = re.findall(r"\[dbg\] script:\n(.*?)(?=\n\[dbg\]|\Z)", p.stderr, re.S)
    if m:
        script = m[-1]
    return src, verdict, script, p.stderr


def z3_verdict(script):
    try:
        out = subprocess.run(
            [Z3, "-smt2", "-in"], input=script, capture_output=True, text=True,
            timeout=30,
        )
    except subprocess.TimeoutExpired:
        return "timeout"
    text = out.stdout.strip()
    if "(error" in text:
        return "error:" + text.splitlines()[0]
    for l in reversed(text.splitlines()):
        if l.strip() in ("sat", "unsat", "unknown"):
            return l.strip()
    return "other"


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    start = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    stats = {"gen-error": 0, "no-script": 0, "agree": 0, "abstain": 0,
             "spurious-unsat": 0, "spurious-sat": 0, "render-invalid": 0,
             "z3-other": 0, "timeout": 0}
    for seed in range(start, start + n):
        src, verdict, script, err = run_case(seed)
        if verdict in ("gen-error", "timeout") or verdict is None:
            stats["gen-error" if verdict == "gen-error" else "timeout"] += 1
            continue
        if script is None:
            stats["no-script"] += 1
            continue
        zv = z3_verdict(script)
        cat = None
        if zv.startswith("error"):
            cat = "render-invalid"
        elif zv in ("timeout", "other", "unknown"):
            cat = "z3-other"
        elif verdict == "definite-unsat" and zv == "sat":
            cat = "spurious-unsat"
        elif verdict == "definite-sat" and zv == "unsat":
            cat = "spurious-sat"
        elif verdict in ("definite-unsat", "definite-sat"):
            cat = "agree"
        else:
            cat = "abstain"  # possibly-* / unknown: honest abstention
        stats[cat] += 1
        if cat in ("spurious-unsat", "spurious-sat", "render-invalid"):
            base = os.path.join(FAILDIR, f"{cat}-{seed}")
            open(base + ".lukb", "w").write(src)
            open(base + ".smt2", "w").write(script)
            open(base + ".info", "w").write(f"adsmt={verdict}\nz3={zv}\n")
            print(f"[{seed}] {cat}: adsmt={verdict} z3={zv}", flush=True)
        if (seed - start + 1) % 200 == 0:
            print(f"...{seed - start + 1}/{n} {stats}", flush=True)
    print(f"DONE {stats}")


if __name__ == "__main__":
    main()
