#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors
"""Collision-biased DATATYPE query generator.

Selector names deliberately REUSE constructor names of another datatype in the
same group. SMT-LIB requires a selector name to be distinct only inside its own
group, so this is legal and both z3 and cvc5 accept it — and it is the shape the
general datatype generator never produces, which is why three separate
differentials came back clean while 35 false `unsat`s per 2000 queries sat in
the structural rules (closed by f1e0614 / 742aa6d / 408e950).

Usage:  dt_collision_gen.py <outdir> <lo> <hi>   then run each query through
the candidate build, z3 and cvc5, and score NEWLY-INTRODUCED false unsats
against the baseline rather than the raw count.
"""
# Collision-biased generator: selector names deliberately REUSE constructor names
# of another datatype in the same group (legal SMT-LIB; z3 and cvc5 both accept).
def gen(seed):
    r = random.Random(seed)
    # E: a well-founded "donor" datatype whose constructor names get reused as selectors
    donor_ctors = [("dnil", []), ("dcons", [("dh", "Int"), ("dt", "E")])]
    # P: the target sort. 1 or 2 constructors; some selectors named after E's ctors.
    npc = r.choice([1, 2])
    pctors = []
    for c in range(npc):
        na = r.randint(1, 3)
        fields = []
        for a in range(na):
            ft = r.choice(["P", "E", "Int", "P"])
            # collide with probability .5
            if r.random() < 0.5:
                sn = r.choice(["dnil", "dcons", "dh", "dt"])
            else:
                sn = f"p{c}s{a}"
            fields.append((sn, ft))
        pctors.append((f"pc{c}", fields))
    # well-foundedness for P
    if all(any(t == "P" for _, t in f) for _, f in pctors):
        pctors.append(("pbase", []))
    # de-duplicate selector names inside P (SMT-LIB requires distinct within a group)
    seen = set()
    for i, (c, fl) in enumerate(pctors):
        nf = []
        for sn, ft in fl:
            k = sn
            j = 0
            while k in seen:
                j += 1; k = f"{sn}_{j}"
            seen.add(k); nf.append((k, ft))
        pctors[i] = (c, nf)
    def render(cs):
        return "(" + " ".join("(" + c + "".join(f" ({s} {t})" for s, t in fl) + ")" for c, fl in cs) + ")"
    L = ["(set-logic ALL)",
         f"(declare-datatypes ((E 0) (P 0)) ({render(donor_ctors)} {render(pctors)}))"]
    for v in ["p", "q"]: L.append(f"(declare-const {v} P)")
    L.append("(declare-const e E)")
    L.append("(declare-const i Int)")
    allsel = [(s, t) for _, fl in pctors for s, t in fl]
    def pterm(d=0):
        if d > 1 or r.random() < 0.5: return r.choice(["p", "q"])
        cands = [s for s, t in allsel if t == "P"]
        if cands and r.random() < 0.7: return f"({r.choice(cands)} {pterm(d+1)})"
        c, fl = r.choice(pctors)
        if not fl: return c
        return "(" + c + " " + " ".join(
            (pterm(d+1) if t=="P" else ("e" if t=="E" else "i")) for _, t in fl) + ")"
    for _ in range(r.randint(1, 4)):
        k = r.random()
        if k < 0.65:
            a, b = pterm(), pterm()
            L.append(f"(assert {'(= %s %s)'%(a,b) if r.random()<0.4 else '(not (= %s %s))'%(a,b)})")
        elif k < 0.85:
            c, _ = r.choice(pctors)
            L.append(f"(assert (not ((_ is {c}) {pterm()})))")
        else:
            cands = [s for s, t in allsel if t == "E"]
            if cands: L.append(f"(assert (= ({r.choice(cands)} {pterm()}) e))")
            cands = [s for s, t in allsel if t == "Int"]
            if cands: L.append(f"(assert (= ({r.choice(cands)} {pterm()}) i))")
    L.append("(check-sat)")
    return "\n".join(L) + "\n"

out = sys.argv[1]; lo, hi = int(sys.argv[2]), int(sys.argv[3])
os.makedirs(out, exist_ok=True)
for s in range(lo, hi):
    open(f"{out}/c{s:05d}.smt2", "w").write(gen(s))
