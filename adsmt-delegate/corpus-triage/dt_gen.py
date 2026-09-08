#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors
"""Random DATATYPE queries with NO name collisions — the neutral control for
the collision-biased generator. Every selector name is globally unique, so a
verdict change here is about the structural rules themselves."""
import random, sys, os
def gen(seed):
    r = random.Random(seed)
    # 1-2 sorts; each 1-3 constructors; fields drawn from Int / the sorts.
    sorts = ["S"] if r.random() < 0.45 else ["S", "T"]
    decl = {}
    for si, s in enumerate(sorts):
        n = r.randint(1, 3)
        ctors = []
        for c in range(n):
            na = r.randint(0, 2)
            fields = [(f"{s}c{c}f{a}", r.choice(["Int"] + sorts)) for a in range(na)]
            ctors.append((f"{s}c{c}", fields))
        # well-foundedness: ensure a base case
        if all(any(t in sorts for _, t in fl) or fl == [] and False for _, fl in ctors):
            ctors.append((f"{s}base", []))
        decl[s] = ctors
    def render(s):
        return "(" + " ".join("(" + c + "".join(f" ({n} {t})" for n, t in fl) + ")"
                              for c, fl in decl[s]) + ")"
    L = ["(set-logic ALL)",
         "(declare-datatypes (" + " ".join(f"({s} 0)" for s in sorts) + ") ("
         + " ".join(render(s) for s in sorts) + "))"]
    vars_of = {}
    for s in sorts:
        vars_of[s] = [f"{s.lower()}{i}" for i in range(2)]
        for v in vars_of[s]:
            L.append(f"(declare-const {v} {s})")
    L.append("(declare-const i Int)")
    allsel = {s: [(n, t) for _, fl in decl[s] for n, t in fl] for s in sorts}
    def term(s, d=0):
        if d > 1 or r.random() < 0.45:
            return r.choice(vars_of[s])
        cands = [(sn, src) for src in sorts for sn, t in allsel[src] if t == s]
        if cands and r.random() < 0.5:
            sn, src = r.choice(cands)
            return f"({sn} {term(src, d+1)})"
        c, fl = r.choice(decl[s])
        if not fl:
            return c
        return "(" + c + " " + " ".join(
            (term(t, d + 1) if t in sorts else "i") for _, t in fl) + ")"
    for _ in range(r.randint(1, 4)):
        s = r.choice(sorts)
        k = r.random()
        if k < 0.6:
            a, b = term(s), term(s)
            L.append(f"(assert {'(= %s %s)'%(a,b) if r.random()<0.45 else '(not (= %s %s))'%(a,b)})")
        elif k < 0.8:
            c, _ = r.choice(decl[s])
            t = f"((_ is {c}) {term(s)})"
            if r.random() < 0.5:
                t = f"(not {t})"
            L.append(f"(assert {t})")
        else:
            ints = [(n, src) for src in sorts for n, t in allsel[src] if t == "Int"]
            if ints:
                n, src = r.choice(ints)
                L.append(f"(assert (= ({n} {term(src)}) {r.randint(0,3)}))")
    L.append("(check-sat)")
    return "\n".join(L) + "\n"
out = sys.argv[1]; lo, hi = int(sys.argv[2]), int(sys.argv[3])
os.makedirs(out, exist_ok=True)
for s in range(lo, hi):
    open(f"{out}/d{s:05d}.smt2", "w").write(gen(s))
