#!/usr/bin/env python3
import re, sys, os, glob, json, collections

ROOT = "/home/ybi/verus-fork/.local-replies-to/adsmt/corpus-2026-07-04-lukb-per-obligation"

FAM = {
 "fuel":      [r"\bfuel\b", r"FuelId", r"\bFuel\b", r"fuel_bool", r"fuel_defaults", r"rec%", r"%%fuel", r"\bsucc\(", r"fuel%"],
 "poly":      [r"\bPoly\b", r"`%I`", r"\bI\(", r"\bB\(", r"\bR\(", r"has_type", r"as_type", r"`%B`", r"`%R`", r"`%F`", r"`%Poly%"],
 "height":    [r"\bheight\b", r"\bHeight\b", r"height_lt", r"\bDcr\b", r"check_decrease", r"partial-order"],
 "nclip":     [r"nClip", r"uClip", r"iClip", r"charClip"],
 "fueldist":  [r"%%fuel_distinct_ord%%"],
 "type":      [r"\bType\b", r"\bTYPE%", r"tr_bound%", r"proj%", r"\bsized\("],
}
# stricter per-request families
REQ_FAM = {
 "fuel/FuelId/fuel_bool/rec%": [r"fuel", r"FuelId", r"fuel_bool", r"rec%", r"\bFuel\b"],
 "Poly/%I/I(/box/unbox/has_type": [r"\bPoly\b", r"`%I`", r"\bI\(", r"has_type", r"`%B`", r"`%R`", r"`%F`", r"as_type", r"`%Poly%", r"`Poly%"],
 "height/Height/height_lt/Dcr/check_decrease": [r"height", r"Height", r"height_lt", r"\bDcr\b", r"check_decrease", r"partial-order"],
 "nClip": [r"nClip"],
 "%%fuel_distinct_ord%%": [r"%%fuel_distinct_ord%%"],
}

def parse(path):
    items = []
    for ln, line in enumerate(open(path, encoding="utf-8"), 1):
        s = line.rstrip("\n")
        t = s.strip()
        if not t: kind = "blank"
        elif t.startswith("#"): kind = "comment"
        elif t.startswith("axiom:"): kind = "axiom"
        elif t.startswith("goal:"): kind = "goal"
        elif t.startswith("sort "): kind = "sort"
        elif t.startswith("const "): kind = "const"
        elif t.startswith("fn "): kind = "fn"
        elif t.startswith("data "): kind = "data"
        else: kind = "other"
        items.append((ln, kind, s))
    return items

def report(rel):
    path = os.path.join(ROOT, rel)
    items = parse(path)
    n = len(items)
    kinds = collections.Counter(k for _,k,_ in items)
    axioms = [s for _,k,s in items if k=="axiom"]
    decls  = [s for _,k,s in items if k in ("sort","const","fn","data")]
    out = {"file": rel, "total_lines": n, "kinds": dict(kinds)}
    # split: preamble vs obligation section
    obidx = next((i for i,(_,_,s) in enumerate(items) if s.strip().startswith("# ── obligation")), None)
    if obidx is not None:
        pre = items[:obidx]; post = items[obidx:]
        out["preamble_lines"] = len(pre)
        out["obligation_lines"] = len([x for x in post if x[1] not in ("blank",)])
        out["obligation_axioms"] = len([x for x in post if x[1]=="axiom"])
        out["preamble_axioms"] = len([x for x in pre if x[1]=="axiom"])
    fam = {}
    for name, pats in REQ_FAM.items():
        rx = re.compile("|".join(pats))
        fam[name] = {
          "axioms": sum(1 for a in axioms if rx.search(a)),
          "decls":  sum(1 for d in decls if rx.search(d)),
          "all_items": sum(1 for _,k,s in items if k in ("axiom","sort","const","fn","data") and rx.search(s)),
        }
    out["families"] = fam
    # union of all scaffolding
    allrx = re.compile("|".join(p for pats in REQ_FAM.values() for p in pats))
    typerx = re.compile(r"\bType\b|\bTYPE%|tr_bound%|proj%|\bsized\(")
    unionrx = re.compile("|".join(list(p for pats in REQ_FAM.values() for p in pats)+[r"\bType\b", r"TYPE%", r"tr_bound%", r"proj%", r"sized\(", r"uInv", r"iInv", r"charInv", r"uHi", r"iLo", r"iHi", r"uClip", r"iClip", r"charClip", r"\bSZ\b", r"ext_eq", r"mut_ref", r"closure_", r"default_ens", r"has_resolved", r"fndef", r"bit(xor|and|or|shr|shl|not)", r"singular_mod"]))
    out["scaffold_union_items"] = sum(1 for _,k,s in items if k in ("axiom","sort","const","fn","data") and unionrx.search(s))
    out["total_items"] = sum(1 for _,k,s in items if k in ("axiom","sort","const","fn","data","goal"))
    out["clean_items"] = [s for _,k,s in items if k in ("axiom","sort","const","fn","data","goal") and not unionrx.search(s)]
    return out

if __name__ == "__main__":
    for rel in sys.argv[1:]:
        r = report(rel)
        clean = r.pop("clean_items")
        print(json.dumps(r, ensure_ascii=False, indent=1))
        print("  CLEAN (no scaffolding token) items:", len(clean))
        for c in clean: print("   |", c[:200])
        print()
