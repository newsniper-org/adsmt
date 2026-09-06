#!/usr/bin/env python3
import re, os, glob, collections, csv

ROOT = "/home/ybi/verus-fork/.local-replies-to/adsmt/corpus-2026-07-04-lukb-per-obligation"

MODREC   = re.compile(r"`([A-Za-z0-9_]+)!rec%([A-Za-z0-9_.]+?)\.")
VSTDMOD  = ("vstd", "core", "alloc")
SEQSORT  = re.compile(r"TYPE%vstd!(seq|map|set|multiset)\.")
CHOOSE   = re.compile(r"%%choose|choose%|`.*!.*choose")
DEEPEQ   = re.compile(r"ext_eq\(true")
NONLIN   = re.compile(r"%%hidden|nlarith|singular")
CLOSURE  = re.compile(r"`.*!.*closure|closure_req\(`[a-z]")

# manifest
man = {}
with open(os.path.join(ROOT,"manifest.tsv"), encoding="utf-8") as fh:
    rd = csv.DictReader(fh, delimiter="\t")
    for r in rd:
        man[r["obligation"]] = r

rows = []
for f in sorted(glob.glob(os.path.join(ROOT,"*","*.lukb"))):
    rel = os.path.relpath(f, ROOT)
    fixture = rel.split("/")[0]
    txt = open(f, encoding="utf-8").read()
    modrecs = sorted(set(f"{m.group(1)}!{m.group(2)}" for m in MODREC.finditer(txt)
                         if m.group(1) not in VSTDMOD))
    seq   = bool(SEQSORT.search(txt))
    ch    = bool(CHOOSE.search(txt))
    deep  = bool(DEEPEQ.search(txt))
    if modrecs:
        cls, why = "b", "recursive spec fn: " + ",".join(sorted(set(x.split("!")[1] for x in modrecs)))
    elif seq:
        cls, why = "c", "vstd library sort (Seq/Map/Set) + broadcast axiom group" + (" + deep ext_eq" if deep else "")
    elif ch:
        cls, why = "c", "choose / Hilbert-epsilon binder"
    else:
        cls, why = "a", ""
    rows.append(dict(ob=rel, fixture=fixture, lines=txt.count("\n"), cls=cls, why=why,
                     verdict=man.get(rel.replace(".lukb",""), {}).get("class", "(not in manifest)")))

# per-fixture rollup
byfix = collections.OrderedDict()
for r in rows:
    byfix.setdefault(r["fixture"], []).append(r)

print("=== PER-OBLIGATION CLASS COUNTS ===")
cc = collections.Counter(r["cls"] for r in rows)
print(dict(cc), "total", len(rows))
print()
print("=== manifest-only (209) ===")
mrows = [r for r in rows if r["verdict"] != "(not in manifest)"]
print(dict(collections.Counter(r["cls"] for r in mrows)), "total", len(mrows))
print()
print("=== class x verdict (manifest rows) ===")
cx = collections.Counter((r["cls"], r["verdict"]) for r in mrows)
for k in sorted(cx): print("  ", k, cx[k])
print()
print("=== PER FIXTURE ===")
for fx, rs in byfix.items():
    c = collections.Counter(r["cls"] for r in rs)
    whys = sorted(set(r["why"] for r in rs if r["why"]))
    print(f"{fx:22s} obs={len(rs):3d}  a={c['a']:3d} b={c['b']:3d} c={c['c']:3d}  {'; '.join(whys)}")
