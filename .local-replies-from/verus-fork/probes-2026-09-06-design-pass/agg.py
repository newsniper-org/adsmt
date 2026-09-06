#!/usr/bin/env python3
import re, os, glob, statistics, collections

ROOT = "/home/ybi/verus-fork/.local-replies-to/adsmt/corpus-2026-07-04-lukb-per-obligation"

FAMS = [  # priority order for the partition
 ("fuel",   re.compile(r"fuel|FuelId|\bFuel\b|rec%|\bsucc\(|\bzero\b")),
 ("poly",   re.compile(r"\bPoly\b|`%I`|`%B`|`%R`|`%F`|\bI\(|\bB\(|\bR\(|has_type|as_type|`%?Poly%")),
 ("height", re.compile(r"height|Height|\bDcr\b|check_decrease|partial-order")),
 ("type",   re.compile(r"\bType\b|TYPE%|tr_bound%|proj%|\bsized\(|\bDST\(|\bREF\(|\bBOX\(|\bRC\(|\bARC\(|GHOST|TRACKED|NEVER|CONST_PTR|MUTREF|SLICE|PTR\(|ARRAY\(|STRSLICE|ALLOCATOR_GLOBAL|const_int|const_bool|CONST_INT|CONST_BOOL|\bBOOL\b|\bINT\b|\bNAT\b|\bREAL\b|\bCHAR\b|USIZE|ISIZE|UINT\(|SINT\(|FLOAT\(")),
 ("machint",re.compile(r"nClip|uClip|iClip|charClip|uInv|iInv|charInv|uHi|iLo|iHi|\bSZ\b")),
 ("misc",   re.compile(r"ext_eq|mut_ref|closure_req|closure_ens|default_ens|has_resolved|fndef|bitxor|bitand|bitor|bitshr|bitshl|bitnot|singular_mod")),
]

def items(path):
    out=[]
    for line in open(path, encoding="utf-8"):
        t=line.strip()
        if not t or t.startswith("#"): continue
        for k in ("axiom:","goal:","sort ","const ","fn ","data "):
            if t.startswith(k):
                out.append((k.rstrip(": "), t)); break
    return out

tot_lines=tot_items=tot_ax=0
part=collections.Counter(); clean=0
per=[]
clipuse=collections.Counter()
for f in sorted(glob.glob(os.path.join(ROOT,"*","*.lukb"))):
    rel=os.path.relpath(f,ROOT)
    txt=open(f,encoding="utf-8").read()
    its=items(f)
    ax=[s for k,s in its if k=="axiom"]
    tot_lines+=txt.count("\n"); tot_items+=len(its); tot_ax+=len(ax)
    nclean=0
    for k,s in its:
        for name,rx in FAMS:
            if rx.search(s): part[name]+=1; break
        else:
            part["residual"]+=1; nclean+=1
    clean+=nclean
    per.append((rel,txt.count("\n"),len(its),len(ax),nclean))
    # applied machine-int clipping inside the obligation section
    ob = txt.split("# ── obligation ──")[-1]
    if re.search(r"uClip\(|iClip\(|charClip\(", ob): clipuse["u/i/charClip"]+=1
    if "nClip(" in ob: clipuse["nClip"]+=1

print(f"files={len(per)}  total_lines={tot_lines}  total_items={tot_items}  total_axioms={tot_ax}")
ls=[p[1] for p in per]; axs=[p[3] for p in per]; cl=[p[4] for p in per]
print(f"lines:  min={min(ls)} median={statistics.median(ls)} max={max(ls)} mean={statistics.mean(ls):.1f}")
print(f"axioms: min={min(axs)} median={statistics.median(axs)} max={max(axs)} mean={statistics.mean(axs):.1f}")
print(f"residual (items matching NO scaffolding family): min={min(cl)} median={statistics.median(cl)} max={max(cl)} total={clean}")
print()
print("partition of all items across the whole corpus (first-match priority):")
tot=sum(part.values())
for name,_ in FAMS+[("residual",None)]:
    print(f"  {name:9s} {part[name]:7d}  {100*part[name]/tot:5.1f}%")
print()
print("obligations whose GOAL/assumption section applies machine-int clipping:", dict(clipuse))
print()
print("smallest / largest files:")
for rel,l,i,a,c in sorted(per,key=lambda x:x[1])[:3]: print(f"  {rel:32s} lines={l} items={i} axioms={a} residual={c}")
for rel,l,i,a,c in sorted(per,key=lambda x:-x[1])[:3]: print(f"  {rel:32s} lines={l} items={i} axioms={a} residual={c}")
