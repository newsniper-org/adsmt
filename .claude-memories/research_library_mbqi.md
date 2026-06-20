---
name: research-library-mbqi
description: "in-repo research library of MBQI / quantifier-instantiation papers at .claude-research-library/ — for improving OxiZ's clean-MBQI engine"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**`<adsmt root>/.claude-research-library/`** (= `/home/ybi/AD1/.claude-research-library/`) is the user's dedicated research-library path. Populated 2026-06-20 with **13 open-access PDFs on MBQI / quantifier instantiation** + a `README.md` index (reading order + per-paper relevance mapping to adsmt's open problems). Purpose: inform improvements to OxiZ's **clean-MBQI** engine ([[oxiz-mbqi-rewrite]]) — its model-construction recognizers (#264/#279/#280/#281) and the prelude-scale e-matching wall the full-prelude `(abduce)` repro hits ([[verus_fork_integration]]).

Spans 2007→2025: e-matching foundation (de Moura/Bjørner 2007); **the MBQI paper** (Ge/de Moura, CAV 2009); finite-model-finding QI (Reynolds+ 2013); CDQI / conflicting instances (Reynolds+ FMCAD 2014, already ported #229); CCFV unifying instantiation calculus (Barbosa+ TACAS 2017); model-based projection (Bjørner/Janota LPAR 2015); CEGQI synthesis (Reynolds+ CAV 2015); counterexample-guided model synthesis (Preiner+ TACAS 2017); enumerative instantiation (Reynolds+ TACAS 2018); syntax-guided QI (Niemetz+ TACAS 2021); trigger-selection / matching-loops (Leino/Pit-Claudel CAV 2016 — the verus-`:pattern` failure mode); e-matching termination (2024); recent strategy rethink (Jakubův/Janota 2025).

Files named `YEAR-authors-venue-topic.pdf`. **NOT gitignored** and **NOT committed** (5.6 MB third-party copyrighted PDFs — held for private study; if `git add -A` is ever run, gitignore the path first). The `README.md` "How this maps to adsmt's open problems" section ties §4 (enumerative/combination) + §5 (trigger discipline/termination) to the prelude-saturation wall, and §1–§3 (model construction / MBP / finite-model) to the clean-MBQI recognizers.
