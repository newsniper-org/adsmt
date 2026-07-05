---
name: feedback-per-slice-doc-sweep
description: "Standing rule (user, 2026-06-26): at EVERY task/slice completion, thoroughly check and update ALL docs / comments / books with no omission — not just at version bumps."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**At every task/slice completion, sweep and update ALL documentation with no omission: in-code doc comments, design docs (DESIGN.md/README), and the docs/books.** (User, 2026-06-26, starting from the adsmt-ir-asp pooling/interval slice.)

**Why:** the user wants documentation to never drift behind the code — previously a full docs/comments/4-lang-book sweep happened only at version-bump milestones (rc.36/rc.39/etc.); now it is per-slice. Stale docs (e.g. an `lib.rs` "following slices" note for features already landed) are a defect to fix the same slice that lands the feature.

**How to apply:** after the code + tests of a slice are green, BEFORE (or as part of) the commit:
1. in-code comments — module docs + fn docs touched by the slice are already current (keep doing this), AND re-scan for now-stale claims elsewhere (status sections, "later slice" notes, grammar/EBNF blocks).
2. design docs — the crate's `DESIGN.md` / `README` (e.g. `adsmt-ir-asp/DESIGN.md`): reflect the new feature + move it from "planned" to "landed".
3. **books** — the AD1 `docs/books` are **Typst** (`.typ`), two tracks (`implement-from-scratch`, `learning-materials`) × **4 languages** (`en`/`ko`/`ja`/`de`), each lang dir = `main.typ` + `chapters/NN-*.typ`, compiled `typst compile main.typ` (a SEPARATE git repo at `docs/books`). **Follow this method exactly** (user, 2026-06-26 "메인 repo 방식 그대로"). **typed-ASP face book home (user-decided 2026-06-26): a NEW APPENDIX in AD1 `docs/books`** extending the `B-lukb-surface` lineage (the lu-kb surface appendix; typed-ASP = the lu-kb successor) — e.g. `D-typed-asp-surface.typ`, in all 4 languages, registered in each `main.typ`. **Cadence: BATCHED at coherent feature blocks** (per ladder level / sugar group), NOT every micro-slice — the crate rustdoc+DESIGN.md is the every-slice part; the book appendix updates when a coherent block lands.
4. keep the four book languages in lockstep (the established mirror policy); the `docs/books` repo is committed/pushed by the user (separate repo).

This is a CHECKLIST per slice, not a separate milestone task. Relates to [[asp-face-design]] (the current per-slice work) and the prior version-bump doc-sweep practice.
