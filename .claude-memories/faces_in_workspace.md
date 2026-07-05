---
name: faces-in-workspace
description: The adsmt-ir face crates (kernel + SMT-LIB/lukb/ASP faces + CIC→HOL lowering) were absorbed from sibling repos into the AD1 workspace as flat members on 2026-06-27 (a stated Phase-2 gate). Canonical source is now AD1/; the old ~/adsmt-ir* repos are frozen archives.
metadata: 
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**2026-06-27 (`AD1` `0f9b007`, faces-in-workspace = a Phase-2 gate): the 5 `adsmt-ir*` face crates were absorbed into the AD1 workspace as flat members.** Canonical source is now **`AD1/adsmt-ir`, `AD1/adsmt-ir-smtlib`, `AD1/adsmt-ir-lukb`, `AD1/adsmt-ir-asp`, `AD1/adsmt-ir-lower`** (added to root `Cargo.toml` `members`). The crate graph: `adsmt-ir` = the typed CIC kernel (no path-deps); `-smtlib`/`-lukb`/`-asp` faces dep `adsmt-ir`; `-lower` deps `adsmt-ir` + `adsmt-core` + `adsmt-theory` (now `../` intra-workspace, was `../AD1/`).

**The old `/home/ybi/adsmt-ir{,-smtlib,-lukb,-asp,-lower}` repos are FROZEN HISTORY ARCHIVES** — do NOT edit them; edit the AD1 copies. (Absorption = source-only copy, so it's reversible; the archives hold the pre-absorption git history. Several OTHER memories still say a face "lives in `~/adsmt-ir-…`" — that now means the AD1 member; the `~/` path is the archive.) Per-crate `.gitignore` was dropped to match the workspace convention (no member has one).

**Only prior AD1 consumer of a face = `adsmt-lsp`** (`adsmt-ir-asp = { path = "../adsmt-ir-asp", optional }`, rewired from `../../`). The verus-fork `-V emit-lukb` producer (`air/src/lukb.rs`) is self-contained (NO adsmt dep), so it's UNAFFECTED; its structural-differential harness `check_lukb` now lives at `AD1/adsmt-ir-lukb/examples/check_lukb.rs`.

Validated: all 5 new members + `adsmt-lsp` build + test green in-workspace; `cargo metadata` lists them. Full `cargo test --workspace` is the user's `!` gate (per [[feedback_long_test_runs]]). See [[cic_hol_lowering]], [[verus_emits_lukb_surface]], [[asp_face_design]].
