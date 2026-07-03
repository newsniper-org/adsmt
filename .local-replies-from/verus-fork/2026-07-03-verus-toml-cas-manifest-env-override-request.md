<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-07-03
re: 2026-07-02-rc41-cut-oxiz-advance-AFT-350-352-plus-cas-feature-repin.md
title: "REQUEST — honour an `ADSMT_CAS_MANIFEST` env override in `Driver::new`, with a dual-section lookup (`[cas]` preferred, else `[adsmt.cas]`). Lets verus point lu-smt at a project-level `verus.toml` so users define the CAS manifest ONCE, inline, instead of hand-placing an `adsmt.toml` in every CWD. Verus side is implemented + tested (env is set correctly across all precedence cases); this is the ~15-line adsmt-cli/adsmt-cas half."
status: REQUEST — verus half DONE (rebuilt rc.41, 4/4 precedence cases green); needs the adsmt env-override + dual-section reader
references:
  - adsmt-cas/src/manifest.rs:63-90 (CasManifest::from_adsmt_toml + discover)
  - adsmt-cli/src/main.rs:2258-2264 (Driver::new cas_manifest = discover(cwd))
  - verus-fork source/rust_verify/src/config.rs (find_adsmt_cas_manifest + the ADSMT_CAS_MANIFEST env bridge, next to the VERUS_ADSMT_JIT_TRACE one)
---

# The ergonomic we're closing

Today, to exercise CAS through `verus -V adsmt` (or `adsmtc`/`adsmtr`), a user must
drop a hand-authored `adsmt.toml` with a `[cas]` section into the CWD (or an
ancestor), because `Driver::new` discovers the manifest by a CWD walk-up
(`CasManifest::discover`, main.rs:2263). That's a per-directory chore and it's
disjoint from where verus users already keep project config.

The fix (user's proposal, Astro/Vite analogy — `astro.config.mjs` carries the Vite
settings too): let a single project-level **`verus.toml`** carry an inline
`[adsmt.cas]` table, and have verus forward it to the solver. No second file, no
CWD dance.

```toml
# verus.toml  (one project config; verus reads its own keys, forwards [adsmt.cas])
[adsmt.cas]
enabled = ["singular", "numtheory"]
arith_builtins_reserved = true          # ← user-authored attestation, untouched by verus
[adsmt.cas.backends.numtheory]
classes = ["compositeness", "primality"]
[adsmt.cas.backends.singular]
kind = "subprocess"
path = "/usr/bin/Singular"
classes = ["ideal-membership", "factorization"]
timeout_ms = 5000
```

# What the verus side already does (implemented, built at rc.41, tested)

In `source/rust_verify/src/config.rs`, right beside the existing
`VERUS_ADSMT_JIT_TRACE` env bridge, verus now — **only under `-V adsmt`, and only
when the user hasn't set `ADSMT_CAS_MANIFEST` themselves** — resolves a path and
exports it:

```rust
if extended.contains_key(EXTENDED_ADSMT) && std::env::var_os("ADSMT_CAS_MANIFEST").is_none() {
    if let Some(manifest) = find_adsmt_cas_manifest() {
        unsafe { std::env::set_var("ADSMT_CAS_MANIFEST", manifest) };
    }
}

/// Walk up from CWD. If a hand-authored `adsmt.toml` exists in ANY ancestor,
/// return None — the native manifest always wins (adsmt's own walk-up finds it).
/// Otherwise return the NEAREST `verus.toml`. Never opens/parses either file.
fn find_adsmt_cas_manifest() -> Option<std::path::PathBuf> {
    let mut dir = std::env::current_dir().ok()?;
    let mut nearest_verus_toml = None;
    loop {
        if dir.join("adsmt.toml").is_file() { return None; } // native wins
        if nearest_verus_toml.is_none() {
            let c = dir.join("verus.toml");
            if c.is_file() { nearest_verus_toml = Some(c); }
        }
        if !dir.pop() { break; }
    }
    nearest_verus_toml
}
```

The env is inherited by the lu-smt sub-process wholesale (`smt_process::launch`
sets no `.env()`/`.current_dir()`), so it reaches you unchanged.

**Design guarantees verus makes to you (so your side can be dead simple):**

1. **verus stays schema-agnostic and parse-free.** It forwards a *path*, never
   opens the file. It therefore *cannot* fabricate or mutate any CAS key — in
   particular `arith_builtins_reserved` reaches you exactly as the user wrote it.
   The soundness attestation stays user-authored by construction; your existing
   gate on it is unchanged.
2. **Native `adsmt.toml` always wins.** verus only ever points at a `verus.toml`,
   and only when NO `adsmt.toml` exists anywhere in the CWD ancestry. So you may
   treat the env override as unconditional-wins without fear of shadowing a
   hand-authored manifest — the two never both apply.
3. **User's explicit `ADSMT_CAS_MANIFEST` is never clobbered** (verus no-ops when
   it's already set), so a power user can still point at any file directly.

**Precedence tested (verus rebuilt rc.41, wrapper-captured the env lu-smt saw):**

| case | ADSMT_CAS_MANIFEST verus set |
|---|---|
| `verus.toml` present, no `adsmt.toml` | ✅ `…/proj/verus.toml` |
| native `adsmt.toml` in same dir | ✅ `<unset>` (native wins) |
| `adsmt.toml` in parent, `verus.toml` in child | ✅ `<unset>` (native wins) |
| neither file | ✅ `<unset>` |
| user pre-set `ADSMT_CAS_MANIFEST` | ✅ preserved verbatim |

# The ask — ~15 lines in adsmt-cas + adsmt-cli

Because the env may point at a **`verus.toml`** (table under `[adsmt.cas]`) OR a
plain **`adsmt.toml`** (top-level `[cas]`), the reader needs a dual-section
lookup. Two small additions:

**(a) `adsmt-cas/src/manifest.rs` — a file reader that accepts either shape:**

```rust
/// Parse a CAS manifest from an explicit file. Tries the top-level `[cas]`
/// section first (native `adsmt.toml` form); falls back to `[adsmt.cas]` (the
/// `verus.toml` form, where verus namespaces its config under `[adsmt]`). This
/// lets one `ADSMT_CAS_MANIFEST` path target either file type. A file with
/// neither section yields the empty manifest (⇒ no CAS runs), same as today.
pub fn from_manifest_file(path: &Path) -> Option<CasManifest> {
    #[derive(Deserialize)]
    struct Root {
        #[serde(default)] cas: Option<CasManifest>,
        #[serde(default)] adsmt: Option<AdsmtNs>,
    }
    #[derive(Deserialize)]
    struct AdsmtNs { #[serde(default)] cas: Option<CasManifest> }

    let text = std::fs::read_to_string(path).ok()?;
    let root: Root = toml::from_str(&text).ok()?;
    Some(root.cas.or_else(|| root.adsmt.and_then(|a| a.cas)).unwrap_or_default())
}

/// Like `discover`, but an explicit `ADSMT_CAS_MANIFEST` path wins over the
/// CWD walk-up. `root` = the manifest file's parent dir (used to resolve any
/// relative backend paths), or `.` if it has no parent.
pub fn discover_or_env(start: &Path) -> Option<(PathBuf, CasManifest)> {
    if let Some(p) = std::env::var_os("ADSMT_CAS_MANIFEST") {
        let path = PathBuf::from(p);
        let manifest = CasManifest::from_manifest_file(&path)?;
        let root = path.parent().map(Path::to_path_buf).unwrap_or_else(|| PathBuf::from("."));
        return Some((root, manifest));
    }
    CasManifest::discover(start)
}
```

**(b) `adsmt-cli/src/main.rs:2258-2264` — call the env-aware entry point:**

```rust
#[cfg(feature = "cas")]
cas_manifest: std::env::current_dir()
    .ok()
    .and_then(|d| adsmt_cas::manifest::CasManifest::discover_or_env(&d))
    .map(|(_root, m)| m),
```

(`adsmtc`/`adsmtr` inherit it for free if they build their `Driver` through the
same path; if they construct the manifest elsewhere, the same one-line swap to
`discover_or_env` applies.)

# Notes / points to confirm on your side

- **Relative backend paths & the `root`.** For a `verus.toml`-sourced manifest,
  `root` becomes the `verus.toml`'s dir. If any backend (Singular subprocess, the
  MathHook submodule path) resolves a *relative* path against `root`, it'll now
  resolve against the config file's location — which is the intuitive "project
  root" semantics. Our example uses an absolute Singular path, so it's moot for us;
  flagging only in case a relative-path backend cares.
- **No engine / `-V adsmt` default-path impact.** This is entirely inside the
  `cas`-feature `Driver` construction. With the `cas` feature off, `from_manifest_file`
  isn't even compiled; the env var is silently ignored. The verus verdict path is
  untouched — same contract as the rc.41 CAS feature itself.
- **Malformed / missing file = fail-open.** `from_manifest_file` returns `None`
  (→ falls through to no CAS) on any read/parse error, matching `discover`'s
  existing `.ok()?` behaviour. A typo in `verus.toml`'s `[adsmt.cas]` can only ever
  cost you CAS delegation, never a wrong verdict.

Ping me when it lands and I'll wire the end-to-end check: `verus -V adsmt` on a
`prime(7)`-shaped obligation from a dir whose only config is a `verus.toml`
`[adsmt.cas]`, expecting the CAS numtheory Pratt path to fire (and `<unset>` →
Unknown without it).

— filed by verus-fork (윤병익 / Claude Opus 4.8) / `backend-pluggable` / 2026-07-03
