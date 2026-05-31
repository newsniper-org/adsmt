# cargo publish dry-run audit

**Status**: v1.0.0-rc.2 RC2.2 — completed 2026-05-31 with
findings; **gating issue identified for v1.0.0 stable cut**.

## Findings

### Issue 1: path-only workspace deps fail publish

Most `adsmt-*` crates declare path-based workspace deps
without a `version = "..."` field:

```toml
adsmt-core = { path = "adsmt-core" }
```

`cargo publish --dry-run -p adsmt-cert` reports:

```
error: failed to verify manifest at /home/ybi/AD1/adsmt-cert/Cargo.toml
Caused by:
  all dependencies must have a version requirement specified when publishing.
```

**Fix** (lands in the v1.0.0 stable cut commit): add the
`version` field next to every `path` entry in
`[workspace.dependencies]`:

```toml
adsmt-core = { path = "adsmt-core", version = "=1.0.0" }
```

Pin exact via `=1.0.0` so the workspace stays cohesive.

### Issue 2: missing manifest metadata (warning)

`cargo publish -p adsmt-core --dry-run`:

```
warning: manifest has no documentation, homepage or repository
```

Affects every workspace member's `[package]` section.
Non-blocking but recommended before v1.0.0 cut so crates.io
display pages have useful links.

**Fix**: add to root `[workspace.package]`:

```toml
repository = "https://github.com/newsniper-org/adsmt"
documentation = "https://docs.rs/adsmt-meta"
homepage = "https://github.com/newsniper-org/adsmt"
```

Then each member inherits via `repository.workspace = true`
etc.

### Sample results

- `cargo publish -p adsmt-core --dry-run --allow-dirty`:
  ✅ packaged 11 files (52.5 KiB) + 1 cosmetic warning.
- `cargo publish -p adsmt-cert --dry-run --allow-dirty`:
  ❌ fails on Issue 1.
- `cargo publish -p adsmt-meta --dry-run --allow-dirty`:
  not exercised — `adsmt-meta` is *distro-only* and won't
  go to crates.io (it's a TS/distro packaging convenience,
  not a Rust dep target). Tagged as such in the metacrate
  doc comment.

## Decision

RC2.2 documents the gating issue. The actual manifest
rewrites land in the v1.0.0 stable cut commit (one
mechanical edit per workspace member + a workspace-level
metadata block); deferring is safe because the dry-run
errors don't affect the development workflow, only crates.io
publication.

## Re-verification

```bash
# After the v1.0.0 cut commit, every member must pass:
for crate in adsmt-core adsmt-cert adsmt-theory adsmt-class \
             adsmt-quant adsmt-abduce adsmt-engine adsmt-parser \
             adsmt-cli adsmt-ffi adsmt-lsp adsmt-lints \
             adsmt-heuristic-checker adsmt-heuristic-checker-macros \
             lu-common lu-match lu-expand lu-query lu-rule \
             lu-queue lu-par lu-deps lu-multi \
             logicutils-translator-to-oxiz-sat freshcheck stamp; do
  cargo publish -p "$crate" --dry-run --allow-dirty 2>&1 \
    | grep -E "^error" && echo "FAIL: $crate" || echo "OK:   $crate"
done
```

Expected: every line "OK: <crate>" at v1.0.0 stable cut.
