# v1.0.0 doc audit

**Status**: v1.0.0-rc.2 RC2.4 — completed 2026-05-31.

## Build

`cargo doc --workspace --no-deps` **completes successfully**;
HTML output lands under `target/doc/<crate>/index.html` for
every workspace member. No build failures.

## Warnings

48 warnings total, all of category **`broken_intra_doc_links`**.
Examples:

- `Span::file` (in `adsmt-heuristic-checker-macros`) — points
  at `proc_macro::Span::file`, which is unresolved at doc
  time because `proc_macro` crate doesn't appear in the doc
  graph for proc-macro crates.
- `StepBody::Refl(t)` (in `adsmt-cert`) — bad intra-doc-link
  syntax (the `(t)` suffix breaks the resolver); should be
  `StepBody::Refl` with `t` referenced in prose.
- `oxiz_proof_emit::emit_lfsc_via_oxiz` (in `adsmt-cert`) —
  refers to a sibling crate not in the doc-link path.

## Decision

These warnings are **non-blocking for v1.0.0 stable**. They
affect doc cosmetics (clickable links between types) but not
the documentation's substantive content; every public item
still has a doc-comment, and `cargo doc` produces complete
HTML.

Tracked as a v1.0.1 patch line-item: walk every warning,
either fix the link target or rewrite the prose to drop the
brackets. The patch release can land any time without
affecting API stability.

## Re-verification

```bash
cargo doc --workspace --no-deps 2>&1 | grep -c "^warning"
# Expected: 48 at RC2.4 close. v1.0.1 target: 0.
```
