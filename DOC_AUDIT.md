# v1.0.0 doc audit

**Status**: v1.0.0-rc.2 RC2.4 — completed 2026-05-31.

## Build

`cargo doc --workspace --no-deps` **completes successfully**;
HTML output lands under `target/doc/<crate>/index.html` for
every workspace member. No build failures.

## Warnings — initial pass (RC2.4)

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

## RC2.8 update (2026-05-31) — silenced for clean cut baseline

Per user instruction (option C — promote DOC_AUDIT v1.0.1
candidates to the v1.0.0 cut window), the 48 warnings have
been silenced at the crate level by adding three
`#![allow(...)]` attributes to each affected `lib.rs`:

```rust
#![allow(rustdoc::broken_intra_doc_links)]
#![allow(rustdoc::private_intra_doc_links)]
#![allow(rustdoc::redundant_explicit_links)]
```

Affected crates (9):
- `adsmt-abduce`
- `adsmt-cert` (added alongside the existing clippy allows)
- `adsmt-engine`
- `adsmt-heuristic-checker-macros`
- `adsmt-lints`
- `adsmt-parser`
- `adsmt-quant`
- `adsmt-theory` (added alongside the existing clippy allows)
- `logicutils-translator-to-oxiz-sat`

`cargo doc --workspace --no-deps` now produces zero
documentation warnings (the remaining `warning:` line on stderr
is the build-script status message from
`adsmt-heuristic-checker`, which is intentional progress
output, not a lint warning).

**Deep per-link fix remains a v1.0.1+ patch line item.** The
silencing only suppresses surface noise so the stable cut
baseline is clean; the underlying link-resolution issues still
warrant individual review. When the v1.0.1 link-walk lands,
each `#![allow(...)]` should be removed crate-by-crate as the
corresponding links are repaired, so the lints re-engage and
prevent regression.

## D1 update (2026-06-01) — deep link-walk completed, pulled into v1.0.0 cut

Per the 2026-05-31 v1.0.0 scope expansion (memory
`v1_0_0_scope_expansion.md` option A), the v1.0.1 deep
per-link fix has been pulled forward into the v1.0.0 cut
window.

The 9 `#![allow(rustdoc::*)]` crate-level attributes have been
**fully removed**. Every previously-silenced warning has been
fixed at source via one of:

- *Explicit path qualifier* — e.g. `[`StepId`](crate::canonical::StepId)`
  when the type lives in a sibling module and isn't in scope.
- *`Self::` prefix* — for intra-impl `[`method`]` references
  (e.g. `[`Self::candidates`]` on a sibling method of the
  same struct).
- *Plain text demotion* — for cross-crate references in crates
  that don't pin the target as a workspace dep (e.g. parser →
  cert, quant → theory in some spots), and for explicitly
  private items (`pick_vsids_atom`, `Self::repair`) where
  `--document-private-items` would be wrong to require.
- *Variant-name normalisation* — e.g. `[`StepBody::Refl(t)`]`
  → `[`StepBody::Refl`] carrying a term `t``; rustdoc rejects
  the `Refl(t)` payload syntax.
- *Redundant-link removal* — drop the explicit `(crate::…)`
  target when the label itself already resolves
  (two cases in `prover_emit/common.rs`).

Total fixes: 38 unique source-level edits across 14 files
in 9 crates.

Verification (2026-06-01):

```
$ cargo doc --workspace --no-deps 2>&1 | grep -c "^warning"
1
```

The single remaining `warning:` line is the build-script
status message from `adsmt-heuristic-checker`'s validation
of the shipped minimum heuristic table (intentional progress
output, not a lint). Every `#![warn(rustdoc::*)]` lint is
re-engaged at default level — any regression in a future
commit will surface as a build-time warning, preventing the
silenced regime from re-accreting.

## Re-verification (post-D1)

```bash
cargo doc --workspace --no-deps 2>&1 | grep -c "^warning"
# Expected: 1 (the build-script status message) at D1 close.
# Pre-D1 (RC2.8 silenced regime): 1 (same count, but with
# allow attrs masking the underlying warnings).
# Pre-RC2.8 (initial RC2.4 close): 48.
```
