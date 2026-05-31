# contributions/ + ~/adsmt-contrib/ audit

**Status**: v1.0.0-rc.2 RC2.7 — clean 2026-05-31, per
user instruction (audit must cover the out-of-tree
contributions too, not just the in-tree workspace).

## Scope

| Location | Crates | Result |
|---|---|---|
| `contributions/oxiz/abduction/` | `oxiz-contrib-abduction` | ✅ builds; 14 tests pass |
| `contributions/oxiz/bindings/` | `oxiz-binding-lean4`, `oxiz-binding-lean4-contrib-abduction` | ✅ builds; 9 tests pass |
| `~/adsmt-contrib/` | `adsmt-emit-rocq`, `adsmt-emit-isabelle` | ✅ builds; 26 tests pass (11+15) |

## Verification

```bash
# in-tree submodule contributions
cd contributions/oxiz/abduction && cargo test
cd contributions/oxiz/bindings && cargo test

# out-of-tree adsmt-contrib workspace
cd ~/adsmt-contrib && cargo test
```

All three locations build clean against the v1.0.0-rc.2
adsmt workspace via path / `[patch.crates-io]` deps. No
manifest drift surfaced from the logicutils absorption
(RC1.4.A) — every consumer of `lu-common` or `adsmt-cert`
resolves through the absorbed workspace path correctly.

## Status check against frozen-until-leo4-v1.0 policy

The `oxiz-binding-lean4` crates are frozen at v0.x per
`memory/oxiz_relationship.md` § "Deferred: ALL language
bindings until `leo4` v1.0". RC2.7's job is not to thaw
them; it's only to confirm they still *compile* against
the v1.0.0-rc.2 trunk so the freeze doesn't bit-rot.
They do.

## adsmt-contrib (out-of-tree) consistency

`~/adsmt-contrib/Cargo.toml` consumes `adsmt-cert` via the
sibling-path pattern. Confirmed compiles against the
absorbed adsmt workspace at v1.0.0-rc.2. The
`prover_emit_policy.md` lockstep rule is satisfied — both
backends share the `adsmt_cert::prover_emit::common`
anchors.

## License compatibility

- in-tree contributions: Apache-2.0 (matches OxiZ side)
- adsmt-contrib: triple BSD-2 / Apache-2 / LGPL-2.1+ (matches
  adsmt side)
- one-way upgrade paths preserved; no relicensing required
  at v1.0.0.

## Re-verification

The full audit script:

```bash
set -e
for d in contributions/oxiz/abduction contributions/oxiz/bindings; do
  (cd "$d" && cargo test --quiet)
done
(cd ~/adsmt-contrib && cargo test --quiet)
echo "contributions audit clean"
```
