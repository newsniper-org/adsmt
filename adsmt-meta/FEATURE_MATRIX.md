# adsmt-meta feature matrix audit

**Status**: v1.0.0-rc.2 RC2.1 — verified clean on 2026-05-31.

Each row below was built in isolation (i.e. on its own, not
inside `cargo build --workspace`) to confirm the feature flags
don't depend on workspace-wide leakage.

| Invocation | Result | Notes |
|---|---|---|
| `cargo build -p adsmt-meta` | ✅ pass | default = `no-cli` |
| `cargo build -p adsmt-meta --no-default-features` | ✅ pass | empty feature set; library-only |
| `cargo build -p adsmt-meta --no-default-features --features no-cli` | ✅ pass | explicit no-cli |
| `cargo build -p adsmt-meta --no-default-features --features only-cli` | ✅ pass | all 10 lu-cli binaries reachable |
| `cargo build -p adsmt-meta --no-default-features --features full` | ✅ pass | everything: library + lu-cli + adsmt extensions |

## How to re-verify

```bash
for FEATURES in "" "no-cli" "only-cli" "full"; do
  if [ -z "$FEATURES" ]; then
    cargo build -p adsmt-meta --no-default-features
  else
    cargo build -p adsmt-meta --no-default-features --features "$FEATURES"
  fi
done
```

The audit must re-pass at every cycle close until v1.0.0
stable. After v1.0.0 the safeguard moves to the 8-layer
breaking-version mechanism in `adsmt-heuristic-checker`.
