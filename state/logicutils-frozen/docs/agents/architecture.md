# Architecture

## Workspace

Cargo workspace, edition 2024, resolver 3. Eleven member crates plus
the multicall binary. Every utility crate has both `src/lib.rs` (logic)
and `src/main.rs` (CLI wrapper) so that the logic can be reused by
`lu-multi` and by external consumers.

```
logicutils/
├── lu-common/         # shared types, formats, store, KB AST/lexer/parser
├── freshcheck/        # freshness decision (uses lu-common::store)
├── stamp/             # signature recorder
├── lu-match/          # multi-wildcard pattern matcher
├── lu-expand/         # Cartesian product expander
├── lu-query/          # logic engine (built-in deductive solver)
├── lu-rule/           # rule selection, depends on lu-match
├── lu-queue/          # local + (gated) cluster queues
├── lu-par/            # DAG-aware parallel runner
├── lu-deps/           # dependency-graph IO and analysis
└── lu-multi/          # multicall dispatcher (busybox-style)
```

## Dependency direction

`lu-common` is the only crate that other utility crates may depend on.
Cross-utility coupling happens at the CLI layer (the user pipes
processes), not at the library layer, with two intentional exceptions:

- `lu-rule` depends on `lu-match` because rule patterns *are* match
  patterns; reproducing the parser would be worse than the coupling.
- `lu-multi` depends on every utility because it dispatches to them.

Anything else should be questioned in review.

## lu-common modules

| Module | Responsibility |
| ------ | -------------- |
| `exit` | `ExitCode` enum mapping to `std::process::ExitCode`. |
| `format` | `OutputFormat`, `Record`, `FormatWriter` — shared output. |
| `hash` | `HashAlgorithm`, `ChecksumAlgorithm`, `FreshnessMethod`. |
| `store` | `.lu-store/` on-disk nested hashtable (Ticki collision resolution). |
| `kb`   | `ast`, `lexer`, `parser` for the KB language. |

## Invariants

- `lu-common` builds with `default-features = false` (Tier 1).
- The KB parser and the logic engine are decoupled: the parser produces
  the AST defined in `lu-common::kb::ast`, and `lu-query` interprets
  that AST. Alternative engines plug in via `--engine=PATH`.
- Hashing and checksum algorithms are gated behind features; the only
  always-on algorithm is `crc32` (Tier 1).

## Test strategy

Each crate has unit tests in `src/lib.rs` covering parser/engine/format
edge cases. Integration tests across crates are deliberately deferred to
the documentation examples — they are user-visible contracts and will
break loudly if they regress.
