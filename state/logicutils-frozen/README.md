# logicutils

Composable Unix-style utilities for logic-enhanced builds — multi-wildcard
patterns, content-based freshness, and a logic engine that plays nicely
with `make`, `just`, and any POSIX shell.

logicutils takes the strong ideas of [BioMake][biomake] (multi-wildcards,
content-addressed freshness, logic programming, cluster execution) and
reshapes them as a *toolkit* of small, composable commands rather than a
monolithic build system. Each utility does one job well and is wired up
to the rest with pipes, exit codes, and shell substitution — the way Unix
intended.

[biomake]: https://github.com/evoldoers/biomake

## At a glance

| Utility       | Purpose                                                     |
| ------------- | ----------------------------------------------------------- |
| `freshcheck`  | Decide whether a target is up-to-date.                      |
| `stamp`       | Record/query/diff file signatures (BLAKE3, SHA3, CRC32, …). |
| `lu-match`    | Multi-wildcard pattern matching with backtracking.          |
| `lu-expand`   | Cartesian product expansion of variable domains.            |
| `lu-query`    | Logic knowledge-base query engine (KB language).            |
| `lu-rule`     | Pattern-rule selection with goal backtracking.              |
| `lu-queue`    | Submit/wait/cancel jobs on local or SLURM/SGE/PBS clusters. |
| `lu-par`      | DAG-aware parallel runner with optional transactional rollback. |
| `lu-deps`     | Read, transform, and analyse dependency graphs.             |
| `lu-multi`    | busybox-style multicall binary bundling all of the above.   |

## Quick taste

Hash-driven incremental compile:

```makefile
%.o: %.c
	@freshcheck --method=hash $@ $< || $(CC) -c $< -o $@
	@stamp record --method=hash $@
```

Multi-wildcard fan-out across samples and references:

```sh
lu-expand --var 'S=s1,s2,s3' --var 'R=hg38,mm10' --filter 'S != R' \
          'align-{S}-{R}.bam' \
| while read tgt; do
    lu-rule --rulefile=rules.txt --dry-run "$tgt"
  done
```

Logic-driven build over a knowledge base:

```sh
lu-query --kb project.kb --all 'stale(T)'
```

## Build

Requires Rust 2024 edition (`rustc` ≥ 1.85).

```sh
cargo build --workspace --release
cargo test  --workspace
```

A Tier-1 (resource-constrained) build drops cryptographic hashing and
cluster engines:

```sh
cargo build --workspace --release --no-default-features
```

## CLI standard

logicutils defines a CLI protocol (`docs/agents/cli-protocol.md`) so that
alternative engines and reimplementations remain interoperable. The
crates in this repository are the *reference implementation*.

Highlights of the protocol:

- Exit codes: `0` success / `1` expected negative / `2` error.
- `stdout` is data only; diagnostics go to `stderr`.
- Output formats selectable via `--format=`: `plain`, `json`, `tsv`,
  `csv`, `toml`, `shell`.
- `--protocol-version` prints the semver of the protocol.

## Documentation

| Path | Audience |
| ---- | -------- |
| `docs/man/`             | Man pages (English).                                     |
| `docs/agents/`          | Structured Markdown reference for AI agents (English).   |
| `docs/learning/{en,ko,de,ja}/logicutils.typ` | Tutorial for first-year CS students (Typst ≥ 0.14). |

Render the tutorials with `typst compile logicutils.typ`.

## License

BSD-2-Clause. See [LICENSE](LICENSE).
