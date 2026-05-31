# lu-deps

Read, transform, and analyse dependency graphs.

## Signature

```
lu-deps [OPTIONS] [INPUT]
```

`INPUT` is read from stdin if omitted.

## Options

| Flag | Notes |
| ---- | ----- |
| `--from=makefile\|gcc\|lu-rules\|tsv` | input format |
| `--to=tsv\|csv\|dot\|json\|toml\|taskfile` | output format |
| `--transitive`           | replace direct deps with transitive closure |
| `--reverse=TARGET`       | print every node that depends on TARGET |
| `--topo`                 | print a topological order; cycle → exit 1 |

## Input formats

| `--from` | Description |
| -------- | ----------- |
| `makefile` | Lines of `target: dep1 dep2 …`; comments and recipes ignored. |
| `gcc`      | Output of `gcc -M`/`-MM`; backslash-newline continuations honored. |
| `lu-rules` | Rule file format consumed by `lu-rule`. |
| `tsv`      | `target\tdep1,dep2,…` per line. |

## Output formats

| `--to` | Description |
| ------ | ----------- |
| `tsv`      | `target\tdep1,dep2,…` |
| `csv`      | Two columns: `target,dep`, one row per edge. |
| `dot`      | Graphviz digraph; node IDs are quoted. |
| `json`     | `{"nodes": […], "edges": [[t,d],…]}` |
| `toml`     | `[[edge]]` table per edge with `target` and `dep`. |
| `taskfile` | `lu-par`-compatible TSV (`ID\tDEPS\tCOMMAND` with empty `COMMAND`). |

## Exit codes

0 on success, 1 on `--topo` cycle, 2 on error.
