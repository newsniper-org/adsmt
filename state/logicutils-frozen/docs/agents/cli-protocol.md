# CLI Protocol

Every logicutils utility, including third-party reimplementations,
**must** obey the rules in this file. The protocol is versioned via
`--protocol-version` and follows semver.

Current version: **0.2.0**.

## Exit codes

| Code | Meaning |
| ---- | ------- |
| 0    | Success / true / fresh / at-least-one-solution. |
| 1    | Expected negative result (no match, stale target, no solution, queried fact missing). |
| 2    | Error (bad arguments, I/O failure, parse error, internal bug). |

Code 1 must be distinguishable from code 2 in scripts. **Never** return
2 for a logically-empty result; that is what 1 is for.

## Output streams

- `stdout` carries data only.
- `stderr` carries diagnostics, progress, and timing.
- A utility producing no data **must** still exit 0 if its operation
  succeeded; emptiness is signalled by absence of stdout, not by exit 1.

## Output formats

Selected by `--format=`:

| Token   | Description |
| ------- | ----------- |
| `plain` | Human readable; one record per block. Default. |
| `json`  | Newline-delimited JSON (JSONL). One object per record. |
| `tsv`   | Header line followed by tab-separated rows. |
| `csv`   | RFC 4180. |
| `toml`  | A document with one `[[record]]` per record. |
| `shell` | `KEY=value` lines, single-quoted; safe for `eval`. |

Encoding is UTF-8 throughout. Fields are addressed by name, not
position; reorder freely.

## Standard flags

These flags have the same meaning in every utility:

| Flag | Meaning |
| ---- | ------- |
| `--format=FORMAT`     | Output format (table above). |
| `--store=PATH`        | Content store path. Default `.lu-store/`. |
| `--protocol-version`  | Print `0.2.0` and exit 0. |
| `-h`, `--help`        | Usage and exit 0. |

## Stdin / stdout discipline

A utility that *can* read its primary input from stdin **must** do so
when no positional input is given. This makes pipeline composition the
default.

```
gcc -M main.c | lu-deps --from=gcc --to=tsv
```

## Backwards compatibility

Within a major version: only additive changes. Adding new flags,
formats, or fields is allowed. Removing or repurposing them is not.
Reordering JSON object keys is allowed; renaming them is not.

## Reference implementation vs. spec

The Rust crates in this repository are the reference implementation.
The protocol above is the spec. **When they disagree, the spec wins**;
file a bug against the implementation.
