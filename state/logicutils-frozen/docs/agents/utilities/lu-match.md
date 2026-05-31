# lu-match

Multi-wildcard pattern matcher with backtracking unification.

## Signature

```
lu-match [OPTIONS] PATTERN [INPUT...]
```

If no `INPUT` is given, lines are read from stdin (one input per
line). With `--glob`, `INPUT` is a directory or `.`.

## Pattern syntax

| Form | Matches |
| ---- | ------- |
| `{NAME}`           | one path segment, no `/` |
| `{NAME:segment}`   | identical to `{NAME}` |
| `{NAME:any}`       | any string, including `/` |
| anything else      | literal |

A wildcard `{NAME}` that appears more than once is a *unifier*: every
occurrence must bind to the same value.

## Options

| Flag | Notes |
| ---- | ----- |
| `--glob`        | walk filesystem under `INPUT` |
| `--template=T`  | print `T` after substitution instead of bindings |
| `--filter=E`    | accept only matches satisfying `E` |
| `--format=`     | output format |

## Output

Default `plain`: one block per match, each line `NAME=value`, blocks
separated by blank lines.

`shell`: a single line per match, fields space-separated, suitable for
`eval`. Variable values are POSIX-quoted.

## Exit codes

0 if at least one match, 1 if none, 2 on error.

## Edge cases

- Empty bindings (a `{NAME:any}` matching the empty string) are
  permitted.
- Patterns with no wildcards behave as exact-match string compare.
- `--template` may reference variables not bound by the pattern; they
  are emitted as `{NAME}` literally and the user is warned on stderr.
