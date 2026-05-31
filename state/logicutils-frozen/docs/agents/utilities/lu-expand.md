# lu-expand

Cartesian-product template expander.

## Signature

```
lu-expand [OPTIONS] TEMPLATE
```

## Options

| Flag | Notes |
| ---- | ----- |
| `--var NAME=v1,v2,…`        | repeatable; literal value list |
| `--var-file NAME=PATH`      | repeatable; one value per non-empty line |
| `--filter=E`                | drop combinations where `E` is false |
| `--sep=CHAR`                | separator for `--var` lists, default `,` |
| `--format=`                 | output format |

## Iteration order

Variables advance odometer-style: the **last-declared** variable is the
fastest-moving digit. With `--var X=a,b --var Y=1,2` the output is:

```
X=a Y=1
X=a Y=2
X=b Y=1
X=b Y=2
```

## Exit codes

0 on success (including empty product if a variable has zero values),
2 on error.

## Edge cases

- Zero `--var` and `--var-file`: a single substitution with no
  variables is performed.
- Duplicate `NAME` across `--var` / `--var-file`: last declaration wins,
  diagnostic on stderr.
