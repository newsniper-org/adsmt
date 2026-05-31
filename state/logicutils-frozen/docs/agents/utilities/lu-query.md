# lu-query

Evaluate a query against a logic knowledge base.

## Signature

```
lu-query [OPTIONS] QUERY
```

`QUERY` is a single goal of the form `pred(arg1, arg2, …)`. Arguments
may be values (atoms, strings, numbers) or variables (uppercase
identifiers).

## Options

| Flag | Notes |
| ---- | ----- |
| `--kb=FILE`           | repeatable; load KB module |
| `--fact=PRED(…)`      | repeatable; add inline ground fact |
| `--all`               | emit every solution |
| `--engine=builtin\|PATH` | delegate to external binary if path |
| `--timeout=SECONDS`   | abort after timeout |
| `--format=`           | output format |

## Output

One record per solution. Fields are the variables that appeared in the
query; values are the bindings.

## Exit codes

0 if at least one solution, 1 if none, 2 on error.

## External engine contract

When `--engine=PATH` is supplied, `lu-query` re-exec's `PATH` with the
same `--kb`, `--fact`, `--all`, and final `QUERY` arguments. The
external binary inherits the protocol (exit codes, stdout = JSONL with
`--format=json`, etc.).

## Edge cases

- A query with no variables returns either the empty record (success)
  or no records (failure).
- `not p(X)` succeeds iff `p(X)` has zero solutions for the current
  binding (negation as failure).
- Recursive rules are evaluated depth-first; runaway recursion is the
  caller's responsibility (use `--timeout`).
