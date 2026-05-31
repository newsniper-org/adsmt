# lu-par

Dependency-aware parallel runner.

## Signature

```
lu-par [OPTIONS]
```

Tasks are read from stdin or `--taskfile`. Each non-blank,
non-`#`-prefixed line is:

```
ID<TAB>DEP1,DEP2,…<TAB>COMMAND
```

`COMMAND` is a single shell-evaluated string. An empty deps field
means "no predecessors".

## Options

| Flag | Notes |
| ---- | ----- |
| `-j N`            | worker count; default = number of logical CPUs |
| `--keep-going`    | siblings of a failed task continue |
| `--retry=N`       | retry a failed task up to N times |
| `--progress`      | emit progress to stderr |
| `--transaction[=PATH]` | all-or-nothing: snapshot `PATH` (default `.lu-store`) before the run, restore it on any failure (after retries) |
| `--taskfile=PATH` | read tasks from file instead of stdin |

## Algorithm

1. Parse all lines into a node set.
2. Validate the DAG with Kahn's algorithm; cycle → exit 2.
3. Initialize worker threads sharing an mpsc channel.
4. Push all zero-in-degree nodes onto the ready queue.
5. As each task completes, decrement the in-degree of its successors;
   newly zero-in-degree nodes are pushed to the queue.
6. On failure, behavior depends on `--keep-going` and `--retry`.

## Exit codes

0 if every task succeeded, 1 if any failed (after retries), 2 on
error.

## Edge cases

- Duplicate IDs → error.
- Reference to undeclared dep ID → error.
- `--transaction` rolls back via `stamp`; tasks that did not record
  signatures cannot be undone, so users are encouraged to wrap their
  recipes with `stamp record`.
