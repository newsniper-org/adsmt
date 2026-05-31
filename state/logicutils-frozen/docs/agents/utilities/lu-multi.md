# lu-multi

Multicall dispatcher (busybox-style).

## Signature

```
lu-multi UTILITY [ARG…]
SYMLINK [ARG…]            # SYMLINK basename equals a utility name
```

When invoked through a symlink whose basename matches a compiled-in
utility, dispatch goes there. When invoked as `lu-multi`, the first
positional argument names the utility.

## Options

| Flag | Notes |
| ---- | ----- |
| `--list` | print one utility name per line, exit 0 |
| `--help` | usage summary |

## Bundled utilities

`freshcheck`, `stamp`, `lu-match`, `lu-expand`, `lu-query`, `lu-rule`,
`lu-queue`, `lu-par`, `lu-deps`.

## Use case

Tier-1 deployment. A single statically-linked binary reduces footprint
on embedded systems; install with the same set of symlinks that
busybox uses.

## Exit codes

Exit code of the dispatched utility, or 2 if dispatch failed.
