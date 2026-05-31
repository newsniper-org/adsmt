# freshcheck

Decide whether a target is fresh relative to its dependencies.

## Signature

```
freshcheck [OPTIONS] TARGET [DEPENDENCY...]
```

## Options

| Flag | Type | Default | Notes |
| ---- | ---- | ------- | ----- |
| `--method=`         | repeatable enum | `timestamp` | `timestamp\|hash\|checksum\|size\|always` |
| `--hash-algo=`      | enum  | `blake3` | `blake3\|sha3` |
| `--checksum-algo=`  | enum  | `crc32`  | `crc32` (Tier 1), `crc64` (feature `crc64`), `crc128` (feature `crc128`) |
| `--combine=`        | enum  | `all`    | `any\|all` |
| `--store=`          | path  | `.lu-store/` | |
| `--protocol-version`| flag  | —        | prints `0.1.0` |

## Decision algorithm

1. If `TARGET` does not exist → stale.
2. For each `--method`:
   - `timestamp`: stale if any dep mtime > target mtime.
   - `hash` / `checksum` / `size`: compare current signature against the
     value recorded in the store. Stale if the recorded value is missing
     or differs.
   - `always`: stale unconditionally.
3. Combine per `--combine`:
   - `all` (default): stale only if *every* method says stale.
   - `any`: stale if *any* method says stale.

## Exit codes

- 0 — fresh
- 1 — stale (or target missing)
- 2 — error

## Edge cases

- Zero `DEPENDENCY` arguments + non-`always` method → fresh iff target
  exists and (for hash/size) signature matches.
- A dep that does not exist is treated as "newer" (forces stale) under
  `timestamp`; under `hash` the missing dep is an error (exit 2).
- Signatures from previous runs that reference a now-removed file
  remain in the store until `stamp gc` removes them.
