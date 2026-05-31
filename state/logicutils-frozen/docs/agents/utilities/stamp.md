# stamp

Manage the on-disk content store used by `freshcheck`.

## Subcommands

```
stamp record [OPTIONS] FILE...
stamp query  [OPTIONS] FILE...
stamp diff   [OPTIONS] FILE...
stamp gc     [OPTIONS]
```

| Subcommand | Reads file? | Reads store? | Writes store? |
| ---------- | ----------- | ------------ | ------------- |
| `record`   | yes | no  | yes |
| `query`    | no  | yes | no  |
| `diff`     | yes | yes | no  |
| `gc`       | no  | yes | yes |

## Store layout

`.lu-store/` is a **nested hash table** (Ticki, *Collision Resolution
with Nested Hash Tables*). Every directory is a node; every node has at
most 256 slots indexed by `h_d(key) mod 256`. A slot's on-disk form is
exactly one of:

- `<NN>.json` — a leaf entry, or
- `<NN>/`     — a subtree directory (a deeper nested hash table).

Inserting a key that hashes into an occupied leaf with a *different*
key removes the leaf, creates a subtree at that slot, and re-inserts
both keys at depth `d+1` using a fresh hash function. Lookup walks the
same chain.

`h_d` is FNV-1a-64 seeded with the depth mixed via Knuth's golden
constant, so successive levels behave as effectively independent hash
functions.

```
.lu-store/
├── 1c.json                  # uncontested leaf at depth 0
└── 7f/                      # collision split at slot 0x7f
    ├── 03.json              # one of the colliding keys, depth 1
    └── e2.json              # the other colliding key
```

A `.lu-store/.format` marker file (containing `v2`) is written the first
time the directory is touched. The marker tells subsequent invocations
that the on-disk schema is the v0.2 nested-hashtable layout.

### Automatic migration from v0.1

If `.format` is absent and the directory contains v0.1-style entries
(`<2-hex>/<14-hex>.json`), the first read or write transparently
migrates them: each legacy leaf is re-routed through the new addressing
scheme via `insert_at(root, …, depth = 0)` and the old file is removed.
Empty legacy bucket directories are then pruned. The marker is written
last so the migration runs at most once per upgrade.

Migration also coexists correctly with stores that already contain a
mix of v0.1 leaves and v0.2 leaves (legacy: 14-hex stem; new: 2-hex
stem) sharing the same `<NN>/` directory.

Each leaf is a JSON object keyed by method name:

  ```json
  {
    "path": "src/main.c",
    "size": 1234,
    "blake3": "…",
    "crc32": "…",
    "timestamp": 1712345678
  }
  ```

Multiple methods coexist in the same file. Recording a new method
merges; recording the same method again overwrites.

## Options

| Flag | Notes |
| ---- | ----- |
| `--method=`        | repeatable; same enum as `freshcheck` |
| `--hash-algo=`     | as above |
| `--checksum-algo=` | as above |
| `--store=`         | default `.lu-store/` |
| `--format=`        | only meaningful for `query` and `diff` |

## Exit codes

- `record`, `gc`: 0 on success; 2 on error.
- `query`: 0 if every requested file has at least one signature; 1 if
  any requested file is absent from the store; 2 on error.
- `diff`: 0 if all queried files match their recorded signatures; 1 if
  any file differs; 2 on error or missing record.
