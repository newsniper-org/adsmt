# Extending logicutils

## Swap the logic engine

`lu-query --engine=PATH` re-execs `PATH` with the same flags. To
reimplement the engine:

1. Accept the documented flags (`--kb`, `--fact`, `--all`, `--format`,
   `--timeout`).
2. Honor the CLI protocol: exit codes, stdout-only data, JSONL with
   `--format=json`.
3. Parse the KB language as described in `kb-language.md`. The
   reference parser lives in `lu-common::kb` and is library-exposed —
   you may depend on it from another Rust crate.

## Add a queue backend

1. Implement the `QueueEngine` trait in `lu-queue/src/lib.rs`.
2. Map the generic flags to the backend's native invocation; see the
   table in `utilities/lu-queue.md`.
3. Gate the new backend behind a Cargo feature so Tier-1 builds stay
   slim.

## Add a hash or checksum algorithm

1. Extend the relevant enum in `lu-common::hash`.
2. Implement signature computation. Treat the algorithm as opaque
   bytes; the store records the hex form.
3. Gate behind a Cargo feature unless it is mandatory for Tier-1.
4. Update `freshcheck` and `stamp` flag enums.

## Add a new utility

1. Create a new workspace member crate `lu-<name>` with `lib.rs` and
   `main.rs`.
2. Depend only on `lu-common`. Cross-utility coupling at the library
   layer is forbidden except for documented exceptions
   (`lu-rule → lu-match`).
3. Implement the standard flags from `cli-protocol.md`.
4. Register the binary in `lu-multi/src/main.rs`.
5. Write a man page and a `utilities/<name>.md`.

## Backwards compatibility

Within `0.x` the protocol may change at minor-version boundaries with
explicit notes. From `1.0` onward the rules in `cli-protocol.md` are
binding.
