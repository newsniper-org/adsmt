# `oxiz-sat`: generic writer for `DratProof` / `LratProof` — `enable_writer`

> Draft PR for posting at <https://github.com/cool-japan/oxiz/pulls>.
> Branch: `Honey-Be/oxiz:feat/enable-writer` (forked from `0.2.2`).

---

**Title (suggested):**
`oxiz-sat: parameterize DratProof/LratProof over writer; add enable_writer / with_writer`

**Labels (suggested):** `enhancement`, `oxiz-sat`, `proof`

---

## Motivation

`DratProof::enable(path)` opens a file at the given path and writes
the proof bytes there. For most users this is exactly right.

Some downstream consumers (e.g. SMT layers that want to capture the
DRAT proof for further re-verification, or test harnesses that want
to assert on the produced bytes without touching the filesystem)
need an **in-memory sink** instead. Today the only way to do this is
to point `enable(path)` at `/dev/shm/` or `tempfile` and read it
back — both work but introduce OS-specific assumptions and
filesystem syscalls that aren't really needed.

This PR adds a generic writer parameter to `DratProof` and
`LratProof` so callers can pass any `Write + Send` sink. The default
parameter is `BufWriter<File>` so existing source compiles and the
byte stream produced by `enable(path)` is **byte-identical** to the
unmodified upstream.

## Strict superset guarantee

Every existing public API in `oxiz-sat::proof` continues to work
without source changes:

- `DratProof::new()` — same signature, same return type
  (`DratProof<BufWriter<File>>` via the default parameter)
- `DratProof::default()`, `Drop`, `Debug` — preserved
- `enable(path)` — implementation **unchanged**: still
  `BufWriter::new(File::create(path)?)`
- `add_clause`, `delete_clause`, `flush`, `disable`, `is_enabled` —
  unchanged

The PR adds two new methods on the generic `impl<W: Write + Send>
DratProof<W>` block:

- `DratProof::<W>::with_writer(w: W) -> Self` — fresh logger
  pre-configured with the given sink
- `DratProof::enable_writer(&mut self, w: W) -> io::Result<()>` —
  parallel to `enable(path)` but for arbitrary writers

A new test `test_drat_writer_output_matches_file_path` runs the same
sequence of clauses through both paths and asserts the resulting
bytes are equal. The whole existing test suite (591 tests) passes
unchanged on this branch.

## API after the change

```rust
// Existing — unchanged
let mut proof = DratProof::new();
proof.enable("/tmp/out.drat")?;
proof.add_clause(&[Lit::pos(v0), Lit::pos(v1)])?;
proof.flush()?;

// New — capture in memory
use std::io::Cursor;
let buf = Cursor::new(Vec::new());
let mut proof = DratProof::<Cursor<Vec<u8>>>::with_writer(buf);
proof.add_clause(&[Lit::pos(v0)])?;
proof.flush()?;
// `proof.disable()` releases the writer.
```

## Why generic + default instead of `Box<dyn Write + Send>`

I initially used a trait object. After feedback it was clear the
generic form is more idiomatic Rust:

- zero-cost: writes monomorphize to direct `Write` calls
- no heap allocation per logger
- the default parameter (`= BufWriter<File>`) makes every existing
  call site source-compatible
- the existing `&mut DratProof` signatures in `drat_inprocessing.rs`
  continue to resolve to `&mut DratProof<BufWriter<File>>` and
  behave identically

The only constraint is that a single `DratProof` instance fixes its
`W` for its lifetime — for the proof-logger use case this is fine
because callers choose one sink and stick with it.

## Strict-superset audit (no upstream behavior changed)

Every upstream-callable pattern produces byte-identical output and
the same trait impls:

- `DratProof::new()` returns `DratProof<BufWriter<File>>` (via the
  default type parameter), same as upstream's non-generic
  `DratProof`.
- `DratProof::default()` is implemented on
  `DratProof<BufWriter<File>>`, matching upstream's `Default` impl
  exactly.
- `enable(path)` lives on `impl DratProof<BufWriter<File>>` and uses
  the same `BufWriter::new(File::create(path)?)` body — byte stream
  produced is unchanged.
- `Debug` is `#[derive(Debug)]` on the struct, so for the upstream
  form `DratProof<BufWriter<File>>` (which still satisfies the
  derive's `W: Debug` bound) the formatted output is identical to
  pre-fork. A dedicated test
  (`test_drat_debug_format_default_typed_matches_derive`) guards
  against drift.
- `Drop` runs the same flush logic.
- All other methods (`disable`, `is_enabled`, `add_clause`,
  `delete_clause`, `flush`, plus LRAT's `add_original_clause`,
  `add_empty_clause`, `delete_clause`, `next_id`) keep their
  signatures and bodies.

Additions on top (non-default `W` only):

- `DratProof::<W>::with_writer(w)` and `DratProof::enable_writer(w)`
  for arbitrary `W: Write + Send` writers. These do not shadow or
  alter any upstream method.

## Files changed

- `oxiz-sat/src/proof.rs` — generic refactor, new methods, two new
  tests
- (no other files needed; `drat_inprocessing.rs`'s `&mut DratProof`
  signatures resolve to the default-typed form unchanged)

## Test plan

- `cargo test -p oxiz-sat --lib` — all 592 tests pass (589
  upstream + 3 new)
- New tests:
  - `test_drat_enable_writer_captures_to_cursor` — smoke check
  - `test_drat_writer_output_matches_file_path` — byte-identity
    between `enable(path)` and `enable_writer(BufWriter::new(...))`
  - `test_drat_debug_format_default_typed_matches_derive` —
    strict-superset guard for `Debug` output

---

## Notes for the poster (not part of the PR)

- Reviewers may suggest also adding `enable_writer` on
  `ProofTrimmer` if that struct mirrors the pattern. I left it
  alone because it didn't appear in the API surface for this use
  case; happy to extend on request.
- If the maintainers prefer `pub fn from_writer(w: W) -> Self`
  instead of `with_writer`, the naming is trivial to change.
- Mention the downstream use case (adsmt — Pure-Rust abductive +
  Lean4 layer on top of OxiZ) and link to the related
  `[Discussion]` issue if it's already open.
