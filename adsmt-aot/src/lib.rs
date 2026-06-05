//! AOT prelude bank for lu-smt.
//!
//! Implements the §3.1 layer of the verus-fork engine-refactor
//! request (`.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`,
//! §3.1) — the `.luart` binary artifact that lets `vargo` /
//! `verus-cross-validate` parse Verus's prelude once at build
//! time, hash-cons it, and feed it pre-asserted into every
//! per-query `lu-smt` invocation.  The format is intentionally
//! simple at v0 so the next sub-cycles (§3.1.B → §3.1.E) can
//! layer the `lu-smt --aot-bake` CLI, the mmap-load path, and
//! the `intern_external` integration on top without rewriting
//! the format from scratch.
//!
//! ## v0 layout
//!
//! ```text
//! ┌────────────────────────────────────────────────────────────┐
//! │ magic      : "luart\0\0\0"                  (8 bytes)      │
//! │ version    : u32 LE                         (4 bytes)      │
//! │ sha256     : [u8; 32]                       (32 bytes)     │
//! │ lu_smt_ver : u32 length-prefixed UTF-8 string              │
//! │ pool_len   : u64 LE                                        │
//! │ assert_len : u64 LE                                        │
//! │ ── pool entries (topo-ordered, lower indices first) ───── │
//! │ each entry: tag (u8) + payload                             │
//! │   0x01 Var   (name + ty-string)                            │
//! │   0x02 Const (name + ty-string)                            │
//! │   0x03 App   (f_idx:u32 + x_idx:u32)                       │
//! │   0x04 Lam   (binder-name + binder-ty-string + body_idx)   │
//! │ ── assertion list ─────────────────────────────────────── │
//! │ each: pool_idx:u32 + qid_present:u8                        │
//! │       + (if present: qid_len:u32 + qid_bytes)              │
//! └────────────────────────────────────────────────────────────┘
//! ```
//!
//! Notes on the v0 choices:
//!
//! - **Types are inlined as their `Type::to_string()` rendering**
//!   in each `Var` / `Const` / `Lam` payload.  No separate type
//!   pool.  This trades a bit of redundancy for a much simpler
//!   writer + reader — v1 can introduce a type pool when the
//!   redundancy becomes measurable.
//! - **Pool indices in `App` / `Lam` reference earlier entries
//!   in the same pool** — topological order is enforced by the
//!   writer's traversal (post-order DFS over the input
//!   `Term`s).  The writer validates this invariant before
//!   committing the buffer.
//! - **`qid: Option<String>`** per axiom matches the verus-fork
//!   ack §8.4: Verus tags every prelude axiom with
//!   `(! body :qid prelude_<name>)` and surfacing the `qid` lets
//!   debug tooling cross-reference an `unknown` / abductive
//!   verdict back to a specific axiom.  Other attributes
//!   (`:pattern`, `:skolemid`, `:weight`) belong in the §3.2
//!   JIT-guard metadata, not §3.1.
//!
//! This crate ships the **writer** half at §3.1.A.  The reader
//! (`.luart` → `Arc<TermInner>` pool reconstruction) lands in
//! §3.1.C; the lu-smt `--aot-bake` CLI surface lands in
//! §3.1.B, and `Solver::with_aot_prelude(...)` in §3.1.D.

pub mod cdcl;
pub mod format;
pub mod pool;
pub mod reader;
pub mod writer;

pub use cdcl::{
    write_cdcl_section, CdclClause, CdclSection, SavedPhaseEntry,
    StalmarckEdge, TrailEntry, VsidsEntry, WatchEntry,
    LUART_CDCL_VERSION,
};
pub use format::{LuartHeader, Tag, LUART_MAGIC, LUART_VERSION};
pub use pool::{
    write_assertion, write_luart, write_pool_entry, Assertion,
    AssertionEntry, PoolBuilder, PoolEntry,
};
pub use reader::{
    intern_external, parse_type, read_luart, read_luart_with_cdcl,
    reconstruct, reconstruct_with_cdcl, LuartFile, ReadError,
    ReconstructedCdclPrelude, ReconstructedPrelude,
};
pub use writer::{topo_check, write_header, WriteError};
