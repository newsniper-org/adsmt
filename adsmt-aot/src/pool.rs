//! Pool builder + pool/assertion entry writers — the §3.1.A
//! payload-half of the `.luart` v0 format.
//!
//! [`PoolBuilder`] walks the input assertion list and produces a
//! topologically-ordered pool of `PoolEntry` records keyed by
//! `Term`'s `Arc::ptr_eq` identity (which the hash-cons cache in
//! `adsmt-core::term` already guarantees is canonical per
//! structurally-equal term).  [`write_pool_entry`] +
//! [`write_assertion`] then emit each record in the wire shape
//! the §3.1.C reader will consume.

use std::collections::HashMap;
use std::io::Write;

use adsmt_core::{Term, TermInner};

use crate::format::Tag;
use crate::writer::WriteError;

/// Decoded pool-entry record.  One variant per [`Tag`]; payload
/// shape matches the wire layout per [`write_pool_entry`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PoolEntry {
    /// `TermInner::Var(Arc<Var>)`.
    Var { name: String, ty_str: String },
    /// `TermInner::Const(Arc<Const>)`.
    Const { name: String, ty_str: String },
    /// `TermInner::App(f, x)` — both indices reference earlier
    /// pool entries.
    App { f: u32, x: u32 },
    /// `TermInner::Lam(binder, body)` — binder is inlined,
    /// `body` references an earlier pool entry.
    Lam {
        var_name: String,
        var_ty_str: String,
        body: u32,
    },
}

/// One assertion entry in the on-disk assertion list.  Carries
/// a pool index plus the optional `qid` field per verus-fork
/// ack §8.4.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssertionEntry {
    /// Index of the asserted `Term` in the pool that precedes
    /// the assertion list.
    pub pool_idx: u32,
    /// Optional `:qid` attribute lifted off the original
    /// `(! body :qid …)` annotation, when the source preserved
    /// it.  `None` for plain `(assert body)` forms.
    pub qid: Option<String>,
}

/// An assertion the caller hands to [`PoolBuilder::ingest`] —
/// the public input shape that pairs every `Term` with its
/// optional `qid`.
#[derive(Clone, Debug)]
pub struct Assertion {
    pub term: Term,
    pub qid: Option<String>,
}

/// Streaming pool builder.  Each `ingest(assertion)` call walks
/// the assertion's `Term` once (post-order), assigns a pool
/// index per fresh canonical `Arc<TermInner>` identity, and
/// returns the assertion-list record the caller will later
/// emit.
#[derive(Default)]
pub struct PoolBuilder {
    entries: Vec<PoolEntry>,
    /// Identity-keyed cache: every interned `Term`'s `Arc`
    /// pointer maps to its pool index.  Two structurally-equal
    /// `Term`s share one `Arc` thanks to the hash-cons cache, so
    /// using `Term` (whose `Hash` / `Eq` are pointer-identity
    /// post-rc.10) as the map key is the canonical-pointer test.
    by_term: HashMap<Term, u32>,
}

impl PoolBuilder {
    /// Empty pool, no entries yet.
    pub fn new() -> Self {
        Self::default()
    }

    /// Walk `term` post-order and intern every sub-term into the
    /// pool.  Returns the assigned pool index of `term`.
    pub fn intern(&mut self, term: &Term) -> u32 {
        if let Some(&idx) = self.by_term.get(term) {
            return idx;
        }
        let entry = match term.kind() {
            TermInner::Var(v) => PoolEntry::Var {
                name: v.name.clone(),
                ty_str: v.ty.to_string(),
            },
            TermInner::Const(c) => PoolEntry::Const {
                name: c.name.clone(),
                ty_str: c.ty.to_string(),
            },
            TermInner::App(f, x) => {
                let f_idx = self.intern(f);
                let x_idx = self.intern(x);
                PoolEntry::App { f: f_idx, x: x_idx }
            }
            TermInner::Lam(v, body) => {
                // Visit the body first so its index slots ahead
                // of the lam in the pool's topological order.
                let body_idx = self.intern(body);
                PoolEntry::Lam {
                    var_name: v.name.clone(),
                    var_ty_str: v.ty.to_string(),
                    body: body_idx,
                }
            }
        };
        let idx: u32 = self
            .entries
            .len()
            .try_into()
            .expect(".luart v0 pool >4 GiB entries is not supported");
        self.entries.push(entry);
        self.by_term.insert(term.clone(), idx);
        idx
    }

    /// Convenience: intern an `Assertion` and return the matching
    /// [`AssertionEntry`] record carrying the pool index + qid.
    pub fn ingest(&mut self, a: &Assertion) -> AssertionEntry {
        AssertionEntry {
            pool_idx: self.intern(&a.term),
            qid: a.qid.clone(),
        }
    }

    /// Take the accumulated pool by-value; consumes the builder.
    pub fn into_entries(self) -> Vec<PoolEntry> {
        self.entries
    }

    /// Borrow the accumulated pool without consuming.  Test
    /// helper.
    pub fn entries(&self) -> &[PoolEntry] {
        &self.entries
    }
}

/// Write a single pool entry to `out` in the wire shape:
///
/// ```text
/// tag : u8
/// payload : per-variant (see Tag for the format)
///   Var/Const : name (u32-len + utf-8) + ty-string (u32-len + utf-8)
///   App       : f_idx:u32 LE + x_idx:u32 LE
///   Lam       : var-name + var-ty-string + body_idx:u32 LE
/// ```
pub fn write_pool_entry<W: Write>(
    out: &mut W,
    entry: &PoolEntry,
) -> Result<(), WriteError> {
    match entry {
        PoolEntry::Var { name, ty_str } => {
            out.write_all(&[Tag::Var as u8])?;
            write_str(out, name)?;
            write_str(out, ty_str)?;
        }
        PoolEntry::Const { name, ty_str } => {
            out.write_all(&[Tag::Const as u8])?;
            write_str(out, name)?;
            write_str(out, ty_str)?;
        }
        PoolEntry::App { f, x } => {
            out.write_all(&[Tag::App as u8])?;
            out.write_all(&f.to_le_bytes())?;
            out.write_all(&x.to_le_bytes())?;
        }
        PoolEntry::Lam { var_name, var_ty_str, body } => {
            out.write_all(&[Tag::Lam as u8])?;
            write_str(out, var_name)?;
            write_str(out, var_ty_str)?;
            out.write_all(&body.to_le_bytes())?;
        }
    }
    Ok(())
}

/// Write a single assertion-list entry to `out`:
///
/// ```text
/// pool_idx     : u32 LE
/// qid_present  : u8 (1 if Some, 0 if None)
/// qid          : (length-prefixed utf-8) if qid_present == 1
/// ```
pub fn write_assertion<W: Write>(
    out: &mut W,
    assertion: &AssertionEntry,
) -> Result<(), WriteError> {
    out.write_all(&assertion.pool_idx.to_le_bytes())?;
    match &assertion.qid {
        None => out.write_all(&[0u8])?,
        Some(s) => {
            out.write_all(&[1u8])?;
            write_str(out, s)?;
        }
    }
    Ok(())
}

/// Length-prefixed UTF-8 string helper.  `len` is `u32 LE`.
fn write_str<W: Write>(out: &mut W, s: &str) -> Result<(), WriteError> {
    let bytes = s.as_bytes();
    let len: u32 = bytes
        .len()
        .try_into()
        .expect(".luart v0 string fields > 4 GiB are not supported");
    out.write_all(&len.to_le_bytes())?;
    out.write_all(bytes)?;
    Ok(())
}

/// Convenience top-level writer: header + pool + assertion list,
/// all in one call.  Internally uses [`PoolBuilder`] to walk
/// every assertion's `Term` and produce the topologically-ordered
/// pool.  Header `pool_len` / `assert_len` are computed from the
/// final builder state, so callers don't need to pre-count.
///
/// Per verus-fork ack §6 the cache filename encodes both
/// `sha256_of_prelude_text` and `lu_smt_version`; this writer
/// records both inside the file as well so the reader can
/// cross-check.
pub fn write_luart<W: Write>(
    out: &mut W,
    sha256: [u8; 32],
    lu_smt_version: &str,
    assertions: &[Assertion],
) -> Result<(), WriteError> {
    let mut builder = PoolBuilder::new();
    let entries: Vec<AssertionEntry> =
        assertions.iter().map(|a| builder.ingest(a)).collect();
    let pool = builder.into_entries();
    let header = crate::format::LuartHeader::new(
        sha256,
        lu_smt_version,
        pool.len() as u64,
        entries.len() as u64,
    );
    crate::writer::write_header(out, &header)?;
    for e in &pool {
        write_pool_entry(out, e)?;
    }
    for e in &entries {
        write_assertion(out, e)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Term, Type};

    fn bool_() -> Type {
        Type::bool_()
    }

    #[test]
    fn pool_builder_dedups_via_arc_identity() {
        // Two structurally-identical Bool atoms share one
        // pool index thanks to the hash-cons cache.
        let p1 = Term::var("p", bool_());
        let p2 = Term::var("p", bool_());
        let mut b = PoolBuilder::new();
        let i1 = b.intern(&p1);
        let i2 = b.intern(&p2);
        assert_eq!(i1, i2);
        assert_eq!(b.entries().len(), 1);
    }

    #[test]
    fn pool_builder_topo_orders_app_after_children() {
        let p = Term::var("p", bool_());
        let n = Term::mk_not(p.clone()).unwrap();
        let mut b = PoolBuilder::new();
        let _ = b.intern(&n);
        // Pool must contain `not`-const, `p`, and the `App(not, p)`,
        // in some topological order — App's child indices both
        // less than the App's own index.
        let entries = b.entries();
        let app_idx = entries
            .iter()
            .position(|e| matches!(e, PoolEntry::App { .. }))
            .expect("App entry must exist");
        if let PoolEntry::App { f, x } = &entries[app_idx] {
            assert!((*f as usize) < app_idx);
            assert!((*x as usize) < app_idx);
        }
    }

    #[test]
    fn write_assertion_emits_pool_idx_then_qid_marker() {
        let mut buf: Vec<u8> = Vec::new();
        let a = AssertionEntry { pool_idx: 42, qid: None };
        write_assertion(&mut buf, &a).unwrap();
        // 4 bytes pool_idx LE + 1 byte qid_present (0).
        assert_eq!(buf.len(), 5);
        assert_eq!(
            u32::from_le_bytes(buf[0..4].try_into().unwrap()),
            42,
        );
        assert_eq!(buf[4], 0u8);
    }

    #[test]
    fn write_assertion_emits_qid_when_present() {
        let mut buf: Vec<u8> = Vec::new();
        let a = AssertionEntry {
            pool_idx: 7,
            qid: Some("prelude_foo".to_string()),
        };
        write_assertion(&mut buf, &a).unwrap();
        // 4 + 1 + 4 + 11 = 20.
        assert_eq!(buf.len(), 20);
        assert_eq!(buf[4], 1u8);
        let qid_len =
            u32::from_le_bytes(buf[5..9].try_into().unwrap());
        assert_eq!(qid_len, 11);
        assert_eq!(&buf[9..20], b"prelude_foo");
    }

    #[test]
    fn write_luart_round_trips_header_and_counts() {
        // Single assertion: `p`.
        let p = Term::var("p", bool_());
        let assertions = vec![Assertion { term: p, qid: None }];
        let mut buf: Vec<u8> = Vec::new();
        write_luart(&mut buf, [0u8; 32], "1.0.0-rc.15", &assertions).unwrap();

        // Header: magic + version + sha256 + version-string +
        //   pool_len + assert_len.
        let mut off = 0;
        assert_eq!(&buf[off..off + 8], crate::format::LUART_MAGIC);
        off += 8;
        let version = u32::from_le_bytes(buf[off..off + 4].try_into().unwrap());
        assert_eq!(version, crate::format::LUART_VERSION);
        off += 4;
        assert_eq!(&buf[off..off + 32], &[0u8; 32]);
        off += 32;
        let v_len = u32::from_le_bytes(buf[off..off + 4].try_into().unwrap());
        off += 4;
        assert_eq!(&buf[off..off + v_len as usize], b"1.0.0-rc.15");
        off += v_len as usize;
        let pool_len = u64::from_le_bytes(buf[off..off + 8].try_into().unwrap());
        assert_eq!(pool_len, 1, "single Var → 1 pool entry");
        off += 8;
        let assert_len = u64::from_le_bytes(buf[off..off + 8].try_into().unwrap());
        assert_eq!(assert_len, 1);
        off += 8;

        // First pool entry: tag(Var) + name + ty-string.
        assert_eq!(buf[off], Tag::Var as u8);
        off += 1;
        let n_len = u32::from_le_bytes(buf[off..off + 4].try_into().unwrap());
        off += 4;
        assert_eq!(&buf[off..off + n_len as usize], b"p");
        off += n_len as usize;
        let t_len = u32::from_le_bytes(buf[off..off + 4].try_into().unwrap());
        off += 4;
        assert_eq!(&buf[off..off + t_len as usize], b"Bool");
        off += t_len as usize;

        // Assertion: pool_idx(0) + qid_present(0).
        let p_idx = u32::from_le_bytes(buf[off..off + 4].try_into().unwrap());
        assert_eq!(p_idx, 0);
        off += 4;
        assert_eq!(buf[off], 0u8);
        off += 1;

        assert_eq!(off, buf.len(), "no trailing bytes");
    }

    #[test]
    fn write_luart_preserves_qid_for_attributed_assertion() {
        let p = Term::var("ff_qid_p", bool_());
        let assertions = vec![Assertion {
            term: p,
            qid: Some("prelude_basic".to_string()),
        }];
        let mut buf: Vec<u8> = Vec::new();
        write_luart(&mut buf, [0u8; 32], "1.0.0-rc.15", &assertions).unwrap();
        // The qid string lives at the very tail of the file.
        assert!(
            buf.windows("prelude_basic".len())
                .any(|w| w == b"prelude_basic"),
            "qid bytes should appear verbatim in the assertion record",
        );
    }
}
