//! `.luart` v0 reader — byte-slice decoder + Term-DAG
//! reconstruction.
//!
//! Counterpart to [`writer`] / [`pool`].  The decoder operates on
//! a borrowed `&[u8]` slice so the caller can mmap the artifact
//! directly (the production path lives in adsmt-cli's
//! `--aot-load`, landing in §3.1.D) and avoid the parse cost on
//! every per-query `lu-smt` invocation.
//!
//! Reconstruction relies on the hash-cons cache: rebuilding a
//! `Term::var(name, ty)` / `Term::const_(name, ty)` /
//! `Term::mk_app(f, x)` / `Term::mk_lam(var, body)` from the
//! per-entry payload routes through the same cache adsmt-core
//! installed at rc.10, so structurally-equal terms across the
//! prelude + the per-query input share one `Arc<TermInner>`
//! identity — the property §3.1.D's `Solver::with_aot_prelude`
//! relies on for `intern_external` cheap-path semantics.
//!
//! [`writer`]: crate::writer

use adsmt_core::{Kind, Term, Type, Var};

use crate::format::{LuartHeader, Tag, LUART_MAGIC, LUART_VERSION};
use crate::pool::{AssertionEntry, PoolEntry};

/// Decoded `.luart` v0 file — header + raw pool + raw
/// assertions, before any Term-DAG reconstruction.  The split
/// lets callers inspect the bake metadata (SHA-256,
/// `lu_smt_version`, counts) without paying the reconstruction
/// cost up-front.
#[derive(Clone, Debug)]
pub struct LuartFile {
    pub header: LuartHeader,
    pub pool: Vec<PoolEntry>,
    pub assertions: Vec<AssertionEntry>,
}

/// Reconstructed prelude — header passthrough + the list of
/// `(Term, Option<qid>)` pairs the bake side recorded.  This is
/// what `Solver::with_aot_prelude` (§3.1.D) hands to the engine
/// as pre-asserted facts.
#[derive(Clone, Debug)]
pub struct ReconstructedPrelude {
    pub header: LuartHeader,
    pub assertions: Vec<(Term, Option<String>)>,
}

/// Errors the reader can surface.  Distinguishes layout-level
/// corruption (wrong magic, truncated bytes) from semantic-level
/// inconsistencies (pool index out of range, type-string
/// re-parse failure).
#[derive(Debug)]
pub enum ReadError {
    /// First 8 bytes did not match `LUART_MAGIC`.
    BadMagic,
    /// `version` field disagreed with the reader's
    /// `LUART_VERSION`.  Bumped only on breaking layout changes.
    UnsupportedVersion { found: u32, expected: u32 },
    /// Slice ended before the field at `at` could be fully read.
    Truncated { at: usize, need: usize },
    /// Pool entry tag byte outside the v0 set (see `Tag`).
    UnknownTag { offset: usize, byte: u8 },
    /// Pool index in `App` / `Lam` / `Assertion` exceeded the
    /// declared `pool_len` or referenced its own slot.
    PoolIndexOutOfRange { entry_index: usize, child: u32 },
    /// `Type::to_string()` round-trip failed at reconstruction
    /// time.  Either the type-string grammar shifted (handle by
    /// extending [`parse_type`]) or the bake side wrote bytes the
    /// parser doesn't accept.
    BadTypeString { entry_index: usize, ty_str: String },
    /// `Type::fun` returned a kind error during reconstruction.
    TypeKernel {
        entry_index: usize,
        err: String,
    },
    /// UTF-8 decode failed on a length-prefixed string field.
    BadUtf8 { offset: usize },
}

impl std::fmt::Display for ReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReadError::BadMagic => write!(f, "luart: bad magic"),
            ReadError::UnsupportedVersion { found, expected } => {
                write!(f, "luart: unsupported version {found} (expected {expected})")
            }
            ReadError::Truncated { at, need } => {
                write!(f, "luart: truncated at offset {at} (need {need} more bytes)")
            }
            ReadError::UnknownTag { offset, byte } => {
                write!(f, "luart: unknown pool tag {byte:#04x} at offset {offset}")
            }
            ReadError::PoolIndexOutOfRange { entry_index, child } => write!(
                f,
                "luart: pool entry {entry_index} references out-of-range / forward index {child}",
            ),
            ReadError::BadTypeString { entry_index, ty_str } => write!(
                f,
                "luart: entry {entry_index} carries un-parseable type string {ty_str:?}",
            ),
            ReadError::TypeKernel { entry_index, err } => {
                write!(f, "luart: entry {entry_index} type kernel: {err}")
            }
            ReadError::BadUtf8 { offset } => {
                write!(f, "luart: invalid utf-8 string at offset {offset}")
            }
        }
    }
}

impl std::error::Error for ReadError {}

/// Cursor over the input byte slice.  Field accessors advance
/// `offset` and surface `ReadError::Truncated` on under-read.
struct Cursor<'a> {
    buf: &'a [u8],
    offset: usize,
}

impl<'a> Cursor<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Self { buf, offset: 0 }
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], ReadError> {
        if self.buf.len() - self.offset < n {
            return Err(ReadError::Truncated {
                at: self.offset,
                need: n - (self.buf.len() - self.offset),
            });
        }
        let s = &self.buf[self.offset..self.offset + n];
        self.offset += n;
        Ok(s)
    }

    fn u8(&mut self) -> Result<u8, ReadError> {
        Ok(self.take(1)?[0])
    }

    fn u32(&mut self) -> Result<u32, ReadError> {
        let s = self.take(4)?;
        Ok(u32::from_le_bytes(s.try_into().unwrap()))
    }

    fn u64(&mut self) -> Result<u64, ReadError> {
        let s = self.take(8)?;
        Ok(u64::from_le_bytes(s.try_into().unwrap()))
    }

    fn fixed32(&mut self) -> Result<[u8; 32], ReadError> {
        let s = self.take(32)?;
        Ok(s.try_into().unwrap())
    }

    fn fixed8(&mut self) -> Result<[u8; 8], ReadError> {
        let s = self.take(8)?;
        Ok(s.try_into().unwrap())
    }

    fn str_u32(&mut self) -> Result<String, ReadError> {
        let len = self.u32()? as usize;
        let start = self.offset;
        let s = self.take(len)?;
        std::str::from_utf8(s)
            .map(|s| s.to_string())
            .map_err(|_| ReadError::BadUtf8 { offset: start })
    }
}

/// Decode a `.luart` v0 file from `buf`.  Pure byte-level pass —
/// performs no kernel work; cross-references between pool
/// indices are validated (forward / out-of-range refs rejected)
/// but Type-string re-parsing is deferred to [`reconstruct`].
pub fn read_luart(buf: &[u8]) -> Result<LuartFile, ReadError> {
    let mut c = Cursor::new(buf);
    let magic = c.fixed8()?;
    if magic != LUART_MAGIC {
        return Err(ReadError::BadMagic);
    }
    let version = c.u32()?;
    if version != LUART_VERSION {
        return Err(ReadError::UnsupportedVersion {
            found: version,
            expected: LUART_VERSION,
        });
    }
    let sha256 = c.fixed32()?;
    let lu_smt_version = c.str_u32()?;
    let pool_len = c.u64()?;
    let assert_len = c.u64()?;

    let mut pool = Vec::with_capacity(pool_len as usize);
    for i in 0..pool_len as usize {
        let tag_off = c.offset;
        let raw = c.u8()?;
        let tag =
            Tag::from_byte(raw).ok_or(ReadError::UnknownTag { offset: tag_off, byte: raw })?;
        let entry = match tag {
            Tag::Var => {
                let name = c.str_u32()?;
                let ty_str = c.str_u32()?;
                PoolEntry::Var { name, ty_str }
            }
            Tag::Const => {
                let name = c.str_u32()?;
                let ty_str = c.str_u32()?;
                PoolEntry::Const { name, ty_str }
            }
            Tag::App => {
                let f = c.u32()?;
                let x = c.u32()?;
                if (f as usize) >= i {
                    return Err(ReadError::PoolIndexOutOfRange {
                        entry_index: i,
                        child: f,
                    });
                }
                if (x as usize) >= i {
                    return Err(ReadError::PoolIndexOutOfRange {
                        entry_index: i,
                        child: x,
                    });
                }
                PoolEntry::App { f, x }
            }
            Tag::Lam => {
                let var_name = c.str_u32()?;
                let var_ty_str = c.str_u32()?;
                let body = c.u32()?;
                if (body as usize) >= i {
                    return Err(ReadError::PoolIndexOutOfRange {
                        entry_index: i,
                        child: body,
                    });
                }
                PoolEntry::Lam {
                    var_name,
                    var_ty_str,
                    body,
                }
            }
        };
        pool.push(entry);
    }

    let mut assertions = Vec::with_capacity(assert_len as usize);
    for _ in 0..assert_len as usize {
        let pool_idx = c.u32()?;
        if (pool_idx as usize) >= pool.len() {
            return Err(ReadError::PoolIndexOutOfRange {
                entry_index: pool.len(),
                child: pool_idx,
            });
        }
        let qid_present = c.u8()?;
        let qid = if qid_present == 1 {
            Some(c.str_u32()?)
        } else {
            None
        };
        assertions.push(AssertionEntry { pool_idx, qid });
    }

    Ok(LuartFile {
        header: LuartHeader {
            magic,
            version,
            sha256,
            lu_smt_version,
            pool_len,
            assert_len,
        },
        pool,
        assertions,
    })
}

/// Rebuild the canonical `Term` for every entry in `file.pool`,
/// in topological order, then return the assertion list as
/// `(Term, Option<qid>)` pairs.  Each per-entry reconstruction
/// routes through the hash-cons cache, so a pool entry that
/// duplicates an already-interned term (e.g. the `Bool` const
/// shared across many quantifier binders) settles on one
/// `Arc<TermInner>` identity.
pub fn reconstruct(file: &LuartFile) -> Result<ReconstructedPrelude, ReadError> {
    let mut interned: Vec<Term> = Vec::with_capacity(file.pool.len());
    for (i, entry) in file.pool.iter().enumerate() {
        let term = match entry {
            PoolEntry::Var { name, ty_str } => {
                let ty = parse_type(ty_str).ok_or_else(|| ReadError::BadTypeString {
                    entry_index: i,
                    ty_str: ty_str.clone(),
                })?;
                Term::var(name, ty)
            }
            PoolEntry::Const { name, ty_str } => {
                let ty = parse_type(ty_str).ok_or_else(|| ReadError::BadTypeString {
                    entry_index: i,
                    ty_str: ty_str.clone(),
                })?;
                Term::const_(name, ty)
            }
            PoolEntry::App { f, x } => {
                let fterm = interned[*f as usize].clone();
                let xterm = interned[*x as usize].clone();
                Term::app(fterm, xterm).map_err(|e| ReadError::TypeKernel {
                    entry_index: i,
                    err: format!("{e:?}"),
                })?
            }
            PoolEntry::Lam {
                var_name,
                var_ty_str,
                body,
            } => {
                let ty = parse_type(var_ty_str).ok_or_else(|| ReadError::BadTypeString {
                    entry_index: i,
                    ty_str: var_ty_str.clone(),
                })?;
                let body_t = interned[*body as usize].clone();
                Term::lam(
                    Var {
                        name: var_name.clone(),
                        ty,
                    },
                    body_t,
                )
            }
        };
        interned.push(term);
    }
    let assertions = file
        .assertions
        .iter()
        .map(|a| (interned[a.pool_idx as usize].clone(), a.qid.clone()))
        .collect();
    Ok(ReconstructedPrelude {
        header: file.header.clone(),
        assertions,
    })
}

/// Minimal inverse of `Type::Display`: parses the right-assoc
/// `A -> B`, parenthesised groups, juxtaposition for type-app,
/// and bare constructor names.  Suitable for v0; bake/load
/// fidelity is covered by the round-trip tests below.
///
/// Returns `None` on any input the grammar doesn't recognise so
/// the caller can surface a typed `ReadError::BadTypeString`.
pub fn parse_type(s: &str) -> Option<Type> {
    let trimmed = s.trim();
    let mut tokens = tokenize_type(trimmed)?;
    let ty = parse_arrow(&mut tokens)?;
    if !tokens.is_empty() {
        return None;
    }
    Some(ty)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TyTok {
    Ident(String),
    LParen,
    RParen,
    Arrow,
}

fn tokenize_type(s: &str) -> Option<Vec<TyTok>> {
    let mut out = Vec::new();
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if (b as char).is_whitespace() {
            i += 1;
            continue;
        }
        if b == b'(' {
            out.push(TyTok::LParen);
            i += 1;
            continue;
        }
        if b == b')' {
            out.push(TyTok::RParen);
            i += 1;
            continue;
        }
        if b == b'-' && i + 1 < bytes.len() && bytes[i + 1] == b'>' {
            out.push(TyTok::Arrow);
            i += 2;
            continue;
        }
        // Identifier — any contiguous run of non-space, non-paren,
        // non-arrow chars.  Matches `Bool`, `Int`, identifiers
        // with prime / sub-script chars, and unicode names; stops
        // at the first whitespace / `(` / `)` / `->`.
        let start = i;
        while i < bytes.len() {
            let c = bytes[i];
            if (c as char).is_whitespace() || c == b'(' || c == b')' {
                break;
            }
            if c == b'-' && i + 1 < bytes.len() && bytes[i + 1] == b'>' {
                break;
            }
            i += 1;
        }
        if i == start {
            return None;
        }
        out.push(TyTok::Ident(s[start..i].to_string()));
    }
    Some(out)
}

fn parse_arrow(tokens: &mut Vec<TyTok>) -> Option<Type> {
    let lhs = parse_app(tokens)?;
    if let Some(TyTok::Arrow) = tokens.first() {
        tokens.remove(0);
        let rhs = parse_arrow(tokens)?;
        return Type::fun(lhs, rhs).ok();
    }
    Some(lhs)
}

fn parse_app(tokens: &mut Vec<TyTok>) -> Option<Type> {
    let mut acc = parse_atom(tokens)?;
    while let Some(tok) = tokens.first() {
        match tok {
            TyTok::Ident(_) | TyTok::LParen => {
                let rhs = parse_atom(tokens)?;
                acc = Type::app(acc, rhs).ok()?;
            }
            _ => break,
        }
    }
    Some(acc)
}

fn parse_atom(tokens: &mut Vec<TyTok>) -> Option<Type> {
    match tokens.first()?.clone() {
        TyTok::Ident(name) => {
            tokens.remove(0);
            // v0 fidelity: every bare identifier is a Type::const_
            // of kind `Type`.  Higher-kinded constructors round-trip
            // through their juxtaposition with type arguments; the
            // resulting `Type::App` reconstructs the kind via
            // `Type::app`'s kernel check.
            Some(Type::const_(&name, Kind::Type))
        }
        TyTok::LParen => {
            tokens.remove(0);
            let inner = parse_arrow(tokens)?;
            if let Some(TyTok::RParen) = tokens.first() {
                tokens.remove(0);
                Some(inner)
            } else {
                None
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pool::{Assertion, PoolBuilder};
    use crate::writer::write_header;
    use crate::{format::LuartHeader, write_luart};

    fn bool_() -> Type {
        Type::bool_()
    }

    #[test]
    fn parse_type_round_trips_bool() {
        let t = parse_type("Bool").unwrap();
        assert_eq!(t.to_string(), "Bool");
    }

    #[test]
    fn parse_type_round_trips_arrow_right_assoc() {
        let t = parse_type("Bool -> Bool -> Bool").unwrap();
        // Display re-renders the same right-assoc form.
        assert_eq!(t.to_string(), "Bool -> Bool -> Bool");
    }

    #[test]
    fn parse_type_round_trips_parenthesised_lhs() {
        let printed = Type::fun(
            Type::fun(bool_(), bool_()).unwrap(),
            bool_(),
        )
        .unwrap()
        .to_string();
        // Display prints `(Bool -> Bool) -> Bool` for nested LHS.
        assert_eq!(printed, "(Bool -> Bool) -> Bool");
        let reparsed = parse_type(&printed).unwrap();
        assert_eq!(reparsed.to_string(), printed);
    }

    #[test]
    fn read_luart_rejects_bad_magic() {
        let buf = vec![0u8; 64];
        match read_luart(&buf) {
            Err(ReadError::BadMagic) => {}
            other => panic!("expected BadMagic, got {other:?}"),
        }
    }

    #[test]
    fn read_luart_rejects_unsupported_version() {
        let mut buf: Vec<u8> = Vec::new();
        let mut header = LuartHeader::new([0u8; 32], "1.0.0-rc.15", 0, 0);
        header.version = LUART_VERSION + 99;
        // Hand-build the prefix because write_header always uses
        // the constant version; this test simulates a future bake.
        buf.extend_from_slice(&LUART_MAGIC);
        buf.extend_from_slice(&(LUART_VERSION + 99).to_le_bytes());
        buf.extend_from_slice(&[0u8; 32]);
        let v = b"1.0.0-rc.15";
        buf.extend_from_slice(&(v.len() as u32).to_le_bytes());
        buf.extend_from_slice(v);
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        match read_luart(&buf) {
            Err(ReadError::UnsupportedVersion { found, expected }) => {
                assert_eq!(found, LUART_VERSION + 99);
                assert_eq!(expected, LUART_VERSION);
            }
            other => panic!("expected UnsupportedVersion, got {other:?}"),
        }
    }

    #[test]
    fn round_trip_single_var_assertion() {
        let p = Term::var("p", bool_());
        let assertions = vec![Assertion { term: p.clone(), qid: None }];
        let mut buf: Vec<u8> = Vec::new();
        write_luart(&mut buf, [0u8; 32], "1.0.0-rc.15", &assertions).unwrap();
        let file = read_luart(&buf).unwrap();
        assert_eq!(file.pool.len(), 1);
        assert_eq!(file.assertions.len(), 1);
        let rebuilt = reconstruct(&file).unwrap();
        let (rt, qid) = &rebuilt.assertions[0];
        assert_eq!(qid, &None);
        // Hash-cons identity: the reader's Term::var(...) lookup
        // hits the cache populated by the writer-side `p`.
        assert!(p == *rt, "reconstructed term should equal the original");
    }

    #[test]
    fn round_trip_or_with_qid() {
        let p = Term::var("p", bool_());
        let q = Term::var("q", bool_());
        let or_pq = Term::mk_or(p, q).unwrap();
        let assertions = vec![Assertion {
            term: or_pq.clone(),
            qid: Some("prelude_or".to_string()),
        }];
        let mut buf: Vec<u8> = Vec::new();
        write_luart(&mut buf, [1u8; 32], "1.0.0-rc.15", &assertions).unwrap();

        let file = read_luart(&buf).unwrap();
        assert_eq!(file.header.sha256, [1u8; 32]);
        assert_eq!(file.header.lu_smt_version, "1.0.0-rc.15");
        assert!(file.pool.len() >= 4);
        let rebuilt = reconstruct(&file).unwrap();
        let (rt, qid) = &rebuilt.assertions[0];
        assert_eq!(qid.as_deref(), Some("prelude_or"));
        assert!(or_pq == *rt);
    }

    #[test]
    fn read_luart_rejects_forward_app_reference() {
        // Hand-build a pool with an `App` referencing forward indices.
        let mut buf: Vec<u8> = Vec::new();
        let h = LuartHeader::new([0u8; 32], "1.0.0-rc.15", 1, 0);
        write_header(&mut buf, &h).unwrap();
        // Pool[0] = App(f=5, x=6) — forward refs.
        buf.push(Tag::App as u8);
        buf.extend_from_slice(&5u32.to_le_bytes());
        buf.extend_from_slice(&6u32.to_le_bytes());
        match read_luart(&buf) {
            Err(ReadError::PoolIndexOutOfRange { entry_index, child }) => {
                assert_eq!(entry_index, 0);
                assert_eq!(child, 5);
            }
            other => panic!("expected PoolIndexOutOfRange, got {other:?}"),
        }
    }
}
