//! `.luart` v0 binary-format constants and tag enumeration.
//!
//! Both halves of the format pipeline (this crate's [`writer`]
//! and the future §3.1.C reader) consume these declarations as
//! the single source of truth.
//!
//! [`writer`]: crate::writer

/// Magic bytes at the start of every `.luart` v0 file.
/// 8 bytes, padded with `\0` so a fixed-size mmap header read
/// can sanity-check the file shape without any allocation.
pub const LUART_MAGIC: [u8; 8] = *b"luart\0\0\0";

/// On-disk format version for `.luart`.  Bumped only on
/// breaking layout changes; field additions inside an existing
/// entry shape do not require a version bump as long as the
/// reader can skip unknown trailing bytes.
pub const LUART_VERSION: u32 = 0;

/// Pool-entry tag byte.  `Tag::from_byte` round-trips the wire
/// representation so the reader can match on the typed enum.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Tag {
    /// `Term::Var(Arc<Var>)` — payload is `name + ty-string`.
    Var = 0x01,
    /// `Term::Const(Arc<Const>)` — payload is `name + ty-string`.
    Const = 0x02,
    /// `Term::App(f, x)` — payload is `f_idx:u32 + x_idx:u32`.
    App = 0x03,
    /// `Term::Lam(binder, body)` — payload is
    /// `binder-name + binder-ty-string + body_idx:u32`.
    Lam = 0x04,
}

impl Tag {
    /// Parse a wire-format tag byte back into the typed enum.
    /// Returns `None` for byte values outside the v0 set so the
    /// reader can flag a corrupt or future-version file early.
    pub fn from_byte(b: u8) -> Option<Self> {
        match b {
            0x01 => Some(Tag::Var),
            0x02 => Some(Tag::Const),
            0x03 => Some(Tag::App),
            0x04 => Some(Tag::Lam),
            _ => None,
        }
    }
}

/// Header struct mirroring the fixed-shape prefix of every
/// `.luart` v0 file.  The variable-length `lu_smt_version`
/// string sits between the fixed bytes and the variable-length
/// pool, so the writer + reader treat it as part of the header
/// even though the on-disk layout encodes it as a length-prefixed
/// field rather than a fixed offset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LuartHeader {
    /// `LUART_MAGIC` — always written verbatim.
    pub magic: [u8; 8],
    /// `LUART_VERSION` — bumped only on breaking layout changes.
    pub version: u32,
    /// SHA-256 of the original prelude text (per verus-fork ack
    /// §8.3).
    pub sha256: [u8; 32],
    /// lu-smt workspace version string at bake time (per
    /// verus-fork ack §8.2 — the cache file name encodes both
    /// hashes for cross-version invalidation).
    pub lu_smt_version: String,
    /// Number of pool entries (Term-DAG nodes) following the
    /// header.
    pub pool_len: u64,
    /// Number of assertion-list entries following the pool.
    pub assert_len: u64,
}

impl LuartHeader {
    /// Compose a fresh v0 header.  Helper for the writer hot
    /// path; readers reconstruct via field-by-field decode.
    pub fn new(
        sha256: [u8; 32],
        lu_smt_version: impl Into<String>,
        pool_len: u64,
        assert_len: u64,
    ) -> Self {
        Self {
            magic: LUART_MAGIC,
            version: LUART_VERSION,
            sha256,
            lu_smt_version: lu_smt_version.into(),
            pool_len,
            assert_len,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn magic_round_trips() {
        assert_eq!(&LUART_MAGIC, b"luart\0\0\0");
    }

    #[test]
    fn tag_from_byte_round_trips_v0_set() {
        for (tag, byte) in [
            (Tag::Var, 0x01),
            (Tag::Const, 0x02),
            (Tag::App, 0x03),
            (Tag::Lam, 0x04),
        ] {
            assert_eq!(Tag::from_byte(byte), Some(tag));
            assert_eq!(tag as u8, byte);
        }
    }

    #[test]
    fn tag_from_byte_rejects_unknown_bytes() {
        for b in [0x00u8, 0x05, 0x10, 0xff] {
            assert_eq!(Tag::from_byte(b), None);
        }
    }

    #[test]
    fn header_default_fields_match_constants() {
        let h = LuartHeader::new([0u8; 32], "1.0.0-rc.15", 0, 0);
        assert_eq!(h.magic, LUART_MAGIC);
        assert_eq!(h.version, LUART_VERSION);
        assert_eq!(h.lu_smt_version, "1.0.0-rc.15");
    }
}
