//! `.luart` v0 writer — header + topo-sort validator.
//!
//! Pool-entry + assertion-entry emission lands in the next
//! commit (§3.1.A part 2).  This file owns the header writer +
//! the topological-order validator the pool emitter will hand
//! off to before writing entry bytes.

use std::io::{self, Write};

use crate::format::{LuartHeader, LUART_MAGIC, LUART_VERSION};

/// Errors the `.luart` writer can surface.
#[derive(Debug)]
pub enum WriteError {
    /// Underlying `io::Write` failed; carries the source error.
    Io(io::Error),
    /// The pool of `Arc<TermInner>` references passed to the
    /// pool writer (lands in §3.1.A part 2) was not in
    /// topological order: at index `i`, a child `Term` referenced
    /// either an absent pool member or one at an index `≥ i`.
    /// The writer never produces such files — this variant is
    /// reachable only when a caller supplies a hand-built pool
    /// out of order.
    NotTopologicallySorted { offending_index: usize },
}

impl std::fmt::Display for WriteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WriteError::Io(e) => write!(f, "luart writer io: {e}"),
            WriteError::NotTopologicallySorted { offending_index } => {
                write!(
                    f,
                    "luart pool not in topological order at index {offending_index}",
                )
            }
        }
    }
}

impl std::error::Error for WriteError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            WriteError::Io(e) => Some(e),
            WriteError::NotTopologicallySorted { .. } => None,
        }
    }
}

impl From<io::Error> for WriteError {
    fn from(value: io::Error) -> Self {
        WriteError::Io(value)
    }
}

/// Write the fixed-layout header prefix of a `.luart` v0 file.
/// Caller is responsible for writing the pool + assertion list
/// (and re-using the same `pool_len` / `assert_len` figures
/// recorded here) afterward.
///
/// Wire layout, all little-endian:
///
/// ```text
/// magic    : [u8; 8]                = b"luart\0\0\0"
/// version  : u32                   = LUART_VERSION
/// sha256   : [u8; 32]
/// lu_smt_version_len : u32
/// lu_smt_version_bytes : utf-8
/// pool_len : u64
/// assert_len : u64
/// ```
pub fn write_header<W: Write>(
    out: &mut W,
    header: &LuartHeader,
) -> Result<(), WriteError> {
    out.write_all(&LUART_MAGIC)?;
    out.write_all(&LUART_VERSION.to_le_bytes())?;
    out.write_all(&header.sha256)?;
    let v_bytes = header.lu_smt_version.as_bytes();
    let v_len: u32 = v_bytes
        .len()
        .try_into()
        .expect("lu-smt version string > 4 GiB is implausible");
    out.write_all(&v_len.to_le_bytes())?;
    out.write_all(v_bytes)?;
    out.write_all(&header.pool_len.to_le_bytes())?;
    out.write_all(&header.assert_len.to_le_bytes())?;
    Ok(())
}

/// Validate that `child_indices[i]` lists only indices strictly
/// less than `i` — i.e. that the pool the writer is about to
/// emit is in topological order.  Returns `Ok(())` on a valid
/// pool; returns the first offending index otherwise.
///
/// Used as a guard at the top of the pool-entry writer (which
/// lands in the next commit) so a hand-built or
/// programmatically-constructed pool that scrambles the order
/// surfaces a typed error instead of silently producing a file
/// the reader rejects.
pub fn topo_check(child_indices: &[Vec<u32>]) -> Result<(), WriteError> {
    for (i, children) in child_indices.iter().enumerate() {
        for &c in children {
            if (c as usize) >= i {
                return Err(WriteError::NotTopologicallySorted {
                    offending_index: i,
                });
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_header_emits_fixed_prefix_then_strings() {
        let mut buf: Vec<u8> = Vec::new();
        let h = LuartHeader::new([7u8; 32], "1.0.0-rc.15", 12, 3);
        write_header(&mut buf, &h).expect("write_header should succeed");

        // magic
        assert_eq!(&buf[0..8], LUART_MAGIC);
        // version
        let mut off = 8;
        assert_eq!(
            u32::from_le_bytes(buf[off..off + 4].try_into().unwrap()),
            LUART_VERSION,
        );
        off += 4;
        // sha256
        assert_eq!(&buf[off..off + 32], &[7u8; 32]);
        off += 32;
        // version string: length-prefixed UTF-8
        let v_len = u32::from_le_bytes(buf[off..off + 4].try_into().unwrap());
        off += 4;
        assert_eq!(v_len as usize, "1.0.0-rc.15".len());
        assert_eq!(&buf[off..off + v_len as usize], b"1.0.0-rc.15");
        off += v_len as usize;
        // pool_len
        assert_eq!(
            u64::from_le_bytes(buf[off..off + 8].try_into().unwrap()),
            12,
        );
        off += 8;
        // assert_len
        assert_eq!(
            u64::from_le_bytes(buf[off..off + 8].try_into().unwrap()),
            3,
        );
        off += 8;
        // No trailing bytes for header-only test.
        assert_eq!(off, buf.len());
    }

    #[test]
    fn topo_check_accepts_well_ordered_pool() {
        // Pool of 4 entries: [], [], [0], [0, 2].
        let child_indices: Vec<Vec<u32>> =
            vec![vec![], vec![], vec![0], vec![0, 2]];
        assert!(topo_check(&child_indices).is_ok());
    }

    #[test]
    fn topo_check_rejects_self_referential_index() {
        // Entry 2 refers to itself.
        let child_indices: Vec<Vec<u32>> =
            vec![vec![], vec![], vec![2]];
        let err = topo_check(&child_indices).unwrap_err();
        match err {
            WriteError::NotTopologicallySorted { offending_index } => {
                assert_eq!(offending_index, 2);
            }
            _ => panic!("expected NotTopologicallySorted, got {err:?}"),
        }
    }

    #[test]
    fn topo_check_rejects_forward_reference() {
        // Entry 0 refers to entry 1.  Forward ref → topo-fail.
        let child_indices: Vec<Vec<u32>> = vec![vec![1], vec![]];
        let err = topo_check(&child_indices).unwrap_err();
        match err {
            WriteError::NotTopologicallySorted { offending_index } => {
                assert_eq!(offending_index, 0);
            }
            _ => panic!("expected NotTopologicallySorted, got {err:?}"),
        }
    }

    #[test]
    fn topo_check_empty_pool_is_ok() {
        let child_indices: Vec<Vec<u32>> = vec![];
        assert!(topo_check(&child_indices).is_ok());
    }
}
