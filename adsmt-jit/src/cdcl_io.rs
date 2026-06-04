//! v0 binary serialisation for [`crate::CdclTrace`] — the
//! §3.5.G `--jit-trace-emit` / `--jit-trace-load` payload.
//!
//! The v0 format covers only the event stream + kernel handle;
//! the GF(2) signature, guard list, and checkpoint table are
//! ignored on write and reconstructed as empty on read.  Those
//! payloads need the GF2 polynomial layout which is its own
//! serialisation problem; v1 lifts the format-version when the
//! recorder has evidence to support pinning a wire shape for
//! `GF2Poly`.
//!
//! Wire layout (all multi-byte fields little-endian):
//!
//! ```text
//! magic        : "lutrace\0"             (8 bytes)
//! version      : u32                    = LUTRACE_VERSION
//! kernel_id    : u32
//! events_len   : u64
//! ── event entries ─────────────────────────────────────────
//! each: tag : u8
//!   0x01 Propagate (atom:u32 + polarity:u8 + antecedent:i64)
//!   0x02 Conflict  (lit_count:u32 + (atom:u32 polarity:u8)*
//!                   + lbd:u32)
//!   0x03 Backjump  (to_scope:u32)
//!   0x04 Decide    (atom:u32 + polarity:u8)
//!   0x05 Restart   (no payload)
//! ```

use std::io::Write;

use crate::cdcl::{CdclTrace, CdclTraceEvent, GF2Snapshot};

/// Magic bytes at the start of every `.lutrace` v0 file.
pub const LUTRACE_MAGIC: [u8; 8] = *b"lutrace\0";

/// On-disk format version for the trace file.  Bumped only on
/// breaking layout changes.
pub const LUTRACE_VERSION: u32 = 0;

/// Errors surface from the trace reader / writer.
#[derive(Debug)]
pub enum TraceIoError {
    Io(std::io::Error),
    BadMagic,
    UnsupportedVersion { found: u32, expected: u32 },
    Truncated { at: usize, need: usize },
    UnknownTag { offset: usize, byte: u8 },
}

impl std::fmt::Display for TraceIoError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TraceIoError::Io(e) => write!(f, "lutrace io: {e}"),
            TraceIoError::BadMagic => write!(f, "lutrace: bad magic"),
            TraceIoError::UnsupportedVersion { found, expected } => {
                write!(f, "lutrace: unsupported version {found} (expected {expected})")
            }
            TraceIoError::Truncated { at, need } => {
                write!(f, "lutrace: truncated at offset {at} (need {need})")
            }
            TraceIoError::UnknownTag { offset, byte } => {
                write!(f, "lutrace: unknown event tag {byte:#04x} at offset {offset}")
            }
        }
    }
}

impl std::error::Error for TraceIoError {}

impl From<std::io::Error> for TraceIoError {
    fn from(value: std::io::Error) -> Self {
        TraceIoError::Io(value)
    }
}

/// Serialise the event stream of `trace` to `out`.  Per the
/// module-doc, the `signature` / `guards` / `checkpoints` fields
/// are written as zero-length placeholders in v0 — readers
/// reconstruct them as `GF2Snapshot::empty()` / empty `Vec`s.
pub fn write_trace<W: Write>(
    out: &mut W,
    trace: &CdclTrace,
) -> Result<(), TraceIoError> {
    out.write_all(&LUTRACE_MAGIC)?;
    out.write_all(&LUTRACE_VERSION.to_le_bytes())?;
    out.write_all(&trace.kernel_id.to_le_bytes())?;
    let n: u64 = trace
        .events
        .len()
        .try_into()
        .expect("trace event count > u64 is implausible");
    out.write_all(&n.to_le_bytes())?;
    for event in &trace.events {
        match event {
            CdclTraceEvent::Propagate {
                atom,
                polarity,
                antecedent,
            } => {
                out.write_all(&[0x01u8])?;
                out.write_all(&atom.to_le_bytes())?;
                out.write_all(&[if *polarity { 1u8 } else { 0u8 }])?;
                out.write_all(&antecedent.to_le_bytes())?;
            }
            CdclTraceEvent::Conflict { learnt, lbd } => {
                out.write_all(&[0x02u8])?;
                let m: u32 = learnt
                    .len()
                    .try_into()
                    .expect("learnt clause > u32 lits is implausible");
                out.write_all(&m.to_le_bytes())?;
                for (atom, polarity) in learnt {
                    out.write_all(&atom.to_le_bytes())?;
                    out.write_all(&[if *polarity { 1u8 } else { 0u8 }])?;
                }
                out.write_all(&lbd.to_le_bytes())?;
            }
            CdclTraceEvent::Backjump { to_scope } => {
                out.write_all(&[0x03u8])?;
                out.write_all(&to_scope.to_le_bytes())?;
            }
            CdclTraceEvent::Decide { atom, polarity } => {
                out.write_all(&[0x04u8])?;
                out.write_all(&atom.to_le_bytes())?;
                out.write_all(&[if *polarity { 1u8 } else { 0u8 }])?;
            }
            CdclTraceEvent::Restart => {
                out.write_all(&[0x05u8])?;
            }
        }
    }
    Ok(())
}

/// Cursor over a borrowed byte slice — same shape as the
/// `.luart` reader's helper, but local to this module so the
/// two reader paths stay independent.
struct Cursor<'a> {
    buf: &'a [u8],
    offset: usize,
}

impl<'a> Cursor<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Self { buf, offset: 0 }
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], TraceIoError> {
        if self.buf.len() - self.offset < n {
            return Err(TraceIoError::Truncated {
                at: self.offset,
                need: n - (self.buf.len() - self.offset),
            });
        }
        let s = &self.buf[self.offset..self.offset + n];
        self.offset += n;
        Ok(s)
    }

    fn u8(&mut self) -> Result<u8, TraceIoError> {
        Ok(self.take(1)?[0])
    }

    fn u32(&mut self) -> Result<u32, TraceIoError> {
        let s = self.take(4)?;
        Ok(u32::from_le_bytes(s.try_into().unwrap()))
    }

    fn u64(&mut self) -> Result<u64, TraceIoError> {
        let s = self.take(8)?;
        Ok(u64::from_le_bytes(s.try_into().unwrap()))
    }

    fn i64(&mut self) -> Result<i64, TraceIoError> {
        let s = self.take(8)?;
        Ok(i64::from_le_bytes(s.try_into().unwrap()))
    }
}

/// Deserialise a `.lutrace` v0 file from `buf`.  The `signature`
/// / `guards` / `checkpoints` fields of the returned
/// [`CdclTrace`] are empty (the v0 format does not persist
/// them) and the dispatcher treats that as the degenerate
/// "always-pass" guard set.
pub fn read_trace(buf: &[u8]) -> Result<CdclTrace, TraceIoError> {
    let mut c = Cursor::new(buf);
    let magic = c.take(8)?;
    if magic != LUTRACE_MAGIC {
        return Err(TraceIoError::BadMagic);
    }
    let version = c.u32()?;
    if version != LUTRACE_VERSION {
        return Err(TraceIoError::UnsupportedVersion {
            found: version,
            expected: LUTRACE_VERSION,
        });
    }
    let kernel_id = c.u32()?;
    let n = c.u64()? as usize;
    let mut events = Vec::with_capacity(n);
    for _ in 0..n {
        let tag_off = c.offset;
        let tag = c.u8()?;
        let event = match tag {
            0x01 => {
                let atom = c.u32()?;
                let polarity = c.u8()? != 0;
                let antecedent = c.i64()?;
                CdclTraceEvent::Propagate {
                    atom,
                    polarity,
                    antecedent,
                }
            }
            0x02 => {
                let m = c.u32()? as usize;
                let mut learnt = Vec::with_capacity(m);
                for _ in 0..m {
                    let atom = c.u32()?;
                    let polarity = c.u8()? != 0;
                    learnt.push((atom, polarity));
                }
                let lbd = c.u32()?;
                CdclTraceEvent::Conflict { learnt, lbd }
            }
            0x03 => CdclTraceEvent::Backjump { to_scope: c.u32()? },
            0x04 => {
                let atom = c.u32()?;
                let polarity = c.u8()? != 0;
                CdclTraceEvent::Decide { atom, polarity }
            }
            0x05 => CdclTraceEvent::Restart,
            other => {
                return Err(TraceIoError::UnknownTag {
                    offset: tag_off,
                    byte: other,
                });
            }
        };
        events.push(event);
    }
    Ok(CdclTrace {
        events,
        signature: GF2Snapshot::empty(),
        checkpoints: Vec::new(),
        guards: Vec::new(),
        kernel_id,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_trace_round_trips_header_only() {
        let trace = CdclTrace::new(GF2Snapshot::empty());
        let mut buf: Vec<u8> = Vec::new();
        write_trace(&mut buf, &trace).unwrap();
        // 8 magic + 4 version + 4 kernel_id + 8 events_len.
        assert_eq!(buf.len(), 24);
        let decoded = read_trace(&buf).unwrap();
        assert_eq!(decoded.events.len(), 0);
        assert_eq!(decoded.kernel_id, 0);
    }

    #[test]
    fn five_event_vocabulary_round_trips_through_bytes() {
        let mut trace = CdclTrace::new(GF2Snapshot::empty());
        trace.events.push(CdclTraceEvent::Propagate {
            atom: 3,
            polarity: true,
            antecedent: -1,
        });
        trace.events.push(CdclTraceEvent::Conflict {
            learnt: vec![(5, true), (7, false)],
            lbd: 2,
        });
        trace.events.push(CdclTraceEvent::Backjump { to_scope: 0 });
        trace.events.push(CdclTraceEvent::Decide {
            atom: 9,
            polarity: false,
        });
        trace.events.push(CdclTraceEvent::Restart);
        trace.kernel_id = 42;
        let mut buf: Vec<u8> = Vec::new();
        write_trace(&mut buf, &trace).unwrap();
        let decoded = read_trace(&buf).unwrap();
        assert_eq!(decoded.kernel_id, 42);
        assert_eq!(decoded.events.len(), 5);
        assert_eq!(decoded.events, trace.events);
    }

    #[test]
    fn read_trace_rejects_bad_magic() {
        let buf = vec![0u8; 24];
        match read_trace(&buf) {
            Err(TraceIoError::BadMagic) => {}
            other => panic!("expected BadMagic, got {other:?}"),
        }
    }

    #[test]
    fn read_trace_rejects_unsupported_version() {
        let mut buf: Vec<u8> = Vec::new();
        buf.extend_from_slice(&LUTRACE_MAGIC);
        buf.extend_from_slice(&(LUTRACE_VERSION + 99).to_le_bytes());
        buf.extend_from_slice(&[0u8; 12]);
        match read_trace(&buf) {
            Err(TraceIoError::UnsupportedVersion { found, expected }) => {
                assert_eq!(found, LUTRACE_VERSION + 99);
                assert_eq!(expected, LUTRACE_VERSION);
            }
            other => panic!("expected UnsupportedVersion, got {other:?}"),
        }
    }
}
