//! v1 binary serialisation for [`crate::CdclTrace`] — the
//! §3.5.G `--jit-trace-emit` / `--jit-trace-load` payload.
//!
//! v0 covered the event stream + kernel handle only; the
//! GF(2) signature, guard list, and checkpoint table were
//! reconstructed as empty on read.  v1 (§1.6) lifts the
//! format-version and persists every `CdclTrace` field
//! end-to-end so emitted traces can round-trip without
//! losing the guard / signature / checkpoint payload.
//!
//! Wire layout (all multi-byte fields little-endian):
//!
//! ```text
//! magic        : "lutrace\0"             (8 bytes)
//! version      : u32                    = LUTRACE_VERSION (1)
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
//! ── end-of-trace GF(2) signature ─────────────────────────
//! basis_len     : u64
//! each polynomial:
//!   n_vars      : u32
//!   order       : u8 (0 = Lex, 1 = Grevlex)
//!   monomials_len : u32
//!   each monomial: exponents_len:u32 + exponents:Vec<u8>
//! classes_len   : u64
//! each: name:str(u32-len utf-8) + class_id:u32
//! ── guards ───────────────────────────────────────────────
//! guards_len    : u64
//! each: tag : u8
//!   0x01 PolyInvariant (polynomial — same layout as basis entry)
//!   0x02 EquivClass    (a:str + b:str)
//!   0x03 SkeletonShape (hash:u64)
//! ── checkpoints ──────────────────────────────────────────
//! checkpoints_len : u64
//! each: at_event:u32 + signature (basis + classes layout above)
//! ```
//!
//! v0 readers fed a v1 artefact surface
//! [`TraceIoError::UnsupportedVersion`] immediately — the
//! `(LUTRACE_VERSION) version` byte mismatch catches the
//! downgrade before any payload bytes are consumed.

use std::io::Write;

use adsmt_theory_finite_field::monomial::{Monomial, MonomialOrder};
use adsmt_theory_finite_field::polynomial::Polynomial as GF2Poly;

use crate::cdcl::{CdclCheckpoint, CdclTrace, CdclTraceEvent, GF2Snapshot};
use crate::guard::JitGuard;
use crate::trace::SkeletonShape;

/// Magic bytes at the start of every `.lutrace` v0 file.
pub const LUTRACE_MAGIC: [u8; 8] = *b"lutrace\0";

/// On-disk format version for the trace file.  Bumped only on
/// breaking layout changes.  v1 (§1.6) lifted the version
/// from 0 because the wire shape now persists every
/// `CdclTrace` field (signature + guards + checkpoints).
pub const LUTRACE_VERSION: u32 = 1;

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

/// Serialise `trace` to `out` — events + GF(2) signature +
/// guard list + checkpoint table.  v1 layout per the
/// module-doc.
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
        write_event(out, event)?;
    }
    write_signature(out, &trace.signature)?;
    let g_len: u64 = trace.guards.len() as u64;
    out.write_all(&g_len.to_le_bytes())?;
    for guard in &trace.guards {
        write_guard(out, guard)?;
    }
    let cp_len: u64 = trace.checkpoints.len() as u64;
    out.write_all(&cp_len.to_le_bytes())?;
    for cp in &trace.checkpoints {
        out.write_all(&cp.at_event.to_le_bytes())?;
        write_signature(out, &cp.signature)?;
    }
    Ok(())
}

fn write_event<W: Write>(
    out: &mut W,
    event: &CdclTraceEvent,
) -> Result<(), TraceIoError> {
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
    Ok(())
}

fn write_polynomial<W: Write>(
    out: &mut W,
    poly: &GF2Poly,
) -> Result<(), TraceIoError> {
    out.write_all(&(poly.n_vars() as u32).to_le_bytes())?;
    let order_byte: u8 = match poly.order() {
        MonomialOrder::Lex => 0,
        MonomialOrder::Grevlex => 1,
    };
    out.write_all(&[order_byte])?;
    let monos = poly.terms();
    out.write_all(&(monos.len() as u32).to_le_bytes())?;
    for m in monos {
        let nv = m.n_vars();
        out.write_all(&(nv as u32).to_le_bytes())?;
        for i in 0..nv {
            out.write_all(&[m.exp(i)])?;
        }
    }
    Ok(())
}

fn write_signature<W: Write>(
    out: &mut W,
    sig: &GF2Snapshot,
) -> Result<(), TraceIoError> {
    out.write_all(&(sig.basis.len() as u64).to_le_bytes())?;
    for p in &sig.basis {
        write_polynomial(out, p)?;
    }
    out.write_all(&(sig.classes.len() as u64).to_le_bytes())?;
    for (name, id) in &sig.classes {
        write_str(out, name)?;
        out.write_all(&id.to_le_bytes())?;
    }
    Ok(())
}

fn write_guard<W: Write>(
    out: &mut W,
    guard: &JitGuard,
) -> Result<(), TraceIoError> {
    match guard {
        JitGuard::PolyInvariant(p) => {
            out.write_all(&[0x01u8])?;
            write_polynomial(out, p)?;
        }
        JitGuard::EquivClass { a, b } => {
            out.write_all(&[0x02u8])?;
            write_str(out, a)?;
            write_str(out, b)?;
        }
        JitGuard::SkeletonShape(SkeletonShape(h)) => {
            out.write_all(&[0x03u8])?;
            out.write_all(&h.to_le_bytes())?;
        }
    }
    Ok(())
}

fn write_str<W: Write>(out: &mut W, s: &str) -> Result<(), TraceIoError> {
    let bytes = s.as_bytes();
    let len: u32 = bytes
        .len()
        .try_into()
        .expect("string > u32 length is implausible");
    out.write_all(&len.to_le_bytes())?;
    out.write_all(bytes)?;
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

    fn str_u32(&mut self) -> Result<String, TraceIoError> {
        let len = self.u32()? as usize;
        let bytes = self.take(len)?;
        std::str::from_utf8(bytes)
            .map(|s| s.to_string())
            .map_err(|_| TraceIoError::Truncated {
                at: self.offset,
                need: 0,
            })
    }
}

fn read_polynomial(c: &mut Cursor<'_>) -> Result<GF2Poly, TraceIoError> {
    let n_vars = c.u32()? as usize;
    let order_byte = c.u8()?;
    let order = match order_byte {
        0 => MonomialOrder::Lex,
        1 => MonomialOrder::Grevlex,
        other => {
            return Err(TraceIoError::UnknownTag {
                offset: c.offset - 1,
                byte: other,
            })
        }
    };
    let mono_count = c.u32()? as usize;
    let mut monos: Vec<Monomial> = Vec::with_capacity(mono_count);
    for _ in 0..mono_count {
        let nv = c.u32()? as usize;
        let mut exps: Vec<u8> = Vec::with_capacity(nv);
        for _ in 0..nv {
            exps.push(c.u8()?);
        }
        if exps.is_empty() {
            monos.push(Monomial::one(0));
        } else {
            monos.push(Monomial::from_exponents(&exps));
        }
    }
    Ok(GF2Poly::from_monomials(n_vars, order, monos))
}

fn read_signature(c: &mut Cursor<'_>) -> Result<GF2Snapshot, TraceIoError> {
    let basis_len = c.u64()? as usize;
    let mut basis: Vec<GF2Poly> = Vec::with_capacity(basis_len);
    for _ in 0..basis_len {
        basis.push(read_polynomial(c)?);
    }
    let classes_len = c.u64()? as usize;
    let mut classes: Vec<(String, u32)> = Vec::with_capacity(classes_len);
    for _ in 0..classes_len {
        let name = c.str_u32()?;
        let id = c.u32()?;
        classes.push((name, id));
    }
    Ok(GF2Snapshot { basis, classes })
}

fn read_guard(c: &mut Cursor<'_>) -> Result<JitGuard, TraceIoError> {
    let tag_off = c.offset;
    let tag = c.u8()?;
    match tag {
        0x01 => {
            let p = read_polynomial(c)?;
            Ok(JitGuard::PolyInvariant(p))
        }
        0x02 => {
            let a = c.str_u32()?;
            let b = c.str_u32()?;
            Ok(JitGuard::EquivClass { a, b })
        }
        0x03 => {
            let h = c.u64()?;
            Ok(JitGuard::SkeletonShape(SkeletonShape(h)))
        }
        other => Err(TraceIoError::UnknownTag {
            offset: tag_off,
            byte: other,
        }),
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
    let signature = read_signature(&mut c)?;
    let g_len = c.u64()? as usize;
    let mut guards: Vec<JitGuard> = Vec::with_capacity(g_len);
    for _ in 0..g_len {
        guards.push(read_guard(&mut c)?);
    }
    let cp_len = c.u64()? as usize;
    let mut checkpoints: Vec<CdclCheckpoint> = Vec::with_capacity(cp_len);
    for _ in 0..cp_len {
        let at_event = c.u32()?;
        let signature = read_signature(&mut c)?;
        checkpoints.push(CdclCheckpoint {
            at_event,
            signature,
        });
    }
    Ok(CdclTrace {
        events,
        signature,
        checkpoints,
        guards,
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
        // 8 magic + 4 version + 4 kernel_id + 8 events_len
        // + 8 basis_len + 8 classes_len + 8 guards_len
        // + 8 checkpoints_len = 56 bytes.
        assert_eq!(buf.len(), 56);
        let decoded = read_trace(&buf).unwrap();
        assert_eq!(decoded.events.len(), 0);
        assert_eq!(decoded.kernel_id, 0);
        assert!(decoded.signature.basis.is_empty());
        assert!(decoded.signature.classes.is_empty());
        assert!(decoded.guards.is_empty());
        assert!(decoded.checkpoints.is_empty());
    }

    #[test]
    fn v1_trace_round_trips_signature_guards_and_checkpoints() {
        use adsmt_theory_finite_field::monomial::{Monomial, MonomialOrder};
        use adsmt_theory_finite_field::polynomial::Polynomial;
        let poly = Polynomial::from_monomials(
            2,
            MonomialOrder::Grevlex,
            vec![Monomial::from_exponents(&[1, 0])],
        );
        let signature = GF2Snapshot {
            basis: vec![poly.clone()],
            classes: vec![("a".to_string(), 1), ("b".to_string(), 1)],
        };
        let mut trace = CdclTrace::new(signature.clone());
        trace.events.push(CdclTraceEvent::Restart);
        trace.guards.push(JitGuard::PolyInvariant(poly.clone()));
        trace.guards.push(JitGuard::EquivClass {
            a: "a".to_string(),
            b: "b".to_string(),
        });
        trace.guards.push(JitGuard::SkeletonShape(SkeletonShape(0xdead_beef)));
        trace.checkpoints.push(CdclCheckpoint {
            at_event: 1,
            signature: signature.clone(),
        });
        let mut buf: Vec<u8> = Vec::new();
        write_trace(&mut buf, &trace).unwrap();
        let decoded = read_trace(&buf).unwrap();
        assert_eq!(decoded.events.len(), 1);
        assert_eq!(decoded.signature.basis.len(), 1);
        assert_eq!(decoded.signature.classes.len(), 2);
        assert_eq!(decoded.guards.len(), 3);
        assert_eq!(decoded.checkpoints.len(), 1);
        assert_eq!(decoded.checkpoints[0].at_event, 1);
        // SkeletonShape guard round-trips its u64 hash exactly.
        match &decoded.guards[2] {
            JitGuard::SkeletonShape(SkeletonShape(h)) => {
                assert_eq!(*h, 0xdead_beef);
            }
            other => panic!("expected SkeletonShape, got {other:?}"),
        }
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
