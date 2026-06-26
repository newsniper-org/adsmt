//! The **AOT-bank** — serialize a type-checked [`Env`] once, reload it later
//! and check only the query delta. The cross-hybridization AOT optimization
//! (DESIGN §8) at the IR level.
//!
//! ## Why this is an *admission journal*, not a state dump
//!
//! A bank stores the [`Env`]'s **admission journal** — the exact ordered
//! sequence of *checked-admitter inputs* ([`define`](crate::define) /
//! [`postulate`](crate::postulate) /
//! [`declare_inductive_indexed`](crate::declare_inductive_indexed) /
//! [`declare_mutual`](crate::declare_mutual)). Loading **replays that journal
//! through the very same checked admitters**, so a loaded `Env` is
//! type-checked, positivity-checked, and template-derived *identically* to the
//! original. Crucially it banks only the **inputs**, never the derived
//! recursor bookkeeping (`method_template` / `rec_positions` / `ctor_of` /
//! `group_of` …): those are re-derived by the admitters at load.
//!
//! ### Soundness (the whole point)
//!
//! Because load = re-admission, the bank adds **no trust** beyond the
//! admitters (which are themselves 후검증'd). The guarantee is the strongest
//! possible under the prime directive (`FALSE_UNSAT=0`, `FALSE_SAT=0`):
//!
//! > A loaded bank can **never** admit a declaration the running kernel would
//! > not — because the running kernel *does* admit it, on load.
//!
//! A corrupt, truncated, or *kernel-version-incompatible* journal simply fails
//! to decode or fails to re-admit, yielding a [`BankError`]; the caller then
//! **falls through to full elaboration** (`Unknown`-safe). This is why no
//! `KERNEL_RULES_VERSION` gate is needed for *soundness*: a bank produced under
//! looser rules that the current kernel would reject is rejected *on replay*; a
//! bank produced under stricter rules is still re-checked under the current
//! (looser) rules, so every loaded declaration is valid for the running kernel.
//! (The earlier "trust the serialized state + a digest" design was found
//! fatally unsound — it proved codec self-consistency, not type-correctness,
//! and trusted derived templates verbatim. This design dissolves that class
//! structurally.)
//!
//! The 128-bit [FNV-1a] `payload_digest` is a **corruption** guard (bit-rot,
//! truncation, a flipped header byte), *not* an authenticity/crypto primitive:
//! the trust posture is a non-adversarial local artifact, exactly like the SMT
//! core's `.luart` / `--aot-load`. Even a *crafted* bank is sound here, because
//! load re-checks everything.
//!
//! ### What the bank wins
//!
//! It skips surface **parse + elaboration** (the journal is ready kernel
//! terms) and yields a portable, content-addressed, re-checkable prelude
//! artifact. Load still re-runs the kernel type-checker over the prelude
//! (correctness-first; DESIGN §7). The full "type-check once, then O(query
//! delta)" win is the **deferred** JIT/NbE conversion-memo increment, which
//! DESIGN §7/§8 gate on the hash-consing port (it needs O(1) term identity);
//! it will layer onto this bank behind a content-digest guard.
//!
//! [FNV-1a]: https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function

use std::fmt;

use crate::env::{AdmissionStep, Env, IndSpec};
use crate::inductive::MutualMember;
use crate::term::{Term, TermKind, Univ};

/// Magic prefix identifying an adsmt-ir bank file (8 bytes).
const MAGIC: [u8; 8] = *b"ADIR-BNK";
/// Wire-format version of the journal encoding. Bump on any change to the
/// codec (a new `AdmissionStep` / `Term` variant, a field, a tag). A bank with
/// an unknown version is rejected (⇒ fall through), never mis-decoded.
const FORMAT_VERSION: u32 = 1;
/// A constructor input list — `(ctor name, arg telescope, idx exprs)` per
/// constructor — matching [`IndSpec::ctors`].
type CtorTriples = Vec<(String, Vec<Term>, Vec<Term>)>;

/// Recursion-depth cap for the (adversarial-input) decoder — a crafted deeply
/// nested term yields [`BankError::DepthExceeded`] instead of a stack overflow.
/// Comfortably above any real CIC term depth (which tracks surface nesting),
/// and small enough that the decoder's recursion fits a modest thread stack; a
/// legitimately deeper term simply falls through to elaboration (Unknown-safe).
const DEPTH_LIMIT: usize = 2048;

// ── digest ──────────────────────────────────────────────────────────────

/// FNV-1a, 128-bit. A small, well-specified, dependency-free **integrity**
/// hash over the canonical byte stream — adequate for accidental corruption /
/// truncation detection (not a cryptographic commitment; see the module docs).
fn fnv1a_128(bytes: &[u8]) -> u128 {
    const OFFSET: u128 = 0x6c62272e07bb014262b821756295c58d;
    const PRIME: u128 = 0x0000000001000000000000000000013b;
    let mut h = OFFSET;
    for &b in bytes {
        h ^= b as u128;
        h = h.wrapping_mul(PRIME);
    }
    h
}

// ── errors ──────────────────────────────────────────────────────────────

/// Why a bank could not be loaded (or built). **Every** variant is a *soft*
/// failure: the caller must fall through to full elaboration / re-checking, so
/// a bad bank can only ever cost work, never produce a wrong verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BankError {
    /// The leading bytes are not an adsmt-ir bank.
    BadMagic,
    /// The wire-format version is not one this build understands.
    UnsupportedFormat(u32),
    /// The byte stream ended (or a length prefix overran the buffer).
    Truncated,
    /// Extra bytes remained after the journal decoded — a malformed bank.
    TrailingBytes,
    /// The recomputed digest disagrees with the header (corruption / tamper).
    DigestMismatch,
    /// A string field was not valid UTF-8 (kernel names are byte-exact; no
    /// lossy decoding — a replacement char would change identity / collide).
    InvalidUtf8,
    /// A `u64`-encoded index/length does not fit this target's `usize`
    /// (e.g. a 64-bit-baked bank on a 32-bit loader) — rejected, never
    /// silently truncated.
    IndexOutOfRange,
    /// An unknown enum tag for the named kind.
    BadTag(&'static str, u8),
    /// The decoder hit [`DEPTH_LIMIT`] on a pathologically nested term.
    DepthExceeded,
    /// The decoded journal did not re-encode to the same bytes — a codec
    /// faithfulness failure (a *correctness*, not soundness, backstop).
    Reencode,
    /// The journal does not reproduce the source `Env` ([`bank_encode`]
    /// self-check): the `Env` used the raw, journal-less `declare` paths, so
    /// the bank would be incomplete.
    IncompleteJournal,
    /// Replaying the journal through the checked admitters rejected a step —
    /// the bank is incompatible with the current kernel (this is the **sound**
    /// fall-through: the running kernel would not admit it).
    Rejected(String),
}

impl fmt::Display for BankError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BankError::BadMagic => write!(f, "not an adsmt-ir bank (bad magic)"),
            BankError::UnsupportedFormat(v) => write!(f, "unsupported bank format version {v}"),
            BankError::Truncated => write!(f, "bank truncated / length prefix overran"),
            BankError::TrailingBytes => write!(f, "trailing bytes after the journal"),
            BankError::DigestMismatch => write!(f, "bank digest mismatch (corruption)"),
            BankError::InvalidUtf8 => write!(f, "invalid UTF-8 in a bank string"),
            BankError::IndexOutOfRange => write!(f, "an index/length does not fit usize"),
            BankError::BadTag(what, t) => write!(f, "unknown {what} tag {t}"),
            BankError::DepthExceeded => write!(f, "term nesting exceeded the decode depth limit"),
            BankError::Reencode => write!(f, "decoded journal did not re-encode identically"),
            BankError::IncompleteJournal => {
                write!(f, "journal does not reproduce the Env (raw declares were used)")
            }
            BankError::Rejected(e) => write!(f, "bank step rejected by the kernel on replay: {e}"),
        }
    }
}

impl std::error::Error for BankError {}

// ── writer ──────────────────────────────────────────────────────────────

/// A tiny append-only canonical binary writer. The encoding is *fully
/// deterministic* (fixed little-endian widths, length-prefixed everything, no
/// maps) so `encode` is a function of the value alone.
struct Writer {
    buf: Vec<u8>,
}

impl Writer {
    fn new() -> Self {
        Writer { buf: Vec::new() }
    }
    fn u8(&mut self, b: u8) {
        self.buf.push(b);
    }
    fn u32(&mut self, x: u32) {
        self.buf.extend_from_slice(&x.to_le_bytes());
    }
    fn u64(&mut self, x: u64) {
        self.buf.extend_from_slice(&x.to_le_bytes());
    }
    fn usize(&mut self, x: usize) {
        self.u64(x as u64);
    }
    fn str(&mut self, s: &str) {
        self.usize(s.len());
        self.buf.extend_from_slice(s.as_bytes());
    }
    fn univ(&mut self, u: &Univ) {
        match u {
            Univ::Prop => self.u8(0),
            Univ::Type(n) => {
                self.u8(1);
                self.u32(*n);
            }
        }
    }
    fn terms(&mut self, ts: &[Term]) {
        self.usize(ts.len());
        for t in ts {
            self.term(t);
        }
    }
    fn term(&mut self, t: &Term) {
        match t.kind() {
            TermKind::Sort(u) => {
                self.u8(0);
                self.univ(u);
            }
            TermKind::Bound(k) => {
                self.u8(1);
                self.usize(*k);
            }
            TermKind::Const(c) => {
                self.u8(2);
                self.str(c);
            }
            TermKind::App(f, a) => {
                self.u8(3);
                self.term(f);
                self.term(a);
            }
            TermKind::Lam(d, b) => {
                self.u8(4);
                self.term(d);
                self.term(b);
            }
            TermKind::Pi(d, b) => {
                self.u8(5);
                self.term(d);
                self.term(b);
            }
            TermKind::Let(ty, v, b) => {
                self.u8(6);
                self.term(ty);
                self.term(v);
                self.term(b);
            }
            TermKind::Elim(ind, m, minors, major) => {
                self.u8(7);
                self.str(ind);
                self.term(m);
                self.terms(minors);
                self.term(major);
            }
            TermKind::Match(ind, m, minors, major) => {
                self.u8(8);
                self.str(ind);
                self.term(m);
                self.terms(minors);
                self.term(major);
            }
            TermKind::Fix { rec_arg, ty, body } => {
                self.u8(9);
                self.usize(*rec_arg);
                self.term(ty);
                self.term(body);
            }
            TermKind::MutElim(member, motives, minors, major) => {
                self.u8(10);
                self.str(member);
                self.terms(motives);
                self.terms(minors);
                self.term(major);
            }
        }
    }
    fn indspec(&mut self, s: &IndSpec) {
        self.str(&s.name);
        self.terms(&s.params);
        self.terms(&s.indices);
        self.univ(&s.sort);
        self.usize(s.ctors.len());
        for (cname, args, idx) in &s.ctors {
            self.str(cname);
            self.terms(args);
            self.terms(idx);
        }
    }
    fn step(&mut self, step: &AdmissionStep) {
        match step {
            AdmissionStep::Define { name, ty, body } => {
                self.u8(0);
                self.str(name);
                self.term(ty);
                self.term(body);
            }
            AdmissionStep::Postulate { name, ty } => {
                self.u8(1);
                self.str(name);
                self.term(ty);
            }
            AdmissionStep::Inductive(s) => {
                self.u8(2);
                self.indspec(s);
            }
            AdmissionStep::Mutual(specs) => {
                self.u8(3);
                self.usize(specs.len());
                for s in specs {
                    self.indspec(s);
                }
            }
        }
    }
    fn journal(&mut self, steps: &[AdmissionStep]) {
        self.usize(steps.len());
        for s in steps {
            self.step(s);
        }
    }
}

/// Encode an admission journal to its canonical payload bytes.
fn encode_journal(steps: &[AdmissionStep]) -> Vec<u8> {
    let mut w = Writer::new();
    w.journal(steps);
    w.buf
}

// ── reader ──────────────────────────────────────────────────────────────

/// A bounds-checked, totality-respecting binary reader over **untrusted**
/// input: every read checks the buffer, every length is validated against the
/// remaining bytes, recursion is depth-bounded — a malformed bank always maps
/// to a [`BankError`], never a panic or a partial-but-trusted value (mirroring
/// `reduce.rs`'s stay-stuck-never-crash discipline for unchecked terms).
struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Reader { buf, pos: 0 }
    }
    fn remaining(&self) -> usize {
        self.buf.len() - self.pos
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8], BankError> {
        if n > self.remaining() {
            return Err(BankError::Truncated);
        }
        let s = &self.buf[self.pos..self.pos + n];
        self.pos += n;
        Ok(s)
    }
    fn u8(&mut self) -> Result<u8, BankError> {
        Ok(self.take(1)?[0])
    }
    fn u32(&mut self) -> Result<u32, BankError> {
        let b = self.take(4)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }
    fn u64(&mut self) -> Result<u64, BankError> {
        let b = self.take(8)?;
        Ok(u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]))
    }
    /// A `usize` index/length, hard-rejecting any value that does not fit the
    /// target's `usize` (no silent truncation on 32-bit / wasm32).
    fn usize(&mut self) -> Result<usize, BankError> {
        usize::try_from(self.u64()?).map_err(|_| BankError::IndexOutOfRange)
    }
    fn str(&mut self) -> Result<String, BankError> {
        let n = self.usize()?;
        let b = self.take(n)?;
        std::str::from_utf8(b).map(|s| s.to_string()).map_err(|_| BankError::InvalidUtf8)
    }
    fn univ(&mut self) -> Result<Univ, BankError> {
        match self.u8()? {
            0 => Ok(Univ::Prop),
            1 => Ok(Univ::Type(self.u32()?)),
            t => Err(BankError::BadTag("univ", t)),
        }
    }
    fn terms(&mut self, depth: usize) -> Result<Vec<Term>, BankError> {
        let n = self.usize()?;
        // cap the pre-allocation: each term is ≥1 byte, so a length above the
        // remaining-byte count can never be satisfied (the loop will Truncate).
        let mut v = Vec::with_capacity(n.min(self.remaining()));
        for _ in 0..n {
            v.push(self.term(depth)?);
        }
        Ok(v)
    }
    fn term(&mut self, depth: usize) -> Result<Term, BankError> {
        if depth >= DEPTH_LIMIT {
            return Err(BankError::DepthExceeded);
        }
        let d = depth + 1;
        Ok(match self.u8()? {
            0 => Term::sort(self.univ()?),
            1 => Term::bound(self.usize()?),
            2 => Term::cnst(self.str()?),
            3 => Term::app(self.term(d)?, self.term(d)?),
            4 => Term::lam(self.term(d)?, self.term(d)?),
            5 => Term::pi(self.term(d)?, self.term(d)?),
            6 => Term::let_(self.term(d)?, self.term(d)?, self.term(d)?),
            7 => {
                let ind = self.str()?;
                let m = self.term(d)?;
                let minors = self.terms(d)?;
                let major = self.term(d)?;
                Term::elim(ind, m, minors, major)
            }
            8 => {
                let ind = self.str()?;
                let m = self.term(d)?;
                let minors = self.terms(d)?;
                let major = self.term(d)?;
                Term::mtch(ind, m, minors, major)
            }
            9 => {
                let rec_arg = self.usize()?;
                let ty = self.term(d)?;
                let body = self.term(d)?;
                Term::fix(rec_arg, ty, body)
            }
            10 => {
                let member = self.str()?;
                let motives = self.terms(d)?;
                let minors = self.terms(d)?;
                let major = self.term(d)?;
                Term::mutelim(member, motives, minors, major)
            }
            t => return Err(BankError::BadTag("term", t)),
        })
    }
    fn ctors(&mut self) -> Result<CtorTriples, BankError> {
        let n = self.usize()?;
        let mut v = Vec::with_capacity(n.min(self.remaining()));
        for _ in 0..n {
            let cname = self.str()?;
            let args = self.terms(0)?;
            let idx = self.terms(0)?;
            v.push((cname, args, idx));
        }
        Ok(v)
    }
    fn indspec(&mut self) -> Result<IndSpec, BankError> {
        Ok(IndSpec {
            name: self.str()?,
            params: self.terms(0)?,
            indices: self.terms(0)?,
            sort: self.univ()?,
            ctors: self.ctors()?,
        })
    }
    fn step(&mut self) -> Result<AdmissionStep, BankError> {
        Ok(match self.u8()? {
            0 => AdmissionStep::Define {
                name: self.str()?,
                ty: self.term(0)?,
                body: self.term(0)?,
            },
            1 => AdmissionStep::Postulate { name: self.str()?, ty: self.term(0)? },
            2 => AdmissionStep::Inductive(self.indspec()?),
            3 => {
                let n = self.usize()?;
                let mut v = Vec::with_capacity(n.min(self.remaining()));
                for _ in 0..n {
                    v.push(self.indspec()?);
                }
                AdmissionStep::Mutual(v)
            }
            t => return Err(BankError::BadTag("step", t)),
        })
    }
    fn journal(&mut self) -> Result<Vec<AdmissionStep>, BankError> {
        let n = self.usize()?;
        let mut v = Vec::with_capacity(n.min(self.remaining()));
        for _ in 0..n {
            v.push(self.step()?);
        }
        Ok(v)
    }
}

/// Decode a payload to an admission journal, requiring it to consume *exactly*
/// the input (no trailing bytes).
fn decode_journal(payload: &[u8]) -> Result<Vec<AdmissionStep>, BankError> {
    let mut r = Reader::new(payload);
    let steps = r.journal()?;
    if r.pos != r.buf.len() {
        return Err(BankError::TrailingBytes);
    }
    Ok(steps)
}

// ── replay (the sound load) ──────────────────────────────────────────────

/// Replay an admission journal through the **checked** admitters, on a fresh
/// `Env`. Any kernel rejection becomes [`BankError::Rejected`] — the sound
/// fall-through (the running kernel would not admit the step).
fn replay(steps: &[AdmissionStep]) -> Result<Env, BankError> {
    let mut env = Env::new();
    for step in steps {
        let r = match step {
            AdmissionStep::Define { name, ty, body } => {
                crate::check::define(&mut env, name, ty.clone(), body.clone())
            }
            AdmissionStep::Postulate { name, ty } => {
                crate::check::postulate(&mut env, name, ty.clone())
            }
            AdmissionStep::Inductive(s) => crate::inductive::declare_inductive_indexed(
                &mut env,
                &s.name,
                s.params.clone(),
                s.indices.clone(),
                s.sort,
                s.ctors.clone(),
            ),
            AdmissionStep::Mutual(specs) => {
                let members = specs
                    .iter()
                    .map(|s| MutualMember {
                        name: s.name.clone(),
                        params: s.params.clone(),
                        indices: s.indices.clone(),
                        sort: s.sort,
                        ctors: s.ctors.clone(),
                    })
                    .collect();
                crate::inductive::declare_mutual(&mut env, members)
            }
        };
        r.map_err(|e| BankError::Rejected(e.to_string()))?;
    }
    Ok(env)
}

// ── public API ────────────────────────────────────────────────────────────

/// Serialize a type-checked [`Env`] to an AOT-bank.
///
/// **Self-check:** the journal is replayed on a fresh `Env` and required to
/// reproduce `env` exactly ([`Env::semantically_eq`]); this guarantees a
/// produced bank always reloads, and rejects (with
/// [`BankError::IncompleteJournal`]) an `Env` assembled via the raw,
/// journal-less `declare` paths.
pub fn bank_encode(env: &Env) -> Result<Vec<u8>, BankError> {
    let payload = encode_journal(env.journal());

    // Producer self-check: the journal must re-admit to exactly this Env.
    let replayed = replay(env.journal())?;
    if !env.semantically_eq(&replayed) {
        return Err(BankError::IncompleteJournal);
    }

    // Header: MAGIC ‖ FORMAT_VERSION ‖ payload_len ‖ digest ‖ payload.
    // The digest covers MAGIC ‖ FORMAT_VERSION ‖ payload_len ‖ payload, so a
    // flipped version/length byte is caught too.
    let mut pre = Vec::with_capacity(8 + 4 + 8);
    pre.extend_from_slice(&MAGIC);
    pre.extend_from_slice(&FORMAT_VERSION.to_le_bytes());
    pre.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    let mut digest_input = pre.clone();
    digest_input.extend_from_slice(&payload);
    let digest = fnv1a_128(&digest_input);

    let mut out = Vec::with_capacity(pre.len() + 16 + payload.len());
    out.extend_from_slice(&pre);
    out.extend_from_slice(&digest.to_le_bytes());
    out.extend_from_slice(&payload);
    Ok(out)
}

/// Load an AOT-bank: verify integrity, decode the journal, and **replay it
/// through the checked admitters**, returning the re-checked `Env`.
///
/// On *any* [`BankError`] the caller must fall through to full elaboration —
/// a bad / incompatible / corrupt bank is `Unknown`-safe, never a wrong
/// verdict (see the module docs).
pub fn bank_decode(bytes: &[u8]) -> Result<Env, BankError> {
    const HEADER: usize = 8 + 4 + 8 + 16;
    if bytes.len() < HEADER {
        return Err(BankError::Truncated);
    }
    if bytes[..8] != MAGIC {
        return Err(BankError::BadMagic);
    }
    let version = u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]);
    if version != FORMAT_VERSION {
        return Err(BankError::UnsupportedFormat(version));
    }
    let payload_len = u64::from_le_bytes([
        bytes[12], bytes[13], bytes[14], bytes[15], bytes[16], bytes[17], bytes[18], bytes[19],
    ]);
    let payload_len = usize::try_from(payload_len).map_err(|_| BankError::IndexOutOfRange)?;
    if bytes.len() != HEADER + payload_len {
        return Err(BankError::Truncated);
    }
    let stored = u128::from_le_bytes(bytes[20..36].try_into().unwrap());
    let payload = &bytes[HEADER..];

    // Integrity: recompute the digest over the header-sans-digest ‖ payload.
    let mut digest_input = Vec::with_capacity(20 + payload.len());
    digest_input.extend_from_slice(&bytes[..20]);
    digest_input.extend_from_slice(payload);
    if fnv1a_128(&digest_input) != stored {
        return Err(BankError::DigestMismatch);
    }

    let steps = decode_journal(payload)?;

    // Codec-faithfulness backstop (a *correctness*, not soundness, check):
    // the decoded journal must re-encode to the same payload.
    if encode_journal(&steps) != payload {
        return Err(BankError::Reencode);
    }

    // The sound load: re-admit every step through the checked admitters.
    replay(&steps)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Wrap an arbitrary payload into a valid (correct-magic/version/digest)
    /// bank, bypassing [`bank_encode`]'s self-check — to craft banks whose
    /// journal the kernel will *reject*, exercising the sound fall-through.
    fn wrap_payload(payload: &[u8]) -> Vec<u8> {
        let mut pre = Vec::new();
        pre.extend_from_slice(&MAGIC);
        pre.extend_from_slice(&FORMAT_VERSION.to_le_bytes());
        pre.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        let mut digest_input = pre.clone();
        digest_input.extend_from_slice(payload);
        let digest = fnv1a_128(&digest_input);
        let mut out = pre;
        out.extend_from_slice(&digest.to_le_bytes());
        out.extend_from_slice(payload);
        out
    }

    #[test]
    fn fnv_distinguishes() {
        assert_ne!(fnv1a_128(b"abc"), fnv1a_128(b"abd"));
        assert_ne!(fnv1a_128(b""), fnv1a_128(b"\0"));
        assert_eq!(fnv1a_128(b"hello"), fnv1a_128(b"hello"));
    }

    #[test]
    fn empty_env_round_trips() {
        let env = Env::new();
        let bytes = bank_encode(&env).unwrap();
        let back = bank_decode(&bytes).unwrap();
        assert!(env.semantically_eq(&back));
        assert!(back.journal().is_empty());
    }

    /// The codec faithfully round-trips a journal exercising **every** `Term`
    /// variant (incl. the easy-to-confuse `Elim`/`Match` pair and `MutElim`),
    /// both `Univ` cases, and all four `AdmissionStep` kinds — independent of
    /// type-checking (these terms need not be well-typed). The rc.34.1 lesson:
    /// cover every variant through the real codec.
    #[test]
    fn codec_covers_all_variants() {
        let every_term = Term::mutelim(
            "M",
            vec![Term::sort(Univ::Prop), Term::sort(Univ::Type(3))],
            vec![
                Term::bound(7),
                Term::fix(
                    2,
                    Term::cnst("c"),
                    Term::let_(Term::cnst("a"), Term::cnst("b"), Term::bound(0)),
                ),
            ],
            Term::app(
                Term::lam(
                    Term::pi(Term::cnst("d"), Term::bound(0)),
                    Term::elim(
                        "E",
                        Term::cnst("mot"),
                        vec![Term::mtch("Mt", Term::cnst("m2"), vec![Term::cnst("x")], Term::cnst("mj2"))],
                        Term::cnst("mj"),
                    ),
                ),
                Term::cnst("arg"),
            ),
        );
        let journal = vec![
            AdmissionStep::Define { name: "d".into(), ty: every_term.clone(), body: Term::bound(0) },
            AdmissionStep::Postulate { name: "p".into(), ty: every_term.clone() },
            AdmissionStep::Inductive(IndSpec {
                name: "I".into(),
                params: vec![Term::type_(0)],
                indices: vec![],
                sort: Univ::Type(0),
                ctors: vec![("c0".into(), vec![], vec![]), ("c1".into(), vec![every_term.clone()], vec![])],
            }),
            AdmissionStep::Mutual(vec![IndSpec {
                name: "J".into(),
                params: vec![],
                indices: vec![Term::cnst("Nat")],
                sort: Univ::Prop,
                ctors: vec![("k".into(), vec![every_term.clone()], vec![Term::bound(0)])],
            }]),
        ];
        let bytes = encode_journal(&journal);
        let back = decode_journal(&bytes).unwrap();
        assert_eq!(journal, back);
    }

    #[test]
    fn crafted_good_journal_loads() {
        let journal =
            vec![AdmissionStep::Postulate { name: "P".into(), ty: Term::sort(Univ::Type(0)) }];
        let bank = wrap_payload(&encode_journal(&journal));
        let env = bank_decode(&bank).unwrap();
        assert!(env.lookup("P").is_some());
    }

    /// A journal the running kernel would **reject** (here a `postulate` of an
    /// ill-scoped type `Bound(0)` in the empty context) yields the sound
    /// [`BankError::Rejected`] on load — never a trusted-but-unchecked `Env`.
    #[test]
    fn crafted_bad_journal_is_rejected() {
        let journal = vec![AdmissionStep::Postulate { name: "X".into(), ty: Term::bound(0) }];
        let bank = wrap_payload(&encode_journal(&journal));
        match bank_decode(&bank) {
            Err(BankError::Rejected(_)) => {}
            other => panic!("expected Rejected, got {other:?}"),
        }
    }

    /// A journal referencing an undeclared constant is also rejected on replay
    /// (the checked admitter's `UnknownConst`).
    #[test]
    fn crafted_dangling_const_is_rejected() {
        let journal = vec![AdmissionStep::Postulate {
            name: "Y".into(),
            ty: Term::cnst("DoesNotExist"),
        }];
        let bank = wrap_payload(&encode_journal(&journal));
        match bank_decode(&bank) {
            Err(BankError::Rejected(_)) => {}
            other => panic!("expected Rejected, got {other:?}"),
        }
    }

    /// Decoder totality: a wide range of malformed payloads (truncations, a
    /// bad tag, an absurd length prefix) each map to a `BankError`, never a
    /// panic, never a partial-but-trusted `Env`.
    #[test]
    fn decoder_totality_on_crafted_payloads() {
        // a real, well-formed payload to truncate.
        let journal =
            vec![AdmissionStep::Postulate { name: "P".into(), ty: Term::sort(Univ::Type(0)) }];
        let good = encode_journal(&journal);
        for cut in 0..good.len() {
            assert!(decode_journal(&good[..cut]).is_err(), "truncation at {cut} must error");
            // and wrapped (valid digest) → bank_decode must still not panic.
            let _ = bank_decode(&wrap_payload(&good[..cut]));
        }
        // bad step tag.
        assert!(matches!(decode_journal(&{
            let mut p = Vec::new();
            p.extend(&1u64.to_le_bytes()); // 1 step
            p.push(250); // unknown step tag
            p
        }), Err(BankError::BadTag("step", 250))));
        // absurd journal length (no data) → Truncated, not OOM/panic.
        assert_eq!(
            decode_journal(&u64::MAX.to_le_bytes()),
            Err(BankError::Truncated)
        );
    }

    /// A forged bank carrying a `Fix` with an out-of-range `rec_arg` must be
    /// REJECTED on load (re-admission catches it via the kernel's now-total
    /// `fix` typing), never crash the decoder. Regression for the M3-1
    /// adversarial review (a forged `Fix{rec_arg=2^34}` aborted the process).
    #[test]
    fn crafted_huge_fix_rec_arg_is_rejected() {
        let nat_spec = IndSpec {
            name: "Nat".into(),
            params: vec![],
            indices: vec![],
            sort: Univ::Type(0),
            ctors: vec![
                ("O".into(), vec![], vec![]),
                ("S".into(), vec![Term::cnst("Nat")], vec![]),
            ],
        };
        let ty = Term::arrow(Term::cnst("Nat"), Term::cnst("Nat"));
        let body = Term::lam(Term::cnst("Nat"), Term::bound(0));
        let journal = vec![
            AdmissionStep::Inductive(nat_spec),
            AdmissionStep::Define {
                name: "f".into(),
                ty: ty.clone(),
                body: Term::fix(1usize << 34, ty, body),
            },
        ];
        let bank = wrap_payload(&encode_journal(&journal));
        match bank_decode(&bank) {
            Err(BankError::Rejected(_)) => {}
            other => panic!("expected Rejected, got {other:?}"),
        }
    }

    /// A pathologically deep term yields `DepthExceeded`, not a stack overflow.
    /// Run on a large stack so the decoder's bounded recursion is exercised
    /// safely regardless of the platform's default thread-stack size.
    #[test]
    fn deep_nesting_yields_depth_error() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                // a left-nested App spine deeper than DEPTH_LIMIT, crafted as
                // bytes (encoding such a term directly would recurse too).
                let leaf = |c: u8| {
                    let mut t = vec![2u8]; // Const tag
                    t.extend(&1u64.to_le_bytes());
                    t.push(c);
                    t
                };
                let arg = leaf(b'a');
                let mut term = leaf(b'x');
                for _ in 0..(DEPTH_LIMIT + 5) {
                    let mut t = vec![3u8]; // App tag, nest on the f side
                    t.extend(&term);
                    t.extend(&arg);
                    term = t;
                }
                let mut payload = Vec::new();
                payload.extend(&1u64.to_le_bytes()); // 1 step
                payload.push(1u8); // Postulate
                payload.extend(&1u64.to_le_bytes());
                payload.push(b'P'); // name "P"
                payload.extend(&term); // ty
                assert_eq!(decode_journal(&payload), Err(BankError::DepthExceeded));
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
