//! **Number-theory backend** — the witness PRODUCER for the `Compositeness` and
//! `Primality` obligation classes, so the P1.8/P1.9 `admit` re-checkers become
//! reachable from the live engine. Pure `num-bigint` (no external CAS, no
//! subprocess, no submodule) — it just computes a divisor / a Pratt certificate.
//!
//! ## Soundness
//! UNTRUSTED like every backend. It only ever RETURNS A WITNESS; every witness is
//! re-checked by [`adsmt_cas::admit`] — the divisor by `1 < d < n ∧ n mod d = 0`,
//! the Pratt certificate by the recursive-Lucas re-check (`pratt_verifies`). A
//! producer bug (a wrong divisor, a malformed cert, an off-by-one) can therefore
//! only ever yield [`CasReply::Undecided`] or a witness that FAILS the re-check ⇒
//! `Unknown`, NEVER a wrong verdict. Trial work is bounded ([`MAX_TRIAL_BITS`]); a
//! larger `n` ⇒ `Undecided` (the sound fallback), matching `admit`'s own
//! `MAX_PRATT_NODES` fail-closed discipline.

use adsmt_cas::{
    CasBackend, CasCapability, CasClass, CasReply, Obligation, PrattCert, Witness, WitnessedDir,
};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::One;

/// The pure number-theory backend. Stateless.
#[derive(Debug, Default, Clone, Copy)]
pub struct NumTheoryBackend;

impl NumTheoryBackend {
    pub fn new() -> Self {
        NumTheoryBackend
    }
}

const CAPABILITIES: &[CasCapability] = &[
    CasCapability { class: CasClass::Compositeness, witnessed: WitnessedDir::Sat },
    CasCapability { class: CasClass::Primality, witnessed: WitnessedDir::Sat },
];

/// Bit-length cap on trial division / factorization. Beyond it we return
/// `Undecided` (√n trial steps would be too many) rather than spin — a sound
/// downgrade. Generous for the small `k` these goals carry; a real large-prime
/// path is a PARI/ECPP backend (post-1.0).
const MAX_TRIAL_BITS: u64 = 40;

/// Node budget for the recursive Pratt construction (mirrors `admit`'s
/// `MAX_PRATT_NODES`). Fail-closed: exhaustion ⇒ `None` ⇒ `Undecided`.
const MAX_PRATT_NODES: u32 = 4096;

impl CasBackend for NumTheoryBackend {
    fn name(&self) -> &'static str {
        "numtheory"
    }

    fn capabilities(&self) -> &[CasCapability] {
        CAPABILITIES
    }

    fn decide(&self, obligation: &Obligation) -> CasReply {
        match obligation {
            // A proper divisor witnesses compositeness; `admit` re-checks `1<d<n`.
            Obligation::Compositeness { n } => match find_divisor(n) {
                Some(d) => CasReply::Witnessed(Witness::Divisor(d)),
                None => CasReply::Undecided, // prime / too large ⇒ sound downgrade
            },
            // A Pratt certificate witnesses primality; `admit` re-checks it fully.
            Obligation::Primality { n } => {
                let mut budget = MAX_PRATT_NODES;
                match build_pratt(n, &mut budget) {
                    Some(cert) => CasReply::Witnessed(Witness::PrattPrime(cert)),
                    None => CasReply::Undecided, // composite / too large ⇒ downgrade
                }
            }
            _ => CasReply::Undecided,
        }
    }
}

/// A proper divisor `d` of `n` with `1 < d < n`, or `None` if `n` is prime,
/// `n < 4`, or `n` exceeds [`MAX_TRIAL_BITS`]. Trial division to `√n`.
fn find_divisor(n: &BigInt) -> Option<BigInt> {
    let two = BigInt::from(2);
    if *n < BigInt::from(4) || n.bits() > MAX_TRIAL_BITS {
        return None;
    }
    if n.is_even() {
        return Some(two);
    }
    let mut d = BigInt::from(3);
    while &d * &d <= *n {
        if n.is_multiple_of(&d) {
            return Some(d);
        }
        d += 2;
    }
    None // prime
}

/// Full prime factorization of `m ≥ 1` as `(prime, multiplicity)` pairs, by trial
/// division; `None` if `m` exceeds [`MAX_TRIAL_BITS`].
fn factorize(m: &BigInt) -> Option<Vec<(BigInt, u32)>> {
    if m.bits() > MAX_TRIAL_BITS {
        return None;
    }
    let mut m = m.clone();
    let mut out: Vec<(BigInt, u32)> = Vec::new();
    let peel = |q: &BigInt, m: &mut BigInt, out: &mut Vec<(BigInt, u32)>| {
        let mut e = 0u32;
        while m.is_multiple_of(q) {
            *m /= q;
            e += 1;
        }
        if e > 0 {
            out.push((q.clone(), e));
        }
    };
    peel(&BigInt::from(2), &mut m, &mut out);
    let mut d = BigInt::from(3);
    while &d * &d <= m {
        peel(&d, &mut m, &mut out);
        d += 2;
    }
    if m > BigInt::one() {
        out.push((m, 1)); // the remaining prime cofactor
    }
    Some(out)
}

/// Build a Pratt (recursive-Lucas) certificate proving `n` prime, or `None` if `n`
/// is composite / `< 2` / too large / the node budget is exhausted. The cert shape
/// matches `adsmt_cas`'s `pratt_verifies`: `2` is the axiomatic base (empty
/// factors), and for `n > 2` we factor `n − 1`, find a Lucas base `a`
/// (`a^(n−1) ≡ 1` and `a^((n−1)/q) ≢ 1` for every prime `q | n−1`), and recurse on
/// each `q`.
fn build_pratt(n: &BigInt, budget: &mut u32) -> Option<PrattCert> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    let two = BigInt::from(2);
    if *n == two {
        return Some(PrattCert { base: two, factors: Vec::new() });
    }
    if *n < two || n.bits() > MAX_TRIAL_BITS {
        return None;
    }
    let n_minus_1 = n - 1;
    let factors = factorize(&n_minus_1)?;
    let one = BigInt::one();
    let mut a = two;
    while &a < n {
        let is_base = a.modpow(&n_minus_1, n) == one
            && factors.iter().all(|(q, _)| a.modpow(&(&n_minus_1 / q), n) != one);
        if is_base {
            let mut sub = Vec::with_capacity(factors.len());
            for (q, e) in &factors {
                sub.push((q.clone(), *e, build_pratt(q, budget)?));
            }
            return Some(PrattCert { base: a, factors: sub });
        }
        a += 1;
    }
    None // no Lucas base in range ⇒ n is composite (or out of reach)
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_cas::{admit, Disposition, Verdict};

    fn bi(n: i64) -> BigInt {
        BigInt::from(n)
    }

    /// A produced divisor always re-checks to `Sat` (composite); a prime yields no
    /// divisor (`Undecided`).
    #[test]
    fn compositeness_witnesses_re_check() {
        let b = NumTheoryBackend::new();
        for n in [4, 6, 9, 15, 21, 100, 561] {
            let ob = Obligation::Compositeness { n: bi(n) };
            match b.decide(&ob) {
                CasReply::Witnessed(w) => {
                    assert_eq!(admit(&ob, &w), Disposition::Verdict(Verdict::Sat), "n={n}")
                }
                other => panic!("expected a divisor for composite {n}, got {other:?}"),
            }
        }
        for p in [2, 3, 5, 7, 13, 97] {
            assert!(
                matches!(b.decide(&Obligation::Compositeness { n: bi(p) }), CasReply::Undecided),
                "prime {p} must have no divisor"
            );
        }
    }

    /// A produced Pratt cert always re-checks to `Sat` (prime); a composite yields
    /// no cert (`Undecided`) — and even if it did, `admit` would reject it.
    #[test]
    fn primality_certs_re_check() {
        let b = NumTheoryBackend::new();
        for p in [2, 3, 5, 7, 11, 13, 97, 101, 7919] {
            let ob = Obligation::Primality { n: bi(p) };
            match b.decide(&ob) {
                CasReply::Witnessed(w) => {
                    assert_eq!(admit(&ob, &w), Disposition::Verdict(Verdict::Sat), "p={p}")
                }
                other => panic!("expected a Pratt cert for prime {p}, got {other:?}"),
            }
        }
        for c in [4, 9, 15, 21, 341, 561] {
            assert!(
                matches!(b.decide(&Obligation::Primality { n: bi(c) }), CasReply::Undecided),
                "composite {c} must produce no Pratt cert"
            );
        }
    }
}
