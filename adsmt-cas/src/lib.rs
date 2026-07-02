//! # adsmt-cas — the trusted CAS re-check core
//!
//! A Computer Algebra System is an **untrusted oracle**: it *finds* a witness,
//! this crate's trusted, clean-room [`admit`] *checks* it. No CAS answer moves an
//! adsmt verdict without a witness [`admit`] re-validates — in time cheaper than,
//! and independent of, the CAS's own search. Design + soundness argument:
//! `docs/design/CAS_BACKEND_INTEGRATION.md` (the `§9` adversarial-review
//! hardening governs).
//!
//! **This is P0**: the type surface + the [`admit`] re-checkers for the four
//! witness-delegated classes whose re-check is a short, self-contained
//! certificate — ideal membership (cofactor), factorization (reducible),
//! compositeness (proper divisor), existential Diophantine (int solution). The
//! backend subprocess + the typed-term classifier + the offline `adsmt-cert`
//! replay are later slices; the *trusted* half — the re-checkers — lands first,
//! because it is the entire soundness story.
//!
//! ## The re-check ring (§9-B1)
//! Every polynomial re-check runs over **ℚ** ([`poly::MPoly`], exact
//! `BigRational`). The GF(2) `adsmt-theory-finite-field` crate is FORBIDDEN here:
//! its `x²=x` + mod-2 quotient makes the false identity `x − x² = 0` pass, which
//! would admit `x ∈ ⟨x²⟩` — a false `unsat`. Char-0 obligations use ℚ; a real
//! GF(2) obligation would carry its own char and is out of P0 scope.

pub mod manifest;
pub mod poly;
#[cfg(feature = "term")]
pub mod term;

use manifest::CasManifest;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use poly::MPoly;

/// The verdict a re-checked CAS witness establishes about the SMT obligation
/// (`H ∧ ¬G` — the verus convention: a discharged goal reads `Unsat`). Maps to
/// `SatLevel::Definite{Sat,Unsat}` at the engine boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// A model exists (a counterexample / a satisfying assignment).
    Sat,
    /// No model — the goal is valid / the obligation discharged.
    Unsat,
}

/// What [`admit`] returns. Only [`Disposition::Verdict`] moves the engine; the
/// other two are the sound fallbacks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Disposition {
    /// The witness re-checked — a trusted verdict.
    Verdict(Verdict),
    /// The witness did NOT re-check (a CAS bug, a wrong/incomplete witness, a
    /// ring mismatch, a mis-shaped obligation) — the SOUND fallback. NEVER a
    /// verdict on the CAS's word.
    Unknown,
}

/// The coefficient ring of a polynomial obligation. `admit` dispatches the
/// re-checker on it (§9-B1). P0 re-checks char-0 rings over ℚ; a GF(2) obligation
/// is out of scope (→ `Unknown`) rather than mis-checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ring {
    /// Integers — re-checked over ℚ (a ℚ-identity proves the integer implication).
    Z,
    /// Rationals.
    Q,
    /// Reals (polynomial identities are char-0, re-checked over ℚ).
    R,
    /// Characteristic 2 — NOT re-checkable by this char-0 core (out of P0 scope).
    Gf2,
}

impl Ring {
    /// Is this ring re-checkable by the char-0 (ℚ) core? (§9-B1 forbids the GF(2)
    /// path here.)
    fn is_char0(self) -> bool {
        matches!(self, Ring::Z | Ring::Q | Ring::R)
    }
}

/// The integer domain of an existential-Diophantine variable — part of the
/// obligation, not a detail (§9-B3): `xⁿ` over ℕ excludes the `0`/sign
/// "solutions".
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Domain {
    /// ℕ — `≥ 1`.
    Nat,
    /// ℕ₀ / WNat — `≥ 0`.
    WNat,
    /// ℤ — unconstrained.
    Int,
}

impl Domain {
    fn contains(self, v: &BigInt) -> bool {
        match self {
            Domain::Nat => v >= &BigInt::one(),
            Domain::WNat => !v.is_negative(),
            Domain::Int => true,
        }
    }
}

/// The obligation `admit` re-checks a witness against. In the integrated path
/// this is DERIVED by `admit` from the original `Sequent` (§9-B2: never from the
/// untrusted extraction); in P0 it is built directly (a caller / test supplies
/// the trusted polynomials). Carries only what the trusted re-check needs.
#[derive(Clone, Debug)]
pub enum Obligation {
    /// `g₁=0,…,gₘ=0 ⊢ f=0` — the `gᵢ` come from the hypotheses.
    IdealMembership { ring: Ring, f: MPoly, generators: Vec<MPoly> },
    /// Is `target` reducible (∃ a non-trivial factorization)?
    Factorization { ring: Ring, target: MPoly },
    /// Is `n` composite?
    Compositeness { n: BigInt },
    /// Is `n` prime? (Re-checked by a [`Witness::PrattPrime`] certificate — the
    /// dual of `Compositeness`; a divisor witnesses composite, a Pratt tree
    /// witnesses prime.)
    Primality { n: BigInt },
    /// `∃ x̄ ∈ domains. ⋀ⱼ systemⱼ(x̄) = 0` (an UNBOUNDED existential — a bounded
    /// one is decidable and routes to the native engine, §8).
    DiophantineExists { system: Vec<MPoly>, domains: Vec<Domain> },
}

/// A **Pratt primality certificate** (recursive Lucas) for a number `n`: a
/// witness `base` and the full prime factorization of `n − 1` as `(qᵢ, eᵢ,
/// certᵢ)` triples, where `∏ qᵢ^eᵢ = n − 1` and each `certᵢ` recursively proves
/// `qᵢ` prime (down to the axiomatic base prime 2). See [`admit`] for the exact
/// re-check. Poly-size and poly-time checkable (primality ∈ NP), so it is a
/// genuine witness-delegation certificate — the CAS finds it, the trusted core
/// re-checks it. Bounded fail-closed at re-check (`MAX_PRATT_NODES`).
#[derive(Clone, Debug)]
pub struct PrattCert {
    /// The Lucas witness `a` (a primitive-root-like base mod `n`).
    pub base: BigInt,
    /// The factorization of `n − 1`: `(prime qᵢ, exponent eᵢ, cert that qᵢ is prime)`.
    pub factors: Vec<(BigInt, u32, PrattCert)>,
}

/// The witness a backend returns; each variant has a trusted re-checker in
/// [`admit`]. Corrected per §9: cofactors are `(generator-index, qᵢ)` pairs
/// (§9-G9); factors are `≥2 non-unit` (§9-B5); a divisor is re-checked
/// `1 < d < n` (§9-B6); an int solution is re-checked domain-∈ **and** equation
/// (§9-B3).
#[derive(Clone, Debug)]
pub enum Witness {
    /// `f = Σ qᵢ·g_{idxᵢ}` — the pairs `(idx, qᵢ)`.
    Cofactors(Vec<(usize, MPoly)>),
    /// `∏ factors = target`, each factor a non-unit.
    Factors(Vec<MPoly>),
    /// A divisor `d` of `n`.
    Divisor(BigInt),
    /// One integer per existential variable.
    IntSolution(Vec<BigInt>),
    /// A Pratt primality certificate for `n` (recursive Lucas).
    PrattPrime(PrattCert),
}

/// DoS bound on a Pratt certificate re-check — total tree nodes visited. A cert
/// exceeding it is REJECTED (fail-closed → the obligation stays `Unknown`), never
/// accepted. Generous: a Pratt tree for `n` has O(log n) nodes, so 4096 covers
/// primes of thousands of bits. Same fail-closed discipline as the §8
/// counterexample-tree bound; the re-check is iterative, so it never stack-overflows.
const MAX_PRATT_NODES: u32 = 4096;

/// Re-check a [`PrattCert`] proves `n` prime by the recursive Lucas criterion —
/// ITERATIVELY (a worklist, no native recursion) and BUDGET-bounded. Sound:
/// returns `true` ONLY if `n` is genuinely prime.
///
/// For each `(n, cert)` popped (`n = 2` is the axiomatic base prime; `n < 2`
/// fails): (1) `∏ qᵢ^eᵢ = n − 1` EXACTLY — the soundness hinge, forcing the `qᵢ`
/// to be ALL prime factors of `n − 1` (a partial factorization would let a
/// composite masquerade; overshoot bails early so no giant powers are formed);
/// (2) each `qᵢ` is pushed for recursive prime verification; (3) `base^(n−1) ≡ 1
/// (mod n)`; (4) for every listed `qᵢ`, `base^((n−1)/qᵢ) ≢ 1 (mod n)`. All pass
/// for every node within budget ⇒ `n` prime (Lucas's theorem).
fn pratt_verifies(n: &BigInt, cert: &PrattCert) -> bool {
    let one = BigInt::one();
    let two = BigInt::from(2);
    let mut budget = MAX_PRATT_NODES;
    let mut work: Vec<(BigInt, &PrattCert)> = vec![(n.clone(), cert)];
    while let Some((n, cert)) = work.pop() {
        if budget == 0 {
            return false; // DoS bound, fail-closed
        }
        budget -= 1;
        if n == two {
            continue; // axiomatic base prime
        }
        if n < two {
            return false; // 0, 1, negatives are not prime
        }
        let n_minus_1 = &n - &one;
        // (1) reconstruct n−1 = ∏ qᵢ^eᵢ EXACTLY.
        let mut prod = one.clone();
        for (q, e, sub) in &cert.factors {
            if q < &two || *e == 0 {
                return false; // a factor must be ≥ 2 with positive multiplicity
            }
            for _ in 0..*e {
                prod *= q;
                if prod > n_minus_1 {
                    return false; // overshoot ⇒ can't equal n−1 (also bounds this loop)
                }
            }
            work.push((q.clone(), sub)); // (2) qᵢ must be prime — recurse
        }
        if prod != n_minus_1 {
            return false;
        }
        // canonical base residue in [0, n)
        let a = ((&cert.base % &n) + &n) % &n;
        // (3) base^(n−1) ≡ 1 (mod n)
        if a.modpow(&n_minus_1, &n) != one {
            return false;
        }
        // (4) for each qᵢ: base^((n−1)/qᵢ) ≢ 1 (mod n)
        for (q, _, _) in &cert.factors {
            if a.modpow(&(&n_minus_1 / q), &n) == one {
                return false;
            }
        }
    }
    true
}

/// **The trusted re-checker — the only thing that moves a verdict.** Clean-room:
/// it re-validates the `witness` against the `obligation` using exact ℚ / ℤ
/// arithmetic, DERIVES the verdict from what the witness establishes (it does not
/// trust any backend-declared direction — §9-G3), and returns [`Disposition::Unknown`]
/// on ANY mismatch (wrong witness, ring not char-0, shape mismatch). A failed
/// re-check is a CAS bug ⇒ `Unknown`, never a verdict.
///
/// (In the integrated path this same function is the offline `adsmt-cert`
/// replay checker — one re-checker, two callers, §7. In P0 it is the online half.)
#[must_use]
pub fn admit(obligation: &Obligation, witness: &Witness) -> Disposition {
    match (obligation, witness) {
        // Ideal membership: f = Σ qᵢ·g_{idxᵢ} exactly over ℚ ⇒ f=0 is entailed by
        // ⋀gᵢ=0 ⇒ the obligation `⋀gᵢ=0 ∧ f≠0` is UNSAT (goal valid).
        (Obligation::IdealMembership { ring, f, generators }, Witness::Cofactors(cofactors)) => {
            if !ring.is_char0() {
                return Disposition::Unknown; // §9-B1: not our re-check ring
            }
            let mut combo = MPoly::zero();
            for (idx, q) in cofactors {
                let Some(g) = generators.get(*idx) else {
                    return Disposition::Unknown; // §9-G9: dangling generator index
                };
                combo = combo.add(&q.mul(g));
            }
            if f.sub(&combo).is_zero() {
                Disposition::Verdict(Verdict::Unsat)
            } else {
                Disposition::Unknown // wrong cofactor (the §9-B1 GF(2) trap dies here over ℚ)
            }
        }

        // Factorization: ≥2 NON-UNIT factors whose product is the target ⇒
        // reducible ⇒ Sat of the "∃ non-trivial factorization" obligation. The
        // IRREDUCIBLE direction has no short witness (§9-B5) — never admitted here.
        (Obligation::Factorization { ring, target }, Witness::Factors(factors)) => {
            if !ring.is_char0() {
                return Disposition::Unknown;
            }
            if factors.len() < 2 || factors.iter().any(|p| p.is_unit() || p.is_zero()) {
                return Disposition::Unknown; // trivial / unit factor proves nothing
            }
            if MPoly::product(factors).sub(target).is_zero() {
                Disposition::Verdict(Verdict::Sat)
            } else {
                Disposition::Unknown
            }
        }

        // Compositeness: a PROPER divisor `1 < d < n` with `n mod d = 0` ⇒ Sat.
        // (§9-B6: without the proper bound, d∈{1,n} would call every prime composite.)
        (Obligation::Compositeness { n }, Witness::Divisor(d)) => {
            let one = BigInt::one();
            if d > &one && d < n && (n % d).is_zero() {
                Disposition::Verdict(Verdict::Sat)
            } else {
                Disposition::Unknown
            }
        }

        // Primality: a Pratt certificate that re-checks (recursive Lucas) ⇒ n is
        // prime ⇒ Sat. The dual of Compositeness — a divisor witnesses composite,
        // a Pratt tree witnesses prime. DoS-bounded, fail-closed to Unknown.
        (Obligation::Primality { n }, Witness::PrattPrime(cert)) => {
            if pratt_verifies(n, cert) {
                Disposition::Verdict(Verdict::Sat)
            } else {
                Disposition::Unknown
            }
        }

        // Existential Diophantine: EVERY coordinate in its declared domain AND
        // every system polynomial evaluates to 0 at the tuple ⇒ a real model ⇒
        // Sat. (§9-B3: the domain conjunct is re-checked, not just the equation —
        // else a signed / zero tuple slips through a ℕ-existential.)
        (Obligation::DiophantineExists { system, domains }, Witness::IntSolution(tuple)) => {
            if tuple.len() != domains.len() {
                return Disposition::Unknown;
            }
            for (v, dom) in tuple.iter().zip(domains.iter()) {
                if !dom.contains(v) {
                    return Disposition::Unknown; // out-of-domain coordinate
                }
            }
            let point: Vec<BigRational> = tuple.iter().map(|z| BigRational::from(z.clone())).collect();
            if system.iter().all(|p| p.eval(&point).is_zero()) {
                Disposition::Verdict(Verdict::Sat)
            } else {
                Disposition::Unknown // the tuple is not a root
            }
        }

        // Any other (obligation, witness) pairing is mis-shaped ⇒ the sound fallback.
        _ => Disposition::Unknown,
    }
}

/// Which verdict direction a `(class, backend)` row's witness proves (the other
/// direction downgrades) — §1/§3-A. Kept for the capability surface; a backend
/// declares it, `admit` ignores it (§9-G3, it derives the verdict itself).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WitnessedDir {
    Sat,
    Unsat,
}

/// A class of algebraic obligation a backend may decide (the §3 taxonomy). P0
/// re-checks the first four; the rest are declared for the capability surface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CasClass {
    IdealMembership,
    Factorization,
    Compositeness,
    Primality,
    DiophantineExists,
    UniversalRefutation,
}

/// A capability a backend advertises — read by the dispatcher to SELECT among
/// backends **without spawning** them (the manifest `cas.enabled` order picks;
/// `admit` still gates the verdict). Static per backend.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CasCapability {
    pub class: CasClass,
    pub witnessed: WitnessedDir,
}

/// What a backend returns from `decide`.
#[derive(Clone, Debug)]
pub enum CasReply {
    /// A witness for a direction — handed to [`admit`] (which re-derives the verdict).
    Witnessed(Witness),
    /// The backend could not decide this obligation.
    Undecided,
    /// The backend errored (crash, timeout, parse failure).
    Error,
}

/// The one trait every backend implements — in-tree (behind the `cas` feature) or
/// out-of-tree (`adsmt-contrib/cas-backend-*`). P0 defines the surface;
/// `cas-backend-singular` (P1) is the first implementer.
pub trait CasBackend: Send {
    /// Stable identifier (matches the `adsmt.toml` `[cas.backends.<name>]` key).
    fn name(&self) -> &'static str;
    /// Static — lets the dispatcher pick without spawning the CAS.
    fn capabilities(&self) -> &[CasCapability];
    /// Run the (already-classified) obligation. Subprocess for core backends.
    fn decide(&self, obligation: &Obligation) -> CasReply;
}

/// The class an obligation falls into (for backend selection).
pub fn classify(obligation: &Obligation) -> CasClass {
    match obligation {
        Obligation::IdealMembership { .. } => CasClass::IdealMembership,
        Obligation::Factorization { .. } => CasClass::Factorization,
        Obligation::Compositeness { .. } => CasClass::Compositeness,
        Obligation::Primality { .. } => CasClass::Primality,
        Obligation::DiophantineExists { .. } => CasClass::DiophantineExists,
    }
}

/// The manifest's kebab-case class name → [`CasClass`].
pub(crate) fn class_from_kebab(s: &str) -> Option<CasClass> {
    Some(match s {
        "ideal-membership" => CasClass::IdealMembership,
        "factorization" => CasClass::Factorization,
        "compositeness" => CasClass::Compositeness,
        "primality" => CasClass::Primality,
        "diophantine-exists" => CasClass::DiophantineExists,
        "universal-refutation" => CasClass::UniversalRefutation,
        _ => return None,
    })
}

/// **The dispatcher** — try the manifest-enabled backends in `cas.enabled` order,
/// the FIRST whose witness `admit()`-re-checks wins (§4.3). A backend that is not
/// permitted the class, does not cover it, returns `Undecided`/`Error`, or whose
/// witness fails the re-check falls through to the next. No eligible backend ⇒
/// [`Disposition::Unknown`]. Soundness rests entirely on [`admit`]: no manifest,
/// try-order, or lying backend can move a verdict without a re-checked witness.
pub fn dispatch(
    manifest: &CasManifest,
    backends: &[&dyn CasBackend],
    obligation: &Obligation,
) -> Disposition {
    let class = classify(obligation);
    for name in manifest.try_order() {
        if !manifest.permits(name, class) {
            continue; // manifest allow-list narrows (never widens)
        }
        let Some(backend) = backends.iter().find(|b| b.name() == name) else { continue };
        if !backend.capabilities().iter().any(|cap| cap.class == class) {
            continue; // backend does not advertise this class
        }
        if let CasReply::Witnessed(w) = backend.decide(obligation)
            && let Disposition::Verdict(v) = admit(obligation, &w)
        {
            return Disposition::Verdict(v);
        }
        // Undecided / Error / failed re-check → the next backend in order.
    }
    Disposition::Unknown
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ri(n: i64) -> BigRational {
        BigRational::from(BigInt::from(n))
    }
    fn c(n: i64) -> MPoly {
        MPoly::constant(ri(n))
    }
    fn x() -> MPoly {
        MPoly::var(0)
    }
    fn y() -> MPoly {
        MPoly::var(1)
    }

    // ── Ideal membership (the gold case) ────────────────────────────────────
    #[test]
    fn membership_valid_cofactor_is_unsat() {
        // x²−1 ∈ ⟨x−1⟩ with cofactor x+1: (x−1)(x+1) = x²−1. Goal x²−1=0 valid.
        let f = x().mul(&x()).sub(&c(1)); // x²−1
        let g = x().sub(&c(1)); // x−1
        let ob = Obligation::IdealMembership { ring: Ring::Z, f, generators: vec![g] };
        let w = Witness::Cofactors(vec![(0, x().add(&c(1)))]); // q = x+1
        assert_eq!(admit(&ob, &w), Disposition::Verdict(Verdict::Unsat));
    }

    #[test]
    fn membership_wrong_cofactor_the_gf2_trap_is_rejected() {
        // §9-B1: x ∈ ⟨x²⟩ is FALSE. Bad cofactor q=1: x − 1·x² = x − x². Over GF(2)
        // that collapses to 0 (false accept); over ℚ it is non-zero ⇒ Unknown.
        let ob =
            Obligation::IdealMembership { ring: Ring::Z, f: x(), generators: vec![x().mul(&x())] };
        let w = Witness::Cofactors(vec![(0, c(1))]);
        assert_eq!(admit(&ob, &w), Disposition::Unknown);
    }

    #[test]
    fn membership_dangling_generator_index_is_unknown() {
        let ob = Obligation::IdealMembership { ring: Ring::Z, f: x(), generators: vec![x()] };
        let w = Witness::Cofactors(vec![(7, c(1))]); // no generator 7
        assert_eq!(admit(&ob, &w), Disposition::Unknown);
    }

    #[test]
    fn membership_gf2_ring_is_out_of_scope() {
        // A char-2 obligation must NOT be re-checked by the char-0 core (§9-B1).
        let ob = Obligation::IdealMembership { ring: Ring::Gf2, f: x(), generators: vec![x()] };
        let w = Witness::Cofactors(vec![(0, c(1))]); // x = 1·x, a true identity even over ℚ
        assert_eq!(admit(&ob, &w), Disposition::Unknown);
    }

    // ── Factorization (reducible only, §9-B5) ───────────────────────────────
    #[test]
    fn factorization_two_nonunit_factors_is_sat() {
        let target = x().mul(&x()).sub(&c(1)); // x²−1
        let ob = Obligation::Factorization { ring: Ring::Z, target };
        let w = Witness::Factors(vec![x().sub(&c(1)), x().add(&c(1))]);
        assert_eq!(admit(&ob, &w), Disposition::Verdict(Verdict::Sat));
    }

    #[test]
    fn factorization_single_factor_proves_nothing() {
        // §9-B5: a 1-element "factor list" multiply-backs to the target but does
        // NOT establish reducibility.
        let target = x().mul(&x()).sub(&c(1));
        let ob = Obligation::Factorization { ring: Ring::Z, target: target.clone() };
        assert_eq!(admit(&ob, &Witness::Factors(vec![target])), Disposition::Unknown);
    }

    #[test]
    fn factorization_unit_factor_is_rejected() {
        // [2, (x²−1)/2] multiplies back but 2 is a unit ⇒ not a proper factorization.
        let target = x().mul(&x()).sub(&c(1));
        let ob = Obligation::Factorization { ring: Ring::Q, target };
        let half = MPoly::constant(BigRational::new(BigInt::from(1), BigInt::from(2)));
        let w = Witness::Factors(vec![c(2), half.mul(&x().mul(&x()).sub(&c(1)))]);
        assert_eq!(admit(&ob, &w), Disposition::Unknown);
    }

    // ── Compositeness (proper divisor, §9-B6) ───────────────────────────────
    #[test]
    fn compositeness_proper_divisor_is_sat() {
        let ob = Obligation::Compositeness { n: BigInt::from(15) };
        assert_eq!(admit(&ob, &Witness::Divisor(BigInt::from(3))), Disposition::Verdict(Verdict::Sat));
    }

    #[test]
    fn compositeness_divisor_one_or_n_is_rejected() {
        // §9-B6: d∈{1,n} divides every n; without the proper bound, 7 (prime) is
        // called "composite".
        let ob = Obligation::Compositeness { n: BigInt::from(7) };
        assert_eq!(admit(&ob, &Witness::Divisor(BigInt::from(1))), Disposition::Unknown);
        assert_eq!(admit(&ob, &Witness::Divisor(BigInt::from(7))), Disposition::Unknown);
        assert_eq!(admit(&ob, &Witness::Divisor(BigInt::from(2))), Disposition::Unknown); // 7 mod 2 ≠ 0
    }

    // ── Existential Diophantine (domain + equation, §9-B3) ───────────────────
    #[test]
    fn diophantine_valid_nat_solution_is_sat() {
        // ∃x,y∈ℕ. x²+y²−25 = 0 — witness (3,4).
        let sys = vec![x().mul(&x()).add(&y().mul(&y())).sub(&c(25))];
        let ob = Obligation::DiophantineExists { system: sys, domains: vec![Domain::Nat, Domain::Nat] };
        let w = Witness::IntSolution(vec![BigInt::from(3), BigInt::from(4)]);
        assert_eq!(admit(&ob, &w), Disposition::Verdict(Verdict::Sat));
    }

    #[test]
    fn diophantine_out_of_domain_coordinate_is_rejected() {
        // §9-B3: (0,5) roots the equation but 0 ∉ ℕ(=≥1) ⇒ NOT a ℕ-solution.
        let sys = vec![x().mul(&x()).add(&y().mul(&y())).sub(&c(25))];
        let ob = Obligation::DiophantineExists { system: sys, domains: vec![Domain::Nat, Domain::Nat] };
        let w = Witness::IntSolution(vec![BigInt::from(0), BigInt::from(5)]);
        assert_eq!(admit(&ob, &w), Disposition::Unknown);
    }

    #[test]
    fn diophantine_non_root_is_rejected() {
        let sys = vec![x().mul(&x()).add(&y().mul(&y())).sub(&c(25))];
        let ob = Obligation::DiophantineExists { system: sys, domains: vec![Domain::Nat, Domain::Nat] };
        let w = Witness::IntSolution(vec![BigInt::from(3), BigInt::from(3)]); // 18 ≠ 25
        assert_eq!(admit(&ob, &w), Disposition::Unknown);
    }

    #[test]
    fn diophantine_wnat_admits_zero() {
        // Same equation but WNat(≥0): (0,5) is now a valid solution ⇒ Sat.
        let sys = vec![x().mul(&x()).add(&y().mul(&y())).sub(&c(25))];
        let ob =
            Obligation::DiophantineExists { system: sys, domains: vec![Domain::WNat, Domain::WNat] };
        let w = Witness::IntSolution(vec![BigInt::from(0), BigInt::from(5)]);
        assert_eq!(admit(&ob, &w), Disposition::Verdict(Verdict::Sat));
    }

    #[test]
    fn mismatched_pairing_is_unknown() {
        let ob = Obligation::Compositeness { n: BigInt::from(15) };
        assert_eq!(admit(&ob, &Witness::Factors(vec![c(3), c(5)])), Disposition::Unknown);
    }

    // ── primality (Pratt certificate re-check) ───────────────────────────────
    fn bi(n: i64) -> BigInt {
        BigInt::from(n)
    }
    /// Base-case cert for the axiomatic prime 2 (contents ignored by the checker).
    fn p2() -> PrattCert {
        PrattCert { base: bi(1), factors: vec![] }
    }
    fn pc(base: i64, factors: Vec<(i64, u32, PrattCert)>) -> PrattCert {
        PrattCert {
            base: bi(base),
            factors: factors.into_iter().map(|(q, e, c)| (bi(q), e, c)).collect(),
        }
    }
    /// A genuine Pratt cert for 3 (3−1 = 2, base 2).
    fn cert3() -> PrattCert {
        pc(2, vec![(2, 1, p2())])
    }

    #[test]
    fn primality_valid_pratt_cert_is_sat() {
        // 7 prime: 7−1 = 6 = 2·3, base 3. 3^6≡1 (mod 7); 3^3≡6≢1; 3^2≡2≢1.
        let cert = pc(3, vec![(2, 1, p2()), (3, 1, cert3())]);
        assert_eq!(
            admit(&Obligation::Primality { n: bi(7) }, &Witness::PrattPrime(cert)),
            Disposition::Verdict(Verdict::Sat)
        );
    }

    #[test]
    fn primality_carmichael_561_is_rejected() {
        // 561 = 3·11·17 is a CARMICHAEL number: a^560≡1 (mod 561) for all a coprime
        // to 561, so it passes the Fermat condition — but Lucas's ≢1 side condition
        // cannot hold for every prime factor of 560 (no primitive root exists for a
        // composite). With base 2: 2^(560/7)=2^80≡1 (mod 561), so it is REJECTED.
        // (560 = 2^4·5·7.)
        let cert = pc(2, vec![(2, 4, p2()), (5, 1, pc(2, vec![(2, 2, p2())])), (7, 1, pc(3, vec![(2, 1, p2()), (3, 1, cert3())]))]);
        assert_eq!(
            admit(&Obligation::Primality { n: bi(561) }, &Witness::PrattPrime(cert)),
            Disposition::Unknown
        );
    }

    #[test]
    fn primality_partial_factorization_is_rejected() {
        // A cert for 7 that OMITS the factor 3 (claims 6 = 2 only) ⇒ ∏ ≠ n−1 ⇒
        // rejected — the soundness hinge against a masquerading composite.
        let cert = pc(3, vec![(2, 1, p2())]); // prod = 2 ≠ 6
        assert_eq!(
            admit(&Obligation::Primality { n: bi(7) }, &Witness::PrattPrime(cert)),
            Disposition::Unknown
        );
    }

    #[test]
    fn primality_composite_factor_claim_is_rejected() {
        // Claim 4 is a "prime factor" of 15−1=14? No: 14 = 2·7. But claim 15−1 via
        // a composite factor: cert for 15 (composite) with factors 2·7 and base 2 —
        // 2^14 mod 15 = 4 ≢ 1 ⇒ Fermat condition already fails ⇒ rejected. And a
        // cert that lists a composite q with a bogus sub-cert fails at the recursion.
        let cert = pc(2, vec![(2, 1, p2()), (7, 1, pc(3, vec![(2, 1, p2()), (3, 1, cert3())]))]);
        assert_eq!(
            admit(&Obligation::Primality { n: bi(15) }, &Witness::PrattPrime(cert)),
            Disposition::Unknown
        );
        // A cert naming a COMPOSITE (4) as a prime factor of n−1 fails the recursive
        // prime check on 4 (no valid Pratt cert for 4 exists).
        let bogus4 = pc(3, vec![(2, 2, p2())]); // pretends 4 is prime (4−1=3=2? no, 3; bogus)
        let cert2 = pc(2, vec![(4, 1, bogus4)]); // n−1 = 4 ⇒ n = 5, but factor 4 is composite
        assert_eq!(
            admit(&Obligation::Primality { n: bi(5) }, &Witness::PrattPrime(cert2)),
            Disposition::Unknown
        );
    }

    #[test]
    fn primality_one_and_composite_targets_are_rejected() {
        // n < 2 and an even composite have no valid Pratt cert.
        assert_eq!(admit(&Obligation::Primality { n: bi(1) }, &Witness::PrattPrime(p2())), Disposition::Unknown);
        assert_eq!(admit(&Obligation::Primality { n: bi(9) }, &Witness::PrattPrime(pc(2, vec![(2, 3, p2())]))), Disposition::Unknown);
    }

    #[test]
    fn primality_node_budget_is_fail_closed() {
        // A pathological cert that would blow the node budget is rejected, not
        // accepted (DoS guard). Build a wide fan-out beyond MAX_PRATT_NODES.
        let wide: Vec<(BigInt, u32, PrattCert)> =
            (0..(MAX_PRATT_NODES as usize + 10)).map(|_| (bi(2), 1, p2())).collect();
        let cert = PrattCert { base: bi(3), factors: wide };
        assert_eq!(
            admit(&Obligation::Primality { n: bi(7) }, &Witness::PrattPrime(cert)),
            Disposition::Unknown
        );
    }

    #[test]
    fn primality_adversarial_pseudoprimes_all_rejected() {
        // Empirical confirmation of the cas-p19-pratt-adversarial workflow's
        // predictions ([[feedback_empirical_adversarial_review]]): EXECUTE the
        // proposed break-certs, assert every composite is rejected.
        let unknown = |n: i64, cert: PrattCert| {
            assert_eq!(
                admit(&Obligation::Primality { n: bi(n) }, &Witness::PrattPrime(cert)),
                Disposition::Unknown,
                "composite {n} must NOT be certified prime",
            );
        };
        // 341 = 11·31 — a FERMAT pseudoprime to base 2 (2^340≡1 mod 341), a
        // distinct class from Carmichael. 340 = 2^2·5·17 (well-formed factor tree),
        // yet some 2^(340/q)≡1 (mod 341) ⇒ the Lucas ≢1 side condition fails ⇒ reject.
        unknown(341, pc(2, vec![
            (2, 2, p2()),
            (5, 1, pc(2, vec![(2, 2, p2())])),           // 5-1 = 4 = 2^2
            (17, 1, pc(3, vec![(2, 4, p2())])),          // 17-1 = 16 = 2^4, base 3
        ]));
        // 561 Carmichael with a DIFFERENT base (4) — confirms NO base certifies it.
        unknown(561, pc(4, vec![
            (2, 4, p2()),
            (5, 1, pc(2, vec![(2, 2, p2())])),
            (7, 1, pc(3, vec![(2, 1, p2()), (3, 1, cert3())])),
        ]));
        // 9 = 3² with base 8 ≡ −1 (mod 9): 8^8≡1 (Fermat) but 8^4≡1 ⇒ Lucas q=2 fails.
        unknown(9, pc(8, vec![(2, 3, p2())]));
        // 25 = 5² with a malformed exponent (2·4^3 = 128 > 24) ⇒ overshoot early-reject.
        unknown(25, pc(2, vec![(2, 1, p2()), (4, 3, p2())]));
        // 21 = 3·7 — no base passes both Fermat and the primitive-root test.
        unknown(21, pc(10, vec![(2, 1, p2()), (5, 1, pc(2, vec![(2, 2, p2())]))]));
    }

    // ── dispatch (manifest-driven, admit-gated) ──────────────────────────────
    struct Mock {
        nm: &'static str,
        caps: Vec<CasCapability>,
        reply: CasReply,
    }
    impl CasBackend for Mock {
        fn name(&self) -> &'static str {
            self.nm
        }
        fn capabilities(&self) -> &[CasCapability] {
            &self.caps
        }
        fn decide(&self, _: &Obligation) -> CasReply {
            self.reply.clone()
        }
    }
    fn membership_ob() -> Obligation {
        Obligation::IdealMembership {
            ring: Ring::Z,
            f: x().mul(&x()).sub(&c(1)),
            generators: vec![x().sub(&c(1))],
        }
    }
    fn cap_membership() -> Vec<CasCapability> {
        vec![CasCapability { class: CasClass::IdealMembership, witnessed: WitnessedDir::Unsat }]
    }

    #[test]
    fn dispatch_admits_a_valid_witness() {
        let m = CasManifest::from_adsmt_toml("[cas]\nenabled=[\"good\"]\n").unwrap();
        let good = Mock {
            nm: "good",
            caps: cap_membership(),
            reply: CasReply::Witnessed(Witness::Cofactors(vec![(0, x().add(&c(1)))])),
        };
        let backends: Vec<&dyn CasBackend> = vec![&good];
        assert_eq!(
            dispatch(&m, &backends, &membership_ob()),
            Disposition::Verdict(Verdict::Unsat)
        );
    }

    #[test]
    fn dispatch_falls_through_a_wrong_witness_in_enabled_order() {
        // "bad" is tried first (it's first in cas.enabled) and returns a WRONG
        // cofactor (q=1 → x²−1 − (x−1) ≠ 0) that admit REJECTS; dispatch falls
        // through to "good". Proves the try-order + admit-gating: a lying backend
        // can neither win nor starve a correct later one.
        let m = CasManifest::from_adsmt_toml("[cas]\nenabled=[\"bad\",\"good\"]\n").unwrap();
        let bad = Mock {
            nm: "bad",
            caps: cap_membership(),
            reply: CasReply::Witnessed(Witness::Cofactors(vec![(0, c(1))])),
        };
        let good = Mock {
            nm: "good",
            caps: cap_membership(),
            reply: CasReply::Witnessed(Witness::Cofactors(vec![(0, x().add(&c(1)))])),
        };
        let backends: Vec<&dyn CasBackend> = vec![&bad, &good];
        assert_eq!(
            dispatch(&m, &backends, &membership_ob()),
            Disposition::Verdict(Verdict::Unsat)
        );
    }

    #[test]
    fn dispatch_disabled_or_unpermitted_backend_yields_unknown() {
        // A backend not in the manifest's class allow-list is never tried.
        let m = CasManifest::from_adsmt_toml(
            "[cas]\nenabled=[\"good\"]\n[cas.backends.good]\nclasses=[\"factorization\"]\n",
        )
        .unwrap();
        let good = Mock {
            nm: "good",
            caps: cap_membership(),
            reply: CasReply::Witnessed(Witness::Cofactors(vec![(0, x().add(&c(1)))])),
        };
        let backends: Vec<&dyn CasBackend> = vec![&good];
        assert_eq!(dispatch(&m, &backends, &membership_ob()), Disposition::Unknown);
    }
}
