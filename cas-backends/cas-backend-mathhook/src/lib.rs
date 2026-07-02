//! **MathHook backend** — an UNTRUSTED, IN-PROCESS CAS oracle for `adsmt-cas`.
//!
//! MathHook (<https://github.com/AhmedMashour/mathhook>, developed here against the
//! user's fork <https://github.com/Honey-Be/mathhook>) is a Rust computer-algebra
//! system under **MIT OR Apache-2.0**. Because it is permissively licensed — unlike
//! Singular (GPL, hence a subprocess) — it links **in-process** as a plain crate
//! dependency; this is the first in-process CAS backend.
//!
//! ## Soundness
//! MathHook is UNTRUSTED. This backend only ever RETURNS A WITNESS (a candidate
//! factorization) — it never asserts a verdict. Every witness is re-checked by
//! [`adsmt_cas::admit`] (exact `BigRational` arithmetic); a MathHook bug, a wrong
//! factorization, or a conversion glitch can only ever yield [`CasReply::Undecided`]
//! or a witness that FAILS the re-check ⇒ `Unknown`, never a wrong verdict.
//!
//! ## Scope (first slice)
//! MathHook's `Expression::factor()` factors over char-0. This backend advertises
//! [`CasClass::Factorization`] and converts a `Factorization` obligation's target
//! polynomial to a MathHook expression, factors it, and converts the factors back
//! to a [`Witness::Factors`]. A polynomial it cannot faithfully round-trip (a shape
//! outside the univariate-over-ℚ core, a factor it cannot read back) ⇒ `Undecided`
//! (sound — the dispatcher falls through). MathHook also ships Gröbner bases and
//! finite fields; wiring those (and contributing a cofactor-WITNESS Gröbner
//! membership + the convergence fix upstream) is a follow-on.

use adsmt_cas::{CasBackend, CasCapability, CasClass, CasReply, Obligation, Ring, WitnessedDir};

mod convert;

/// The MathHook in-process backend. Stateless (MathHook is called per `decide`).
#[derive(Debug, Default, Clone, Copy)]
pub struct MathhookBackend;

impl MathhookBackend {
    pub fn new() -> Self {
        MathhookBackend
    }
}

const CAPABILITIES: &[CasCapability] =
    &[CasCapability { class: CasClass::Factorization, witnessed: WitnessedDir::Sat }];

impl CasBackend for MathhookBackend {
    fn name(&self) -> &'static str {
        "mathhook"
    }

    fn capabilities(&self) -> &[CasCapability] {
        CAPABILITIES
    }

    fn decide(&self, obligation: &Obligation) -> CasReply {
        match obligation {
            // Factor the target with MathHook, convert the factors back to the
            // trusted representation, and hand them to `admit` as a witness. Any
            // conversion failure / unsupported shape ⇒ Undecided (sound downgrade).
            //
            // MathHook's `factor()` operates over char-0 (ℤ/ℚ/ℝ). We only OFFER a
            // witness for those rings; `admit` is ring-aware and would gate a
            // mod-p factorization anyway, but declining up front avoids wasted work
            // and keeps the backend's scope honest. (`IntModulo`'s factorization is
            // categorically unsupported by the re-check core — non-constant units.)
            Obligation::Factorization { ring: Ring::Z | Ring::Q | Ring::R, target } => {
                convert::factor_target(target).map_or(CasReply::Undecided, CasReply::Witnessed)
            }
            // Every other class (membership, compositeness, primality, Diophantine,
            // GF(pⁿ)) — and factorization over a positive-characteristic ring — is
            // not covered by this first slice ⇒ Undecided.
            _ => CasReply::Undecided,
        }
    }

    /// ADVISORY step-by-step provenance for a char-0 factorization — MathHook's
    /// educational explanation (§ the "Educational Features" the backend leverages).
    /// Text only; it rides into the certificate's `CasProof::provenance` and never
    /// affects the `admit` re-check.
    fn explain(&self, obligation: &Obligation) -> Option<String> {
        match obligation {
            Obligation::Factorization { ring: Ring::Z | Ring::Q | Ring::R, target } => {
                convert::explain_factorization(target)
            }
            _ => None,
        }
    }
}
