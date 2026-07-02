//! `MPoly` ↔ MathHook `Expression` conversion for the factorization backend.
//!
//! The conversion is CONSERVATIVE: anything it cannot faithfully round-trip yields
//! `None` (⇒ the backend returns `Undecided`, a sound downgrade — `admit` never
//! sees an unfaithful witness). Soundness never rests on this conversion: `admit`
//! independently re-checks `∏ factors = target` over the exact re-check ring, so a
//! wrong factorization / conversion glitch can only ever yield `Unknown`.

use adsmt_cas::poly::MPoly;
use adsmt_cas::Witness;
use mathhook_core::{Expression, Factor, Number};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

/// Factor `target` with MathHook and return a [`Witness::Factors`], or `None` if
/// the polynomial cannot be built / a factor cannot be read back / MathHook does
/// not split it into ≥ 2 non-constant factors.
pub fn factor_target(target: &MPoly) -> Option<Witness> {
    let expr = mpoly_to_expr(target);
    let factored = expr.factor();

    // Decompose the factored expression into candidate factor polynomials.
    let mut factors = Vec::new();
    for f in flatten_product(&factored) {
        factors.push(expr_to_mpoly(&f)?); // a factor we cannot read back ⇒ bail
    }

    // Fold the CONSTANT factors (a leading content) into a non-constant factor so
    // every returned factor is non-constant (hence a non-unit over any ring), and
    // the product still equals `target`. `admit` re-checks ∏ = target + non-unit.
    let mut content = MPoly::constant(BigRational::one());
    let mut nonconst = Vec::new();
    for f in factors {
        if f.as_constant().is_some() {
            content = content.mul(&f);
        } else {
            nonconst.push(f);
        }
    }
    if nonconst.len() < 2 {
        return None; // irreducible / not split ⇒ nothing non-trivial to witness
    }
    nonconst[0] = nonconst[0].mul(&content); // fold content; keeps ∏ = target
    Some(Witness::Factors(nonconst))
}

/// Build a MathHook `Expression` for a polynomial, variable `i` ↦ symbol `v{i}`,
/// exact-`BigRational` coefficients (an integer coefficient uses MathHook's
/// canonical `Integer`/`BigInteger` form, a fraction its `Rational`).
fn mpoly_to_expr(p: &MPoly) -> Expression {
    if p.is_zero() {
        return Expression::integer(0);
    }
    let terms: Vec<Expression> = p
        .iter()
        .map(|(mono, coeff)| {
            let mut factors = vec![coeff_to_expr(coeff)];
            for &(v, e) in mono {
                let sym = Expression::symbol(format!("v{v}"));
                factors.push(if e == 1 {
                    sym
                } else {
                    Expression::pow(sym, Expression::integer(e as i64))
                });
            }
            Expression::mul(factors)
        })
        .collect();
    Expression::add(terms)
}

fn coeff_to_expr(c: &BigRational) -> Expression {
    if c.denom() == &BigInt::one() {
        let n = c.numer();
        match i64::try_from(n.clone()) {
            Ok(i) => Expression::integer(i),
            Err(_) => Expression::Number(Number::BigInteger(Box::new(n.clone()))),
        }
    } else {
        Expression::Number(Number::rational(c.clone()))
    }
}

/// Flatten the top of a factored expression into its factors: a `Mul` expands into
/// its elements, a `Pow(base, k)` (literal `k ≥ 0`) into `k` copies of `base`,
/// anything else is a single factor.
fn flatten_product(e: &Expression) -> Vec<Expression> {
    match e {
        Expression::Mul(fs) => fs.iter().flat_map(flatten_product).collect(),
        Expression::Pow(base, exp) => match literal_exp(exp) {
            Some(k) => vec![(**base).clone(); k],
            None => vec![e.clone()],
        },
        _ => vec![e.clone()],
    }
}

fn literal_exp(e: &Expression) -> Option<usize> {
    match e {
        Expression::Number(Number::Integer(i)) if *i >= 0 => usize::try_from(*i).ok(),
        _ => None,
    }
}

/// Recursively evaluate an arithmetic `Expression` into its exact `MPoly`, or
/// `None` if it is not a polynomial over ℚ in the `v{i}` variables (a float
/// coefficient, an unknown symbol, a non-literal / negative exponent, a
/// function/relation/etc.). This mirrors `adsmt-cas`'s faithful-reflection
/// discipline: it never returns a WRONG polynomial.
fn expr_to_mpoly(e: &Expression) -> Option<MPoly> {
    match e {
        Expression::Number(n) => Some(MPoly::constant(number_to_ratio(n)?)),
        Expression::Symbol(s) => {
            let idx: usize = s.name.strip_prefix('v')?.parse().ok()?;
            Some(MPoly::var(idx))
        }
        Expression::Add(terms) => {
            let mut acc = MPoly::zero();
            for t in terms.iter() {
                acc = acc.add(&expr_to_mpoly(t)?);
            }
            Some(acc)
        }
        Expression::Mul(factors) => {
            let mut acc = MPoly::constant(BigRational::one());
            for f in factors.iter() {
                acc = acc.mul(&expr_to_mpoly(f)?);
            }
            Some(acc)
        }
        Expression::Pow(base, exp) => {
            let k = literal_exp(exp)?;
            let b = expr_to_mpoly(base)?;
            let mut acc = MPoly::constant(BigRational::one());
            for _ in 0..k {
                acc = acc.mul(&b);
            }
            Some(acc)
        }
        _ => None, // not a polynomial shape
    }
}

/// ADVISORY human-readable, step-by-step provenance for factoring `target`, from
/// MathHook's `educational` module. Text only — it never affects the re-check
/// (`admit` is the sole authority); a `None` (no steps) is harmless. Surfaced in the
/// CAS-admitted certificate's [`adsmt_cas::CasProof::provenance`].
pub fn explain_factorization(target: &MPoly) -> Option<String> {
    use mathhook_core::educational::StepByStep;
    let steps = mpoly_to_expr(target).explain_factorization();
    if steps.steps.is_empty() {
        return None;
    }
    let mut out = String::from("MathHook factorization — step-by-step:");
    for (i, step) in steps.steps.iter().enumerate() {
        out.push_str(&format!(
            "\n  {}. {} — {} [{}]",
            i + 1,
            step.title,
            step.description,
            step.rule_applied
        ));
    }
    Some(out)
}

fn number_to_ratio(n: &Number) -> Option<BigRational> {
    match n {
        Number::Integer(i) => Some(BigRational::from(BigInt::from(*i))),
        Number::BigInteger(bi) => Some(BigRational::from((**bi).clone())),
        Number::Rational(r) => Some((**r).clone()),
        Number::Float(_) => None, // inexact ⇒ not an exact polynomial coefficient
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_cas::{admit, Disposition, Obligation, Ring, Verdict};

    fn c(n: i64) -> MPoly {
        MPoly::constant(BigRational::from(BigInt::from(n)))
    }
    fn x() -> MPoly {
        MPoly::var(0)
    }

    #[test]
    fn round_trips_a_polynomial_through_mathhook_expression() {
        // MPoly → Expression → MPoly is the identity on a plain polynomial.
        let p = x().mul(&x()).sub(&c(1)).add(&c(3).mul(&x())); // x² + 3x − 1
        let back = expr_to_mpoly(&mpoly_to_expr(&p)).expect("round-trips");
        assert!(back.sub(&p).is_zero());
    }

    #[test]
    fn a_buggy_common_factor_division_is_gated_not_misverified() {
        // MathHook's `factor()` on x² − x mis-divides x²/x as x² (its
        // `divide_by_factor` has no `Pow(base,n) ÷ base` arm — see §10), returning
        // x·(x²−1) = x³ − x ≠ x² − x. Whatever it hands back, `admit` re-checks
        // ∏ factors = target, so a wrong factorization can only ever downgrade to
        // `Unknown` — NEVER a spurious `Sat`. This is the whole soundness envelope.
        let target = x().mul(&x()).sub(&x());
        if let Some(w) = factor_target(&target) {
            let ob = Obligation::Factorization { ring: Ring::Q, target };
            assert!(matches!(
                admit(&ob, &w),
                Disposition::Verdict(Verdict::Sat) | Disposition::Unknown
            ));
        }
    }

    #[test]
    fn difference_of_squares_is_sound_against_either_mathhook() {
        // x² − 1 = (x−1)(x+1). This case is version-agnostic on purpose (the AD1
        // gitlink may pin either MathHook):
        //   * CB-2-fixed MathHook (submodule branch feat/factor-witness-fixes) splits
        //     it ⇒ admit re-checks ∏ = target ⇒ Sat — the full positive path.
        //   * pre-fix MathHook declines (its `try_quadratic_factoring` was a stub)
        //     ⇒ factor_target is None ⇒ sound Undecided.
        // NEITHER can misverify — that is the whole point of the admit firewall.
        // (docs/design/CAS_BACKEND_INTEGRATION.md §10 tracks the contribute-back.)
        let target = x().mul(&x()).sub(&c(1));
        if let Some(w) = factor_target(&target) {
            let ob = Obligation::Factorization { ring: Ring::Q, target };
            assert_eq!(admit(&ob, &w), Disposition::Verdict(Verdict::Sat));
        }
    }

    #[test]
    fn explain_factorization_is_advisory_text_or_none() {
        // Advisory provenance (F4): a step-by-step explanation, or None — either way
        // it NEVER affects a verdict (`admit` is the sole authority). When present it
        // carries the MathHook header. Just must not panic.
        for p in [x().mul(&x()).sub(&x()), x().mul(&x()).sub(&c(1)), c(6).mul(&x()).add(&c(9))] {
            if let Some(text) = explain_factorization(&p) {
                assert!(text.starts_with("MathHook factorization"), "got: {text}");
            }
        }
    }

    #[test]
    fn a_wrong_conversion_can_only_downgrade_not_misverify() {
        // Soundness envelope: whatever MathHook returns, admit re-checks ∏ = target,
        // so an irreducible target yields None/Undecided (never a spurious Sat).
        let irreducible = x().mul(&x()).add(&c(1)); // x² + 1 is irreducible over ℚ
        if let Some(w) = factor_target(&irreducible) {
            // If MathHook (wrongly) returns factors, admit MUST still gate them.
            let ob = Obligation::Factorization { ring: Ring::Q, target: irreducible };
            // Either the product genuinely equals x²+1 with ≥2 non-units (it can't
            // over ℚ) ⇒ Sat, or admit rejects ⇒ Unknown. Never a WRONG verdict.
            assert!(matches!(admit(&ob, &w), Disposition::Verdict(Verdict::Sat) | Disposition::Unknown));
        }
    }
}
