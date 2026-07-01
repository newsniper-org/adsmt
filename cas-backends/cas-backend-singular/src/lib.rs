//! # cas-backend-singular — the Singular subprocess oracle (UNTRUSTED)
//!
//! Drives [Singular](https://www.singular.uni-kl.de/) as a subprocess to *find*
//! witnesses for the two `adsmt-cas` classes it covers — ideal-membership
//! cofactors (`lift`) and factorization (`factorize`). It is **untrusted**: every
//! witness it returns is re-checked by [`adsmt_cas::admit`] in the trusted core,
//! so a bug in this crate's serialization or output parsing can only ever yield
//! `Unknown`, never a wrong verdict. See `docs/design/CAS_BACKEND_INTEGRATION.md`.
//!
//! Subprocess only (the GPL firewall, §0-6): Singular is invoked as a child
//! process via `ADSMT_SINGULAR_PATH` (or `Singular` on `PATH`); no `libsingular`
//! linkage. The ring is `char 0` with variables `v0,v1,…` named to match the
//! `MPoly` variable indices, so the output parser stays simple and exact.

use std::env;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

use adsmt_cas::poly::{MPoly, Mono};
use adsmt_cas::{
    CasBackend, CasCapability, CasClass, CasReply, Obligation, Witness, WitnessedDir,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

// ───────────────────────── polynomial serialization ─────────────────────────

fn rational_to_singular(c: &BigRational) -> String {
    if c.denom() == &BigInt::one() {
        format!("({})", c.numer())
    } else {
        format!("({}/{})", c.numer(), c.denom())
    }
}

/// `MPoly` → a Singular polynomial string over the ring `(v0,v1,…)`. Coefficients
/// are parenthesized so a negative coefficient never produces `+-`.
pub fn poly_to_singular(p: &MPoly) -> String {
    if p.is_zero() {
        return "0".to_string();
    }
    let mut terms = Vec::new();
    for (mono, coeff) in p.iter() {
        let mut parts = vec![rational_to_singular(coeff)];
        for &(v, e) in mono {
            if e == 1 {
                parts.push(format!("v{v}"));
            } else {
                parts.push(format!("v{v}^{e}"));
            }
        }
        terms.push(parts.join("*"));
    }
    terms.join("+")
}

// ──────────────────────────── polynomial parsing ────────────────────────────

fn parse_rational(s: &str) -> Option<BigRational> {
    // Strip optional surrounding parens (our serializer parenthesizes coefficients
    // to feed Singular; Singular's own output never does — either parses here).
    let s = s.trim().trim_start_matches('(').trim_end_matches(')').trim();
    match s.split_once('/') {
        Some((n, d)) => Some(BigRational::new(n.trim().parse().ok()?, d.trim().parse().ok()?)),
        None => Some(BigRational::from(s.parse::<BigInt>().ok()?)),
    }
}

/// Parse one signed term (`3/2*v0^2*v1`, `v0`, `5`, `v0^2`) into `(monomial, coeff)`.
fn parse_term(term: &str, sign: i32) -> Option<(Mono, BigRational)> {
    let mut coeff = BigRational::from(BigInt::from(sign));
    let mut mono: Mono = Vec::new();
    for factor in term.split('*') {
        let f = factor.trim();
        if f.is_empty() {
            return None;
        }
        if let Some(rest) = f.strip_prefix('v') {
            let (idx, exp) = match rest.split_once('^') {
                Some((a, b)) => (a.trim().parse::<usize>().ok()?, b.trim().parse::<u32>().ok()?),
                None => (rest.trim().parse::<usize>().ok()?, 1),
            };
            mono.push((idx, exp));
        } else {
            coeff *= parse_rational(f)?;
        }
    }
    Some((mono, coeff))
}

/// Parse a Singular `string(poly)` output (over the `v0,v1,…` ring) into an
/// `MPoly`. Untrusted input — returns `None` on any malformed shape (the trusted
/// re-check then never runs on a corrupt witness; it downgrades to `Unknown`).
pub fn parse_singular_poly(s: &str) -> Option<MPoly> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }
    if s == "0" {
        return Some(MPoly::zero());
    }
    let bytes = s.as_bytes();
    let mut items: Vec<(Mono, BigRational)> = Vec::new();
    let (mut start, mut sign) = match bytes[0] {
        b'+' => (1usize, 1i32),
        b'-' => (1, -1),
        _ => (0, 1),
    };
    let mut i = start;
    // A `+`/`-` only separates terms at PAREN DEPTH 0 — a sign INSIDE a
    // parenthesized coefficient (`(-1)`, our serializer's form) is not a separator.
    let mut depth = 0i32;
    loop {
        let at_end = i == bytes.len();
        if !at_end {
            match bytes[i] {
                b'(' => depth += 1,
                b')' => depth -= 1,
                _ => {}
            }
        }
        if at_end || ((bytes[i] == b'+' || bytes[i] == b'-') && depth == 0) {
            let term = s[start..i].trim();
            if !term.is_empty() {
                items.push(parse_term(term, sign)?);
            } else if !at_end && start != 0 {
                return None; // two signs in a row — malformed
            }
            if at_end {
                break;
            }
            sign = if bytes[i] == b'-' { -1 } else { 1 };
            start = i + 1;
        }
        i += 1;
    }
    Some(MPoly::from_monomials(items))
}

// ───────────────────────────── the backend ──────────────────────────────────

/// The Singular subprocess backend.
pub struct SingularBackend {
    path: PathBuf,
}

impl SingularBackend {
    pub fn new(path: impl Into<PathBuf>) -> Self {
        SingularBackend { path: path.into() }
    }

    /// From `$ADSMT_SINGULAR_PATH`, else `Singular` (resolved on `PATH`).
    pub fn from_env() -> Self {
        let path = env::var_os("ADSMT_SINGULAR_PATH")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("Singular"));
        SingularBackend { path }
    }

    /// Run a Singular script on stdin, capture stdout. `None` on any failure
    /// (binary missing, non-zero exit) — the caller maps that to `Error`.
    fn run(&self, script: &str) -> Option<String> {
        let mut child = Command::new(&self.path)
            .arg("-q")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .ok()?;
        child.stdin.take()?.write_all(script.as_bytes()).ok()?;
        let out = child.wait_with_output().ok()?;
        if !out.status.success() {
            return None;
        }
        Some(String::from_utf8_lossy(&out.stdout).into_owned())
    }

    fn ring_vars(nvars: usize) -> String {
        (0..nvars.max(1)).map(|i| format!("v{i}")).collect::<Vec<_>>().join(",")
    }

    fn decide_membership(&self, f: &MPoly, gens: &[MPoly]) -> CasReply {
        if gens.is_empty() {
            return CasReply::Undecided;
        }
        let nvars = gens
            .iter()
            .chain(std::iter::once(f))
            .filter_map(MPoly::max_var)
            .max()
            .map_or(1, |v| v + 1);
        let vars = Self::ring_vars(nvars);
        let gens_s = gens.iter().map(poly_to_singular).collect::<Vec<_>>().join(", ");
        let f_s = poly_to_singular(f);
        let script = format!(
            "ring r = 0,({vars}),dp;\n\
             ideal I = {gens_s};\n\
             poly f = {f_s};\n\
             \"NF:\"+string(reduce(f, groebner(I)));\n\
             matrix T = lift(I, ideal(f));\n\
             int i;\n\
             for (i=1; i<=size(I); i++) {{ \"COF:\"+string(T[i,1]); }}\n\
             quit;\n"
        );
        let Some(out) = self.run(&script) else { return CasReply::Error };

        let mut member = false;
        let mut cofactors: Vec<MPoly> = Vec::new();
        for line in out.lines() {
            let line = line.trim();
            if let Some(nf) = line.strip_prefix("NF:") {
                member = nf.trim() == "0";
            } else if let Some(c) = line.strip_prefix("COF:") {
                match parse_singular_poly(c) {
                    Some(p) => cofactors.push(p),
                    None => return CasReply::Error,
                }
            }
        }
        if !member {
            // f ∉ I — the `sat` (non-membership) direction has no short witness;
            // the design downgrades it (§3-B). We simply produce no witness.
            return CasReply::Undecided;
        }
        // Cofactor i pairs to generator i (Singular's `lift` row order = I's).
        let pairs = cofactors.into_iter().enumerate().collect();
        CasReply::Witnessed(Witness::Cofactors(pairs))
    }

    fn decide_factorization(&self, target: &MPoly) -> CasReply {
        let nvars = target.max_var().map_or(1, |v| v + 1);
        let vars = Self::ring_vars(nvars);
        let t_s = poly_to_singular(target);
        let script = format!(
            "ring r = 0,({vars}),dp;\n\
             poly p = {t_s};\n\
             list L = factorize(p);\n\
             int i;\n\
             for (i=1; i<=size(L[1]); i++) {{ \"FAC:\"+string(L[1][i])+\":\"+string(L[2][i]); }}\n\
             quit;\n"
        );
        let Some(out) = self.run(&script) else { return CasReply::Error };

        // Split the factorization `content · ∏ fᵢ^eᵢ`: gather the non-unit factors
        // (expanded by multiplicity) and the unit `content`. We then fold the
        // content into ONE non-unit factor, so every returned factor is non-unit
        // AND their product is EXACTLY the target — the two conditions
        // `adsmt_cas::admit` re-checks (a bare `[2, x-1, x+1]` would fail on the
        // unit `2`; scaling `x-1` by `2` keeps `∏ = target`).
        let mut content = MPoly::constant(BigRational::one());
        let mut factors: Vec<MPoly> = Vec::new();
        for line in out.lines() {
            let Some(rest) = line.trim().strip_prefix("FAC:") else { continue };
            let Some((ps, ms)) = rest.rsplit_once(':') else { return CasReply::Error };
            let (Some(poly), Ok(mult)) = (parse_singular_poly(ps), ms.trim().parse::<u32>()) else {
                return CasReply::Error;
            };
            if poly.is_zero() {
                return CasReply::Error;
            }
            if poly.is_unit() {
                for _ in 0..mult {
                    content = content.mul(&poly);
                }
            } else {
                for _ in 0..mult {
                    factors.push(poly.clone());
                }
            }
        }
        if factors.len() < 2 {
            // Irreducible (or one factor with the content) — no reducibility witness.
            return CasReply::Undecided;
        }
        factors[0] = factors[0].mul(&content);
        CasReply::Witnessed(Witness::Factors(factors))
    }
}

impl CasBackend for SingularBackend {
    fn name(&self) -> &'static str {
        "singular"
    }

    fn capabilities(&self) -> &[CasCapability] {
        &[
            CasCapability { class: CasClass::IdealMembership, witnessed: WitnessedDir::Unsat },
            CasCapability { class: CasClass::Factorization, witnessed: WitnessedDir::Sat },
        ]
    }

    fn decide(&self, obligation: &Obligation) -> CasReply {
        match obligation {
            Obligation::IdealMembership { f, generators, .. } => {
                self.decide_membership(f, generators)
            }
            Obligation::Factorization { target, .. } => self.decide_factorization(target),
            // Compositeness / Diophantine are PARI/native territory, not Singular.
            _ => CasReply::Undecided,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_cas::{admit, Disposition, Ring, Verdict};

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

    // ── serialization / parsing (no Singular needed) ────────────────────────
    #[test]
    fn serialize_roundtrips_through_parse() {
        let p = x().mul(&x()).mul(&y()).sub(&c(1)).add(&y().mul(&c(3))); // v0^2*v1 - 1 + 3*v1
        let s = poly_to_singular(&p);
        let back = parse_singular_poly(&s).expect("parse");
        assert!(p.sub(&back).is_zero(), "roundtrip: {p:?} vs {back:?} (str {s})");
    }

    #[test]
    fn parse_handles_singular_output_shapes() {
        assert!(parse_singular_poly("0").unwrap().is_zero());
        assert!(parse_singular_poly("v0^2-1")
            .unwrap()
            .sub(&x().mul(&x()).sub(&c(1)))
            .is_zero());
        assert!(parse_singular_poly("3/2*v0*v1-v2+5")
            .unwrap()
            .sub(&MPoly::constant(BigRational::new(BigInt::from(3), BigInt::from(2)))
                .mul(&x())
                .mul(&MPoly::var(1))
                .sub(&MPoly::var(2))
                .add(&c(5)))
            .is_zero());
        assert!(parse_singular_poly("garbage!").is_none());
    }

    // ── end-to-end (gated on Singular being installed) ──────────────────────
    fn singular_available() -> bool {
        SingularBackend::from_env().run("quit;\n").is_some()
    }

    #[test]
    fn e2e_membership_admits_unsat() {
        if !singular_available() {
            eprintln!("Singular not on PATH — skipping e2e");
            return;
        }
        let b = SingularBackend::from_env();
        // x²−1 ∈ ⟨x−1⟩ — Singular finds the cofactor, admit re-checks → Unsat.
        let ob = Obligation::IdealMembership {
            ring: Ring::Z,
            f: x().mul(&x()).sub(&c(1)),
            generators: vec![x().sub(&c(1))],
        };
        let CasReply::Witnessed(w) = b.decide(&ob) else { panic!("expected a witness") };
        assert_eq!(admit(&ob, &w), Disposition::Verdict(Verdict::Unsat));
    }

    #[test]
    fn e2e_non_membership_is_undecided() {
        if !singular_available() {
            return;
        }
        let b = SingularBackend::from_env();
        // x ∉ ⟨x²⟩ — Singular reports non-membership, no witness (sound: → Unknown).
        let ob = Obligation::IdealMembership {
            ring: Ring::Z,
            f: x(),
            generators: vec![x().mul(&x())],
        };
        assert!(matches!(b.decide(&ob), CasReply::Undecided));
    }

    #[test]
    fn e2e_factorization_admits_sat() {
        if !singular_available() {
            return;
        }
        let b = SingularBackend::from_env();
        // 2·(x²−1) is reducible — Singular factors it, content folded in, admit → Sat.
        let ob = Obligation::Factorization { ring: Ring::Q, target: c(2).mul(&x().mul(&x()).sub(&c(1))) };
        let CasReply::Witnessed(w) = b.decide(&ob) else { panic!("expected a witness") };
        assert_eq!(admit(&ob, &w), Disposition::Verdict(Verdict::Sat));
    }

    #[test]
    fn e2e_irreducible_is_undecided() {
        if !singular_available() {
            return;
        }
        let b = SingularBackend::from_env();
        // x²+1 is irreducible over ℚ — no reducibility witness (§9-B5).
        let ob = Obligation::Factorization { ring: Ring::Q, target: x().mul(&x()).add(&c(1)) };
        assert!(matches!(b.decide(&ob), CasReply::Undecided));
    }
}
