//! The lu-kb-successor **unified verdict surface** (design doc §10).
//!
//! The successor is the third face of the `adsmt-ir` CIC kernel, unifying the
//! SMT-LIB face (a 5-level precision lattice) and the typed-ASP face (a 3-valued
//! well-founded approximation pair). Its verdict must carry BOTH — as a
//! **separated product**, never a fused lattice (precision and partiality answer
//! different questions).
//!
//! These are face-agnostic VALUE types: no dependency on the solver. The solve
//! orchestration (the `adsmtc`/`adsmtr` CLI layer, which reaches both OxiZ and
//! `adsmt-ir-asp`) maps `oxiz_solver::SatLevel → Confidence` and the ASP
//! `ThreeValued → AspVerdictView` at its boundary and builds the
//! [`UnifiedVerdict`]; the collapse/meet discipline lives here so every consumer
//! shares one law.

/// How a unified verdict renders at the output boundary — the lu-kb analogue of
/// the SMT face's `OutputMode` and the ASP face's `AspOutputMode`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LuKbOutputMode {
    /// Collapse to the 3-valued `sat`/`unsat`/`unknown` (z3-compatible default).
    #[default]
    Z3Compatible,
    /// Emit the un-collapsed verdict: the 5-level SMT confidence and/or the
    /// 3-valued ASP well-founded partition, verbatim.
    Full,
}

/// The collapsed 3-valued result — the z3-compatible projection of any verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TriState {
    Sat,
    Unsat,
    Unknown,
}

impl TriState {
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            TriState::Sat => "sat",
            TriState::Unsat => "unsat",
            TriState::Unknown => "unknown",
        }
    }

    /// 3-valued **Kleene conjunction** (`Unsat` = false, `Sat` = true,
    /// `Unknown` = middle): false dominates, true is the identity, else
    /// `Unknown`. The sound combinator for a conjunction of two independent
    /// sub-problems (a refutation of either is a refutation of the whole).
    #[must_use]
    pub fn and(self, other: TriState) -> TriState {
        match (self, other) {
            (TriState::Unsat, _) | (_, TriState::Unsat) => TriState::Unsat,
            (TriState::Sat, x) | (x, TriState::Sat) => x,
            _ => TriState::Unknown,
        }
    }
}

/// The face-agnostic mirror of OxiZ's 5-level `SatLevel` — a precision lattice
/// that sharply separates a CONFIRMED verdict from a heuristic one. Only the two
/// `Definite*` poles project to a definite `sat`/`unsat`; everything else is the
/// sound `Unknown`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Confidence {
    DefiniteSat,
    PossiblySat,
    Unknown,
    PossiblyUnsat,
    DefiniteUnsat,
}

impl Confidence {
    /// Project to the 3-valued result: only a confirmed pole surfaces.
    #[must_use]
    pub fn collapse(self) -> TriState {
        match self {
            Confidence::DefiniteSat => TriState::Sat,
            Confidence::DefiniteUnsat => TriState::Unsat,
            Confidence::PossiblySat | Confidence::Unknown | Confidence::PossiblyUnsat => {
                TriState::Unknown
            }
        }
    }

    #[must_use]
    pub fn is_definite(self) -> bool {
        matches!(self, Confidence::DefiniteSat | Confidence::DefiniteUnsat)
    }

    /// The full-mode token (the un-collapsed 5-level verdict).
    #[must_use]
    pub fn as_full_str(self) -> &'static str {
        match self {
            Confidence::DefiniteSat => "definite-sat",
            Confidence::PossiblySat => "possibly-sat",
            Confidence::Unknown => "unknown",
            Confidence::PossiblyUnsat => "possibly-unsat",
            Confidence::DefiniteUnsat => "definite-unsat",
        }
    }

    /// Parse the full-mode token OxiZ emits in `--output-mode full` (and the
    /// collapsed tokens, lifted to the matching `Definite*`/`Unknown`). Returns
    /// `None` on an unrecognised string.
    #[must_use]
    pub fn parse_token(s: &str) -> Option<Confidence> {
        Some(match s.trim() {
            "definite-sat" | "sat" => Confidence::DefiniteSat,
            "possibly-sat" => Confidence::PossiblySat,
            "unknown" => Confidence::Unknown,
            "possibly-unsat" => Confidence::PossiblyUnsat,
            "definite-unsat" | "unsat" => Confidence::DefiniteUnsat,
            _ => return None,
        })
    }

    /// Combine two verdicts about the SAME obligation into the most informative
    /// SOUND verdict — the precision-meet (mirrors `SatLevel::meet`). `Unknown`
    /// is the identity; a confirmed pole dominates any unconfirmed guess
    /// (same or opposite side); two opposing unconfirmed guesses (or two
    /// contradicting confirmed poles — a bug) yield `Unknown`. Never upgrades.
    #[must_use]
    pub fn meet(self, other: Confidence) -> Confidence {
        use Confidence::{DefiniteSat, DefiniteUnsat, PossiblySat, PossiblyUnsat, Unknown};
        match (self, other) {
            (Unknown, x) | (x, Unknown) => x,
            (a, b) if a == b => a,
            (DefiniteSat, PossiblySat | PossiblyUnsat)
            | (PossiblySat | PossiblyUnsat, DefiniteSat) => DefiniteSat,
            (DefiniteUnsat, PossiblySat | PossiblyUnsat)
            | (PossiblySat | PossiblyUnsat, DefiniteUnsat) => DefiniteUnsat,
            (PossiblySat, PossiblyUnsat) | (PossiblyUnsat, PossiblySat) => Unknown,
            (DefiniteSat, DefiniteUnsat) | (DefiniteUnsat, DefiniteSat) => Unknown,
            _ => unreachable!("all same-level pairs handled by the `a == b` arm"),
        }
    }
}

/// The ASP half of a unified verdict — the typed-ASP face's outcome rendered to
/// surface strings (no dependency on `adsmt-ir-asp`'s internal `Atom`/`Solution`
/// types; the orchestration converts at its boundary). The three atom sets are
/// the well-founded model partition (true = `L*`, false = `B\U*`, undefined =
/// `U*\L*`); `consistent` mirrors `Solution.consistent`; `stable_count` is the
/// number of enumerated stable models when available (`None` = over-budget /
/// partial / stratified).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct AspVerdictView {
    pub consistent: bool,
    pub true_atoms: Vec<String>,
    pub false_atoms: Vec<String>,
    pub undefined_atoms: Vec<String>,
    pub stable_count: Option<usize>,
}

impl AspVerdictView {
    /// The collapsed 3-valued projection of the ASP outcome: `Unsat` iff no
    /// answer set exists (`!consistent` with the model space fully decided),
    /// `Sat` iff at least one stable model is known, else `Unknown` (a partial
    /// well-founded answer that did not decide consistency).
    #[must_use]
    pub fn collapse(&self) -> TriState {
        match (self.consistent, self.stable_count) {
            (true, Some(n)) if n > 0 => TriState::Sat,
            // a fully-decided model space with no answer set
            (false, Some(_)) => TriState::Unsat,
            // partial (over-budget well-founded only): cannot certify either way
            _ => TriState::Unknown,
        }
    }
}

/// The lu-kb-successor verdict — a SEPARATED PRODUCT of the two faces' outcomes
/// (design doc §10.1). At least one side is `Some`. The z3-compatible projection
/// is the `meet` of the present sides' collapses; `Full` mode renders both
/// verbatim.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct UnifiedVerdict {
    /// The SMT face's 5-level confidence, when SMT obligations were solved.
    pub smt: Option<Confidence>,
    /// The typed-ASP face's outcome, when rule obligations were solved.
    pub asp: Option<AspVerdictView>,
}

impl UnifiedVerdict {
    #[must_use]
    pub fn smt(c: Confidence) -> Self {
        UnifiedVerdict { smt: Some(c), asp: None }
    }
    #[must_use]
    pub fn asp(v: AspVerdictView) -> Self {
        UnifiedVerdict { smt: None, asp: Some(v) }
    }

    /// The z3-compatible 3-valued projection: the **3-valued Kleene conjunction**
    /// of the present sides' collapses. A hybrid program's SMT half and ASP half
    /// are different sub-problems whose conjunction is the whole, so this is an
    /// AND (not a `meet` — that combines verdicts about the SAME formula): `Unsat`
    /// on EITHER side makes the whole `Unsat` (a refutation kills it — always
    /// sound), `Sat` is the identity (an absent side imposes no constraint), and
    /// otherwise `Unknown`. NOTE: a both-`Sat` hybrid is reported `Sat` under the
    /// assumption the faces are jointly satisfiable (the common disjoint-atom
    /// case); a shared-atom joint-model check is the §10.2 refinement.
    #[must_use]
    pub fn collapse(&self) -> TriState {
        // absent side = the conjunction identity (`Sat`)
        let smt = self.smt.map_or(TriState::Sat, Confidence::collapse);
        let asp = self.asp.as_ref().map_or(TriState::Sat, AspVerdictView::collapse);
        TriState::and(smt, asp)
    }

    /// Render per the output mode: the collapsed `sat`/`unsat`/`unknown`
    /// (z3-compatible) or both un-collapsed sub-verdicts (`Full`).
    #[must_use]
    pub fn render(&self, mode: LuKbOutputMode) -> String {
        match mode {
            LuKbOutputMode::Z3Compatible => self.collapse().as_str().to_string(),
            LuKbOutputMode::Full => {
                let mut parts = Vec::new();
                if let Some(c) = self.smt {
                    parts.push(format!("smt {}", c.as_full_str()));
                }
                if let Some(a) = &self.asp {
                    parts.push(format!(
                        "asp true={{{}}} false={{{}}} undefined={{{}}}",
                        a.true_atoms.join(" "),
                        a.false_atoms.join(" "),
                        a.undefined_atoms.join(" "),
                    ));
                }
                if parts.is_empty() {
                    "unknown".to_string()
                } else {
                    parts.join(" | ")
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Confidence::{DefiniteSat, DefiniteUnsat, PossiblySat, PossiblyUnsat, Unknown};

    #[test]
    fn confidence_collapse_only_definite() {
        assert_eq!(DefiniteSat.collapse(), TriState::Sat);
        assert_eq!(DefiniteUnsat.collapse(), TriState::Unsat);
        assert_eq!(PossiblySat.collapse(), TriState::Unknown);
        assert_eq!(PossiblyUnsat.collapse(), TriState::Unknown);
        assert_eq!(Unknown.collapse(), TriState::Unknown);
    }

    #[test]
    fn confidence_meet_matches_satlevel_law() {
        assert_eq!(Unknown.meet(DefiniteSat), DefiniteSat); // identity
        assert_eq!(DefiniteSat.meet(PossiblyUnsat), DefiniteSat); // pole dominates
        assert_eq!(PossiblySat.meet(PossiblyUnsat), Unknown); // opposing guesses
        assert_eq!(DefiniteSat.meet(DefiniteUnsat), Unknown); // contradiction → Unknown
        for a in [DefiniteSat, PossiblySat, Unknown, PossiblyUnsat, DefiniteUnsat] {
            for b in [DefiniteSat, PossiblySat, Unknown, PossiblyUnsat, DefiniteUnsat] {
                assert_eq!(a.meet(b), b.meet(a), "commutative {a:?} {b:?}");
            }
        }
    }

    #[test]
    fn parse_token_roundtrips_and_lifts() {
        for c in [DefiniteSat, PossiblySat, Unknown, PossiblyUnsat, DefiniteUnsat] {
            assert_eq!(Confidence::parse_token(c.as_full_str()), Some(c));
        }
        assert_eq!(Confidence::parse_token("sat"), Some(DefiniteSat));
        assert_eq!(Confidence::parse_token("unsat"), Some(DefiniteUnsat));
        assert_eq!(Confidence::parse_token("bogus"), None);
    }

    #[test]
    fn unified_collapse_is_meet_of_sides() {
        // SMT confirmed-unsat ⊓ ASP sat ⇒ Unsat (a conjunction killed on one side)
        let v = UnifiedVerdict {
            smt: Some(DefiniteUnsat),
            asp: Some(AspVerdictView { consistent: true, stable_count: Some(1), ..Default::default() }),
        };
        assert_eq!(v.collapse(), TriState::Unsat);
        // both sat ⇒ Sat
        let v2 = UnifiedVerdict {
            smt: Some(DefiniteSat),
            asp: Some(AspVerdictView { consistent: true, stable_count: Some(2), ..Default::default() }),
        };
        assert_eq!(v2.collapse(), TriState::Sat);
        // SMT possibly-sat (unconfirmed) alone ⇒ Unknown
        assert_eq!(UnifiedVerdict::smt(PossiblySat).collapse(), TriState::Unknown);
    }

    #[test]
    fn full_render_keeps_both_sides() {
        let v = UnifiedVerdict {
            smt: Some(PossiblySat),
            asp: Some(AspVerdictView {
                consistent: true,
                true_atoms: vec!["p".into()],
                false_atoms: vec!["q".into()],
                undefined_atoms: vec!["r".into()],
                stable_count: None,
            }),
        };
        let full = v.render(LuKbOutputMode::Full);
        assert!(full.contains("possibly-sat") && full.contains("true={p}") && full.contains("undefined={r}"));
        assert_eq!(v.render(LuKbOutputMode::Z3Compatible), "unknown");
    }
}
