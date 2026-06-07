use std::fmt;

use crate::term::Term;

/// A proven sequent `Γ ⊢ φ`.
///
/// Constructable only via the kernel rules in [`crate::rule`]. Outside
/// `adsmt-core` no code can produce a `Theorem` from raw data, so the
/// rule module is the trusted kernel boundary.
#[derive(Clone, Debug)]
pub struct Theorem {
    hyps: Vec<Term>,
    concl: Term,
}

impl Theorem {
    pub(crate) fn new(hyps: Vec<Term>, concl: Term) -> Self {
        Self { hyps, concl }
    }

    pub fn hyps(&self) -> &[Term] {
        &self.hyps
    }

    pub fn concl(&self) -> &Term {
        &self.concl
    }
}

/// Hypothesis-set union with α-equivalence as the equality predicate.
///
/// rc.24 (e'''.3) — the dedup membership test routes through a
/// `HashSet<Term>` scratch instead of the prior
/// `out.iter().any(|x| x.alpha_eq(h))` linear scan.  `Term`'s
/// rc.10 hash-cons makes the probe O(1) (`Hash` pointer-hash,
/// `Eq` `Arc::ptr_eq`); on closed hypothesis terms α-equality
/// reduces to structural equality on canonical forms, so the
/// set membership and the alpha_eq scan agree.  The output
/// `Vec` is still built in `a`-then-new-`b` order, so the
/// sequent hypothesis ordering is unchanged.
pub(crate) fn union_hyps(a: &[Term], b: &[Term]) -> Vec<Term> {
    use std::collections::HashSet;
    let mut out: Vec<Term> = a.to_vec();
    let mut seen: HashSet<Term> = a.iter().cloned().collect();
    for h in b {
        if seen.insert(h.clone()) {
            out.push(h.clone());
        }
    }
    out
}

/// Difference: hypotheses of `a` excluding any α-equivalent to `target`.
pub(crate) fn remove_hyp(a: &[Term], target: &Term) -> Vec<Term> {
    a.iter().filter(|h| !h.alpha_eq(target)).cloned().collect()
}

impl fmt::Display for Theorem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, h) in self.hyps.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{h}")?;
        }
        if self.hyps.is_empty() {
            write!(f, "⊢ {}", self.concl)
        } else {
            write!(f, " ⊢ {}", self.concl)
        }
    }
}
