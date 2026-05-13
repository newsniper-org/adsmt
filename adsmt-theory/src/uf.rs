//! Uninterpreted functions theory.
//!
//! v0.3 adds congruence closure: when `a = b` is asserted, the
//! theory unifies their union-find classes and propagates congruence
//! over applied terms (`f a` and `f b` merge when their components
//! merge). Disequalities `¬(a = b)` are recorded and surfaced as
//! conflicts if closure later forces them equal.
//!
//! v0.1 polarity-contradiction handling on plain Bool atoms is
//! preserved as a fast path.

use std::collections::HashMap;

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::{Term, Type};

use crate::trait_::{AssertResult, CheckResult, Literal, Theory};

pub struct Uf {
    asserted_eqs: Vec<(Term, Term)>,
    asserted_diseqs: Vec<(Term, Term)>,
    pos_atoms: Vec<Term>,
    neg_atoms: Vec<Term>,
    /// Union-find parent map. Rebuilt at each `check`.
    parent: HashMap<Term, Term>,
    /// All terms registered for congruence reasoning. Rebuilt at
    /// each `check`.
    known: Vec<Term>,
    conflict: Option<TheoryWitness>,
    scope_stack: Vec<UfSnapshot>,
}

#[derive(Clone, Debug)]
struct UfSnapshot {
    eqs_len: usize,
    diseqs_len: usize,
    pos_len: usize,
    neg_len: usize,
}

impl Default for Uf {
    fn default() -> Self {
        Self {
            asserted_eqs: Vec::new(),
            asserted_diseqs: Vec::new(),
            pos_atoms: Vec::new(),
            neg_atoms: Vec::new(),
            parent: HashMap::new(),
            known: Vec::new(),
            conflict: None,
            scope_stack: Vec::new(),
        }
    }
}

impl Uf {
    pub fn new() -> Self { Self::default() }

    fn contains_alpha(set: &[Term], t: &Term) -> bool {
        set.iter().any(|x| x.alpha_eq(t))
    }

    fn invalidate_cache(&mut self) {
        self.parent.clear();
        self.known.clear();
        self.conflict = None;
    }

    /// Register `t` and all its sub-terms in the congruence universe.
    fn register(&mut self, t: &Term) {
        if !self.known.iter().any(|kt| kt.alpha_eq(t)) {
            self.known.push(t.clone());
        }
        if let Term::App(f, x) = t {
            self.register(f);
            self.register(x);
        }
    }

    fn find(&mut self, t: &Term) -> Term {
        match self.parent.get(t).cloned() {
            Some(p) if !p.alpha_eq(t) => {
                let root = self.find(&p);
                self.parent.insert(t.clone(), root.clone());
                root
            }
            _ => t.clone(),
        }
    }

    fn union(&mut self, a: &Term, b: &Term) {
        let ra = self.find(a);
        let rb = self.find(b);
        if !ra.alpha_eq(&rb) {
            self.parent.insert(ra, rb);
        }
    }

    fn same_class(&mut self, a: &Term, b: &Term) -> bool {
        self.find(a).alpha_eq(&self.find(b))
    }

    /// Run congruence-closure to fixpoint over current eqs.
    fn close(&mut self) {
        // Register every relevant term first.
        let eqs = self.asserted_eqs.clone();
        let diseqs = self.asserted_diseqs.clone();
        for (a, b) in &eqs {
            self.register(a);
            self.register(b);
        }
        for (a, b) in &diseqs {
            self.register(a);
            self.register(b);
        }
        // Seed union-find with asserted equalities.
        for (a, b) in &eqs {
            self.union(a, b);
        }
        // Congruence closure: iterate until fixpoint.
        loop {
            let mut changed = false;
            let snapshot = self.known.clone();
            for i in 0..snapshot.len() {
                for j in (i + 1)..snapshot.len() {
                    let (ti, tj) = (&snapshot[i], &snapshot[j]);
                    if let (Term::App(f1, x1), Term::App(f2, x2)) = (ti, tj) {
                        let f1c = (**f1).clone();
                        let x1c = (**x1).clone();
                        let f2c = (**f2).clone();
                        let x2c = (**x2).clone();
                        if self.same_class(&f1c, &f2c)
                            && self.same_class(&x1c, &x2c)
                            && !self.same_class(ti, tj)
                        {
                            let (a, b) = (ti.clone(), tj.clone());
                            self.union(&a, &b);
                            changed = true;
                        }
                    }
                }
            }
            if !changed { break; }
        }
    }

    /// After closure, check whether any asserted disequality is
    /// violated.
    fn detect_diseq_conflict(&mut self) -> Option<TheoryWitness> {
        let diseqs = self.asserted_diseqs.clone();
        for (a, b) in &diseqs {
            if self.same_class(a, b) {
                return Some(TheoryWitness::Opaque {
                    kind: "UF".into(),
                    notes: format!(
                        "congruence closure forces {a} = {b}, but disequality was asserted"
                    ),
                });
            }
        }
        None
    }
}

impl Theory for Uf {
    fn name(&self) -> &'static str { "UF" }

    fn handles_sort(&self, _: &Type) -> bool { true }

    fn assert(&mut self, lit: Literal) -> AssertResult {
        // Equality / disequality recognition: route into the
        // congruence-closure state.
        if let Some((a, b)) = lit.term.dest_eq() {
            self.invalidate_cache();
            if lit.polarity {
                self.asserted_eqs.push((a, b));
            } else {
                self.asserted_diseqs.push((a, b));
            }
            return AssertResult::Accepted;
        }
        // Plain Bool atom: keep the v0.1 polarity-contradiction path.
        if lit.polarity {
            if Self::contains_alpha(&self.neg_atoms, &lit.term) {
                let w = TheoryWitness::Opaque {
                    kind: "UF".into(),
                    notes: format!("conflicting polarities on {}", lit.term),
                };
                self.conflict = Some(w.clone());
                return AssertResult::Conflict { witness: w };
            }
            if !Self::contains_alpha(&self.pos_atoms, &lit.term) {
                self.pos_atoms.push(lit.term);
            }
        } else {
            if Self::contains_alpha(&self.pos_atoms, &lit.term) {
                let w = TheoryWitness::Opaque {
                    kind: "UF".into(),
                    notes: format!("conflicting polarities on {}", lit.term),
                };
                self.conflict = Some(w.clone());
                return AssertResult::Conflict { witness: w };
            }
            if !Self::contains_alpha(&self.neg_atoms, &lit.term) {
                self.neg_atoms.push(lit.term);
            }
        }
        AssertResult::Accepted
    }

    fn check(&mut self) -> CheckResult {
        if let Some(w) = &self.conflict {
            return CheckResult::Unsat { witness: w.clone() };
        }
        self.parent.clear();
        self.known.clear();
        self.close();
        if let Some(w) = self.detect_diseq_conflict() {
            self.conflict = Some(w.clone());
            return CheckResult::Unsat { witness: w };
        }
        CheckResult::Sat
    }

    fn explain(&self) -> Option<TheoryWitness> { self.conflict.clone() }

    /// Equalities that hold in the current congruence closure, beyond
    /// what was asserted. Theories like Arrays consume these to share
    /// reasoning at sort boundaries (sec 26).
    fn derive_equalities(&self) -> Vec<(Term, Term)> {
        // v0.3 alpha: surface the *asserted* equalities only. Derived
        // congruences (from closure) plug in once Nelson-Oppen is on.
        self.asserted_eqs.clone()
    }

    fn derive_disequalities(&self) -> Vec<(Term, Term)> {
        self.asserted_diseqs.clone()
    }

    fn cardinality_witness(&self, sort: &Type) -> PoliteWitness {
        PoliteWitness { sort: format!("{sort}"), upper_bound: None }
    }

    fn push(&mut self) {
        self.scope_stack.push(UfSnapshot {
            eqs_len: self.asserted_eqs.len(),
            diseqs_len: self.asserted_diseqs.len(),
            pos_len: self.pos_atoms.len(),
            neg_len: self.neg_atoms.len(),
        });
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if let Some(snap) = self.scope_stack.pop() {
                self.asserted_eqs.truncate(snap.eqs_len);
                self.asserted_diseqs.truncate(snap.diseqs_len);
                self.pos_atoms.truncate(snap.pos_len);
                self.neg_atoms.truncate(snap.neg_len);
            }
        }
        self.invalidate_cache();
    }

    fn reset(&mut self) {
        self.asserted_eqs.clear();
        self.asserted_diseqs.clear();
        self.pos_atoms.clear();
        self.neg_atoms.clear();
        self.invalidate_cache();
        self.scope_stack.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Term, Type};

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    fn a() -> Term { Term::var("a", int_()) }
    fn b() -> Term { Term::var("b", int_()) }
    fn c() -> Term { Term::var("c", int_()) }

    /// `f : Int -> Int`
    fn f_term() -> Term {
        Term::const_("f", Type::fun(int_(), int_()).unwrap())
    }

    #[test]
    fn empty_state_is_sat() {
        let mut uf = Uf::new();
        assert!(matches!(uf.check(), CheckResult::Sat));
    }

    #[test]
    fn detects_polarity_conflict_on_bool_atom() {
        let mut uf = Uf::new();
        let p = Term::var("p", Type::bool_());
        assert!(matches!(uf.assert(Literal::positive(p.clone()).unwrap()), AssertResult::Accepted));
        assert!(matches!(
            uf.assert(Literal::negative(p).unwrap()),
            AssertResult::Conflict { .. }
        ));
        assert!(matches!(uf.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn equality_alone_is_sat() {
        let mut uf = Uf::new();
        let eq = Term::mk_eq(a(), b()).unwrap();
        uf.assert(Literal::positive(eq).unwrap());
        assert!(matches!(uf.check(), CheckResult::Sat));
    }

    #[test]
    fn transitive_equality_unifies_classes() {
        // a = b, b = c → a, b, c in one class.
        let mut uf = Uf::new();
        uf.assert(Literal::positive(Term::mk_eq(a(), b()).unwrap()).unwrap());
        uf.assert(Literal::positive(Term::mk_eq(b(), c()).unwrap()).unwrap());
        assert!(matches!(uf.check(), CheckResult::Sat));
        assert!(uf.same_class(&a(), &c()));
    }

    #[test]
    fn transitive_equality_with_contradicting_diseq_is_unsat() {
        // a = b, b = c, a ≠ c → unsat (congruence forces a ≡ c).
        let mut uf = Uf::new();
        uf.assert(Literal::positive(Term::mk_eq(a(), b()).unwrap()).unwrap());
        uf.assert(Literal::positive(Term::mk_eq(b(), c()).unwrap()).unwrap());
        uf.assert(Literal::negative(Term::mk_eq(a(), c()).unwrap()).unwrap());
        assert!(matches!(uf.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn congruence_propagates_through_applications() {
        // a = b, f a ≠ f b → unsat.
        let mut uf = Uf::new();
        let fa = Term::app(f_term(), a()).unwrap();
        let fb = Term::app(f_term(), b()).unwrap();
        uf.assert(Literal::positive(Term::mk_eq(a(), b()).unwrap()).unwrap());
        uf.assert(Literal::negative(Term::mk_eq(fa, fb).unwrap()).unwrap());
        assert!(matches!(uf.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn unrelated_terms_stay_separate() {
        // a = b alone — f a and f c stay distinct.
        let mut uf = Uf::new();
        let fa = Term::app(f_term(), a()).unwrap();
        let fc = Term::app(f_term(), c()).unwrap();
        uf.assert(Literal::positive(Term::mk_eq(a(), b()).unwrap()).unwrap());
        uf.assert(Literal::negative(Term::mk_eq(fa, fc).unwrap()).unwrap());
        assert!(matches!(uf.check(), CheckResult::Sat));
    }

    #[test]
    fn nested_congruence_two_hops() {
        // a = b, b = c, f a ≠ f c → unsat (f a ≡ f b ≡ f c).
        let mut uf = Uf::new();
        let fa = Term::app(f_term(), a()).unwrap();
        let fc = Term::app(f_term(), c()).unwrap();
        uf.assert(Literal::positive(Term::mk_eq(a(), b()).unwrap()).unwrap());
        uf.assert(Literal::positive(Term::mk_eq(b(), c()).unwrap()).unwrap());
        uf.assert(Literal::negative(Term::mk_eq(fa, fc).unwrap()).unwrap());
        assert!(matches!(uf.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn push_pop_restores_equality_state() {
        let mut uf = Uf::new();
        uf.assert(Literal::positive(Term::mk_eq(a(), b()).unwrap()).unwrap());
        uf.push();
        uf.assert(Literal::negative(Term::mk_eq(a(), b()).unwrap()).unwrap());
        assert!(matches!(uf.check(), CheckResult::Unsat { .. }));
        uf.pop(1);
        assert!(matches!(uf.check(), CheckResult::Sat));
    }

    #[test]
    fn reset_clears_everything() {
        let mut uf = Uf::new();
        uf.assert(Literal::positive(Term::mk_eq(a(), b()).unwrap()).unwrap());
        uf.assert(Literal::negative(Term::mk_eq(a(), b()).unwrap()).unwrap());
        assert!(matches!(uf.check(), CheckResult::Unsat { .. }));
        uf.reset();
        assert!(matches!(uf.check(), CheckResult::Sat));
    }
}
