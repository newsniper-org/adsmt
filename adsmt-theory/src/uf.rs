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

use std::collections::{HashMap, HashSet};

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::{Term, TermInner, Type};
use indexmap::{IndexMap, IndexSet};

use crate::trait_::{AssertResult, CheckResult, Literal, Theory};

#[derive(Default)]
pub struct Uf {
    asserted_eqs: Vec<(Term, Term)>,
    asserted_diseqs: Vec<(Term, Term)>,
    /// rc.23 (e''.1.b) — was `Vec<Term>` scanned with
    /// `iter().any(alpha_eq)` per assert.  `IndexSet<Term>`
    /// keeps insertion-deterministic order (so
    /// `truncate(snap.pos_len)` rollback semantics are
    /// preserved 1:1) but adds an O(1) `contains` probe via
    /// rc.10 hash-cons (`Term::Hash` is pointer-hash,
    /// `Term::Eq` is `Arc::ptr_eq`).
    pos_atoms: IndexSet<Term>,
    neg_atoms: IndexSet<Term>,
    /// Union-find parent map. Rebuilt at each `check`.
    parent: HashMap<Term, Term>,
    /// rc.23 (e''.1.a) — congruence universe.  Was
    /// `Vec<Term>` with `register()`'s
    /// `iter().any(kt.alpha_eq(t))` linear-scan dedup
    /// (verus-fork rc.22 retry: ~10⁴ `add_known` × ~10³
    /// `known` size = ~10⁷ alpha_eq invocations per
    /// `(check-sat)`).  `IndexSet<Term>` collapses the
    /// inner check to O(1) `contains` while preserving the
    /// indexed `for i; for j > i` pairs scan inside `close()`
    /// (via `get_index(i)`).
    known: IndexSet<Term>,
    conflict: Option<TheoryWitness>,
    scope_stack: Vec<UfSnapshot>,
    /// rc.25 (T0''') — wall-clock budget for `close()`'s
    /// congruence-closure fixpoint.  Set by the engine via
    /// `Theory::set_deadline` before each `check`.  `None` =
    /// unbudgeted (the inner loop never queries `Instant::now`).
    deadline: Option<std::time::Instant>,
    /// Set when `close()` bails out on `deadline`; turns the
    /// next `check` verdict into `Unknown` rather than a
    /// premature (and unsound) `Sat` on a half-closed universe.
    timed_out: bool,
}

#[derive(Clone, Debug)]
struct UfSnapshot {
    eqs_len: usize,
    diseqs_len: usize,
    pos_len: usize,
    neg_len: usize,
}

/// Pick the canonical representative of a class.
///
/// Preference order:
/// 1. `Const` terms (peer theories like Datatypes care about ctors)
/// 2. `Var` terms
/// 3. `App` and `Lam` terms (any of them, in source order)
///
/// Returns the index into `members`.
fn pick_representative(members: &[adsmt_core::Term]) -> usize {
    use adsmt_core::TermInner;
    for (i, t) in members.iter().enumerate() {
        if matches!(t.kind(), TermInner::Const(_)) { return i; }
    }
    for (i, t) in members.iter().enumerate() {
        if matches!(t.kind(), TermInner::Var(_)) { return i; }
    }
    0
}


impl Uf {
    fn expired(dl: Option<std::time::Instant>) -> bool {
        dl.is_some_and(|d| std::time::Instant::now() >= d)
    }

    pub fn new() -> Self { Self::default() }

    fn invalidate_cache(&mut self) {
        self.parent.clear();
        self.known.clear();
        self.conflict = None;
        self.timed_out = false;
    }

    /// Register `t` and all its sub-terms in the congruence universe.
    ///
    /// Pre-rc.23 this scanned `self.known: Vec<Term>` via
    /// `iter().any(|kt| kt.alpha_eq(t))` for dedup.  With
    /// `IndexSet<Term>` the contains-probe is O(1) on the rc.10
    /// hash-cons handles; `insert` itself is the no-op when `t`
    /// is already present, so the redundant pre-check is dropped.
    fn register(&mut self, t: &Term) {
        self.known.insert(t.clone());
        if let TermInner::App(f, x) = t.kind() {
            self.register(f);
            self.register(x);
        }
    }

    // rc.25 (e⁗.2) — `find` / `union` / `same_class` compare
    // union-find roots with `==` (which is `Arc::ptr_eq` post-rc.10
    // hash-cons), not the recursive `alpha_eq` walk.  The `parent`
    // map is keyed on hash-consed `Term`s, so every root is a
    // canonical Arc; two terms share a class iff their roots are
    // the same Arc.  The prior `alpha_eq` calls re-walked the full
    // term structure on every find-chain step + every class
    // comparison — the same hash-cons-hot-path violation as the
    // rc.21 String-key and rc.22 alpha_eq cases, one layer into
    // the congruence machinery (verus-fork rc.24 retry §5: these
    // sit under the O(N²) `close()` loop, so each pair comparison
    // paid a deep recursive `alpha_eq` that `Arc::ptr_eq` settles
    // in one pointer compare).
    fn find(&mut self, t: &Term) -> Term {
        match self.parent.get(t).cloned() {
            Some(p) if p != *t => {
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
        if ra != rb {
            self.parent.insert(ra, rb);
        }
    }

    fn same_class(&mut self, a: &Term, b: &Term) -> bool {
        self.find(a) == self.find(b)
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
        // rc.25 (T0''') — how often the closure fixpoint queries
        // the wall clock.  `Instant::now` is cheap but not free;
        // checking once per signature-pass round (not per term)
        // keeps the overhead negligible while still bounding a
        // pathological prelude to ~one extra round past the
        // deadline.  The signature pass is O(N), so a per-round
        // check is fine-grained enough.
        // (moved to Self::expired(Option<std::time::Instant>) -> bool)

        // Congruence closure via signature hashing (rc.25 e⁗.1).
        //
        // The pre-rc.25 loop was a naive O(N²·rounds) pairwise
        // scan: for every unordered pair `(ti, tj)` of known
        // App-terms it tested `same_class(f1,f2) &&
        // same_class(x1,x2) && !same_class(ti,tj)`.  On the
        // verus_smoke prelude the `known` universe reaches ~5 665
        // terms (the rc.24 ematch fix removed the
        // `collect_universe` O(N²) throttle that used to deadline-
        // fire before this loop ran on a universe that large), so
        // the pairwise scan ballooned to ~1.6 × 10⁷ pairs ×
        // multiple rounds × deep `alpha_eq` per `same_class` —
        // 81 % of cycles in the verus-fork rc.24 retry flamegraph.
        //
        // Standard congruence closure (Downey–Sethi–Tarjan /
        // Nelson–Oppen) indexes each `App(f, x)` by the signature
        // `(find(f), find(x))`.  Two App-terms are congruent iff
        // their signatures collide.  `find` returns a canonical
        // hash-consed root `Term` (Arc-unique per class), so the
        // signature key is `(Term, Term)` with O(1) `Hash`/`Eq`
        // via `Arc::ptr_eq` — no integer class-id indirection
        // needed.  Each round is one O(N) pass over the known
        // App-terms; the loop runs to union-find fixpoint.
        loop {
            if Self::expired(self.deadline) {
                self.timed_out = true;
                return;
            }
            let mut changed = false;
            // Snapshot the App-terms — the signature pass calls
            // `find` (which takes `&mut self` to path-compress),
            // so we can't hold an `iter()` borrow of `self.known`
            // across it.  Insertion order is preserved (the
            // snapshot is a `Vec` built from the `IndexSet`), so
            // the union sequence stays reproducible run-to-run.
            let known_apps: Vec<Term> = self
                .known
                .iter()
                .filter(|t| matches!(t.kind(), TermInner::App(..)))
                .cloned()
                .collect();
            let mut sig: HashMap<(Term, Term), Term> = HashMap::new();
            for t in &known_apps {
                let TermInner::App(f, x) = t.kind() else {
                    continue;
                };
                let key = (self.find(f), self.find(x));
                match sig.get(&key) {
                    Some(prev) => {
                        let prev = prev.clone();
                        // Already-congruent App with the same
                        // signature — merge their classes if not
                        // already merged.
                        if self.find(&prev) != self.find(t) {
                            self.union(&prev, t);
                            changed = true;
                        }
                    }
                    None => {
                        sig.insert(key, t.clone());
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
        // Plain Bool atom: keep the v0.1 polarity-contradiction
        // path.  rc.23 (e''.1.b) — `pos_atoms` / `neg_atoms`
        // are `IndexSet<Term>` so `contains` is O(1) (rc.10
        // hash-cons makes `Term::Hash` / `Eq` pointer-based);
        // `insert` does its own dedup so the pre-check is
        // dropped on the push side.
        if lit.polarity {
            if self.neg_atoms.contains(&lit.term) {
                let w = TheoryWitness::Opaque {
                    kind: "UF".into(),
                    notes: format!("conflicting polarities on {}", lit.term),
                };
                self.conflict = Some(w.clone());
                return AssertResult::Conflict { witness: w };
            }
            self.pos_atoms.insert(lit.term);
        } else {
            if self.pos_atoms.contains(&lit.term) {
                let w = TheoryWitness::Opaque {
                    kind: "UF".into(),
                    notes: format!("conflicting polarities on {}", lit.term),
                };
                self.conflict = Some(w.clone());
                return AssertResult::Conflict { witness: w };
            }
            self.neg_atoms.insert(lit.term);
        }
        AssertResult::Accepted
    }

    fn check(&mut self) -> CheckResult {
        if let Some(w) = &self.conflict {
            return CheckResult::Unsat { witness: w.clone() };
        }
        self.parent.clear();
        self.known.clear();
        self.timed_out = false;
        self.close();
        // rc.25 (T0''') — a deadline-aborted closure leaves the
        // congruence relation half-built; reporting `Sat` off it
        // would be unsound (a forced equality might still be
        // pending).  Surface `Unknown` so the engine treats the
        // budget as exhausted rather than trusting a partial
        // closure.
        if self.timed_out {
            return CheckResult::Unknown {
                reason: "UF congruence closure exceeded rlimit".into(),
            };
        }
        if let Some(w) = self.detect_diseq_conflict() {
            self.conflict = Some(w.clone());
            return CheckResult::Unsat { witness: w };
        }
        CheckResult::Sat
    }

    fn set_deadline(&mut self, deadline: Option<std::time::Instant>) {
        self.deadline = deadline;
    }

    fn explain(&self) -> Option<TheoryWitness> { self.conflict.clone() }

    /// Equalities that hold in the current congruence closure. v0.5
    /// surfaces both asserted equalities and class-level equalities
    /// induced by closure so peer theories (Datatypes, Arrays, BV)
    /// can absorb them via Nelson-Oppen propagation.
    fn derive_equalities(&self) -> Vec<(Term, Term)> {
        let mut out = self.asserted_eqs.clone();

        // (e⁗⁗.1) — O(1) membership dedup replacing the
        // O(out²·alpha_eq) `out.iter().any(…alpha_eq…)` probe.
        // Ground terms are Arc-canonical (rc.24 instrumentation
        // proved ptr_eq == alpha_eq on this universe), so a
        // `(Term, Term)` HashSet keyed on hash-cons identity is
        // exact.  `norm_pair` orders the two terms by their
        // `Hash` (pointer-hash post-rc.10) so `(a,b)` and `(b,a)`
        // collapse to one key — capturing the symmetric
        // `alpha_eq(&rep)&&alpha_eq(m) || alpha_eq(m)&&alpha_eq(&rep)`
        // test the old probe did. 
        let norm_pair = |a: &Term, b: &Term| -> (Term, Term) {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            use std::hash::{Hash, Hasher};
            a.hash(&mut h);
            let ha = h.finish();
            let mut h2 = std::collections::hash_map::DefaultHasher::new();
            b.hash(&mut h2);
            let hb = h2.finish();
            if ha <= hb { (a.clone(), b.clone()) } else { (b.clone(), a.clone()) }                                                                                                                                                 
        };
        let mut seen: HashSet<(Term, Term)> =
            out.iter().map(|(a, b)| norm_pair(a, b)).collect();


        // Group every known term by its union-find root (without
        // mutating the parent map — we just walk the chain).
        // rc.25 (e⁗.2) — root chain walked with `==` (Arc::ptr_eq),
        // not `alpha_eq`; same canonical-root reasoning as `find`.
        let find_root = |t: &Term| -> Term {
            let mut cur = t.clone();
            loop {
                match self.parent.get(&cur) {
                    Some(p) if *p != cur => cur = p.clone(),
                    _ => return cur,
                }
            }
        };

        // rc.23 (e''.1.c) — was `HashMap<Term, Vec<Term>>`
        // with non-deterministic `.values()` iteration order.
        // `IndexMap` keeps the insertion-order of class
        // representatives (driven by `self.known`'s
        // insertion-order, also `IndexSet` since (e''.1.a)),
        // so the emitted equalities are reproducible
        // run-to-run.
        let mut classes: IndexMap<Term, Vec<Term>> = IndexMap::new();
        for t in &self.known {
            classes.entry(find_root(t)).or_default().push(t.clone());
        }

        // v0.7: representative-based propagation. Within each
        // class, pick a *canonical* representative (preferring
        // Const-headed terms — usually constructors or named
        // literals — so peer theories like Datatypes/BV see them
        // directly) and emit equalities only from representative
        // to every other member. Linear in class size instead of
        // quadratic; matches Nelson-Oppen's standard transmission
        // form.
        
        for members in classes.values() {
            if Self::expired(self.deadline) { break; }   // (e⁗⁗.2)
            if members.len() < 2 { continue; }
            let rep_idx = pick_representative(members);
            let rep = members[rep_idx].clone();
            for (i, m) in members.iter().enumerate() {
                if i == rep_idx { continue; }
                let key = norm_pair(&rep, m);
                if seen.insert(key) {
                    out.push((rep.clone(), m.clone()));
                }
            }
        }
        out
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
