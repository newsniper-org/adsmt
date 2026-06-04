//! Theory of arrays.
//!
//! **Read-over-write reasoning** for `(select (store a i v) j)`:
//! - same-index (`i = j`): reduces to `v`
//! - different-index (`i ≠ j`): reduces to `(select a j)` whenever
//!   the disequality `i ≠ j` is locally known to the theory
//!
//! The theory tracks two local channels:
//! - **derived equalities** — surfaced to UF / other theories via
//!   the Nelson-Oppen `derive_equalities` hook
//! - **local disequalities** — collected from negative-polarity
//!   `(= i j)` assertions and used to fire the different-index
//!   rewrite without depending on UF's disequality propagation
//!
//! **Extensionality** (`a ≠ b → ∃k. select a k ≠ select b k`) is
//! recorded as a derivation hook that surfaces `(diff a b)` style
//! witness atoms when an array-disequality is asserted; the
//! quantifier-elimination pipeline above the theory layer then
//! instantiates the witness.
//!
//! Built-in symbols:
//! - `select : (Array I E) -> I -> E`
//! - `store  : (Array I E) -> I -> E -> (Array I E)`
//! - `diff   : (Array I E) -> (Array I E) -> I` (extensionality witness)

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::{Term, TermInner, Type};

use crate::trait_::{AssertResult, CheckResult, Literal, Theory};

#[derive(Default)]
pub struct Arrays {
    /// Equalities the array theory has derived and wants to share with
    /// other theories via Nelson-Oppen propagation. Read-over-write
    /// conclusions land here.
    derived_eqs: Vec<(Term, Term)>,
    /// Locally known disequalities — unordered pairs `(a, b)` where
    /// `a ≠ b` was asserted (typically the negative-polarity of an
    /// equality literal). Used to fire the different-index
    /// read-over-write rewrite without a back-channel from UF.
    local_disequalities: Vec<(Term, Term)>,
    /// Pending extensionality witnesses: when `a ≠ b` was asserted
    /// at the array-sort level, a `(diff a b)` index witness is
    /// queued so the quantifier loop above can route it as an
    /// instantiation candidate.
    pending_extensionality: Vec<(Term, Term)>,
    conflict: Option<TheoryWitness>,
    scope_stack: Vec<ArraysScope>,
}

/// Per-push snapshot — used by `pop` to truncate the relevant
/// vectors atomically.
#[derive(Clone, Copy, Default, Debug)]
struct ArraysScope {
    derived_eqs_len: usize,
    local_diseq_len: usize,
    pending_ext_len: usize,
}

impl Arrays {
    pub fn new() -> Self { Self::default() }

    /// Destructure `(select arr idx)`.
    fn dest_select(t: &Term) -> Option<(Term, Term)> {
        if let TermInner::App(outer, idx) = t.kind()
            && let TermInner::App(head, arr) = outer.kind()
            && let TermInner::Const(c) = head.kind()
            && c.name == "select"
        {
            return Some((arr.clone(), idx.clone()));
        }
        None
    }

    /// Destructure `(store arr idx val)`.
    fn dest_store(t: &Term) -> Option<(Term, Term, Term)> {
        if let TermInner::App(outer3, val) = t.kind()
            && let TermInner::App(outer2, idx) = outer3.kind()
            && let TermInner::App(head, arr) = outer2.kind()
            && let TermInner::Const(c) = head.kind()
            && c.name == "store"
        {
            return Some((arr.clone(), idx.clone(), val.clone()));
        }
        None
    }

    /// Reduce one read-over-write step on the term `t`, if
    /// applicable. Returns `Some((reduced, side_condition))` where
    /// `side_condition` is the equality (same-index case) or
    /// disequality (different-index case) between the store and
    /// select indices; the caller must already have established it.
    /// Returns `None` when no rewrite applies — including the
    /// different-index case if `disequalities` does not contain
    /// `(i, j)` or `(j, i)`.
    fn read_over_write(t: &Term, disequalities: &[(Term, Term)]) -> Option<(Term, Term)> {
        let (arr, j) = Self::dest_select(t)?;
        let (a, i, v) = Self::dest_store(&arr)?;
        if i.alpha_eq(&j) {
            // (select (store a i v) i) = v
            return Some((v, Term::mk_eq(i.clone(), j).ok()?));
        }
        if Self::pair_known_disequal(&i, &j, disequalities) {
            // (select (store a i v) j) → (select a j) when i ≠ j
            return Some((Self::mk_select_term(&a, &j)?, Term::mk_eq(i, j).ok()?));
        }
        let _ = v;
        None
    }

    /// v0.19 C.3 — store-store normalisation.
    ///
    /// Two rewriting rules over nested stores:
    ///
    /// 1. **Same-index dominance** (no side condition):
    ///    `(store (store a i v1) i v2)` ⇒ `(store a i v2)`.
    ///    The outer write dominates; the inner is dead.
    ///
    /// 2. **Disequal-index commutativity** (requires `i ≠ j` in
    ///    `disequalities`):
    ///    `(store (store a i v1) j v2)` ⇒
    ///    `(store (store a j v2) i v1)`. Reordering writes that
    ///    target distinct cells produces an equivalent array
    ///    expression — useful as a canonicalisation step for
    ///    downstream EUF / equality propagation, even though
    ///    both sides are equal as arrays.
    ///
    /// Returns `Some((normalised, side_condition))` when a rule
    /// fires; `None` otherwise. The side condition is the
    /// equality (rule 1) or disequality (rule 2) the caller
    /// must have already established.
    pub(crate) fn store_store_normalize(
        t: &Term,
        disequalities: &[(Term, Term)],
    ) -> Option<(Term, Term)> {
        let (outer_a, j, v2) = Self::dest_store(t)?;
        let (inner_a, i, v1) = Self::dest_store(&outer_a)?;
        if i.alpha_eq(&j) {
            // Same-index dominance.
            let rewritten =
                Self::mk_store_term_like(t, &inner_a, &i, &v2)?;
            return Some((rewritten, Term::mk_eq(i, j).ok()?));
        }
        if Self::pair_known_disequal(&i, &j, disequalities) {
            // Disequal-index commutativity — swap order.
            let inner_swapped =
                Self::mk_store_term_like(t, &inner_a, &j, &v2)?;
            let rewritten =
                Self::mk_store_term_like(t, &inner_swapped, &i, &v1)?;
            // The witness is the disequality.
            let diseq = Term::mk_eq(i, j).ok()?;
            return Some((rewritten, diseq));
        }
        None
    }

    /// Build `(store arr idx val)` reusing the store-op constant
    /// of an existing nested-store term. Type-safe because the
    /// existing term already type-checks.
    ///
    /// Caller supplies `template` — any (store ...) term sharing
    /// the same array sort. We extract its head constant
    /// (`store`) and re-apply with the new args.
    fn mk_store_term_like(
        template: &Term,
        arr: &Term,
        idx: &Term,
        val: &Term,
    ) -> Option<Term> {
        // template = App(App(App(store_const, _), _), _).
        let outer = template;
        let TermInner::App(level2, _) = outer.kind() else { return None; };
        let TermInner::App(level1, _) = level2.kind() else { return None; };
        let TermInner::App(store_op, _) = level1.kind() else { return None; };
        let head: Term = store_op.clone();
        let with_arr = Term::app(head, arr.clone()).ok()?;
        let with_idx = Term::app(with_arr, idx.clone()).ok()?;
        Term::app(with_idx, val.clone()).ok()
    }

    /// Predicate: `(a, b)` (in any order) appears in `pairs` modulo
    /// α-equivalence.
    fn pair_known_disequal(a: &Term, b: &Term, pairs: &[(Term, Term)]) -> bool {
        pairs.iter().any(|(p, q)| {
            (p.alpha_eq(a) && q.alpha_eq(b)) || (p.alpha_eq(b) && q.alpha_eq(a))
        })
    }

    /// Build `(select arr idx)` reusing the surrounding term's typing.
    fn mk_select_term(arr: &Term, idx: &Term) -> Option<Term> {
        let arr_ty = arr.type_of();
        let idx_ty = idx.type_of();
        let elem_ty = arr_ty.dest_fun().map(|(_, e)| e).unwrap_or(idx_ty.clone());
        let sel_ty = Type::fun(
            arr_ty.clone(),
            Type::fun(idx_ty, elem_ty).ok()?,
        )
        .ok()?;
        let sel = Term::const_("select", sel_ty);
        Term::app(Term::app(sel, arr.clone()).ok()?, idx.clone()).ok()
    }

    /// True iff `ty` is an `Array...`-named sort.
    fn is_array_sort(ty: &Type) -> bool {
        ty.to_string().starts_with("Array")
    }
}

impl Theory for Arrays {
    fn name(&self) -> &'static str { "Arrays" }

    fn handles_sort(&self, ty: &Type) -> bool {
        ty.to_string().starts_with("Array")
    }

    fn assert(&mut self, lit: Literal) -> AssertResult {
        let Some((lhs, rhs)) = lit.term.dest_eq() else {
            return AssertResult::Ignored;
        };

        // Negative polarity: route by operand sort.
        //
        // * **Element-sort disequalities** (e.g. `i ≠ j`) go into
        //   `local_disequalities` because they unlock the
        //   different-index branch of `read-over-write`.
        // * **Array-sort disequalities** (e.g. `a ≠ b`) bypass
        //   `local_disequalities` and queue an extensionality witness
        //   `(diff a b)` instead. They cannot drive different-index
        //   reasoning directly; only after the quantifier layer
        //   instantiates the witness does the resulting *element*-
        //   level disequality (`select(a, d) ≠ select(b, d)`) re-enter
        //   the assert path and join `local_disequalities`.
        //
        // Skip the trivial `t ≠ t` case (should be impossible upstream
        // but defensive).
        if !lit.polarity {
            if !lhs.alpha_eq(&rhs) {
                if Self::is_array_sort(&lhs.type_of()) {
                    let ext_known = Self::pair_known_disequal(
                        &lhs,
                        &rhs,
                        &self.pending_extensionality,
                    );
                    if !ext_known {
                        self.pending_extensionality.push((lhs.clone(), rhs.clone()));
                    }
                } else {
                    let known =
                        Self::pair_known_disequal(&lhs, &rhs, &self.local_disequalities);
                    if !known {
                        self.local_disequalities.push((lhs.clone(), rhs.clone()));
                    }
                }
            }
            return AssertResult::Accepted;
        }

        // Positive polarity: try read-over-write rewriting on both
        // sides. Same-index always fires; different-index requires a
        // matching local disequality.
        if let Some((reduced, _side)) = Self::read_over_write(&lhs, &self.local_disequalities) {
            self.derived_eqs.push((reduced, rhs.clone()));
        }
        if let Some((reduced, _side)) = Self::read_over_write(&rhs, &self.local_disequalities) {
            self.derived_eqs.push((lhs.clone(), reduced));
        }
        // v0.21 follow-up — also try store-store normalisation
        // (Arrays.C.3). Surfaces normalised nested-store equalities
        // to the polite combination so EUF can equate
        // `(store (store a i v₁) i v₂)` with `(store a i v₂)`.
        if let Some((normalised, _witness)) =
            Self::store_store_normalize(&lhs, &self.local_disequalities)
        {
            self.derived_eqs.push((normalised, rhs.clone()));
        }
        if let Some((normalised, _witness)) =
            Self::store_store_normalize(&rhs, &self.local_disequalities)
        {
            self.derived_eqs.push((lhs, normalised));
        }
        AssertResult::Ignored
    }

    fn check(&mut self) -> CheckResult {
        match &self.conflict {
            Some(w) => CheckResult::Unsat { witness: w.clone() },
            None => CheckResult::Sat,
        }
    }

    fn explain(&self) -> Option<TheoryWitness> { self.conflict.clone() }

    fn derive_equalities(&self) -> Vec<(Term, Term)> {
        self.derived_eqs.clone()
    }

    fn cardinality_witness(&self, sort: &Type) -> PoliteWitness {
        // Arrays are stably infinite when the element sort is stably
        // infinite (sec 26 table). v0.3 alpha defers to ω; v0.5 plugs
        // in the kind-aware reconciliation.
        PoliteWitness { sort: format!("{sort}"), upper_bound: None }
    }

    fn push(&mut self) {
        self.scope_stack.push(ArraysScope {
            derived_eqs_len: self.derived_eqs.len(),
            local_diseq_len: self.local_disequalities.len(),
            pending_ext_len: self.pending_extensionality.len(),
        });
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if let Some(snap) = self.scope_stack.pop() {
                self.derived_eqs.truncate(snap.derived_eqs_len);
                self.local_disequalities.truncate(snap.local_diseq_len);
                self.pending_extensionality.truncate(snap.pending_ext_len);
            }
        }
        self.conflict = None;
    }

    fn reset(&mut self) {
        self.derived_eqs.clear();
        self.local_disequalities.clear();
        self.pending_extensionality.clear();
        self.conflict = None;
        self.scope_stack.clear();
    }
}

impl Arrays {
    /// Inspect the queue of pending extensionality witnesses. Each
    /// `(a, b)` here was asserted as `a ≠ b` at an array sort. The
    /// quantifier layer above the theory routes these as
    /// `(diff a b)` candidate atoms — extensionality says some
    /// index `k` exists with `select a k ≠ select b k`, and
    /// instantiating `k := diff a b` gives a concrete witness.
    pub fn pending_extensionality(&self) -> &[(Term, Term)] {
        &self.pending_extensionality
    }

    /// Drain the extensionality queue. Used by the quantifier layer
    /// after it routes the witnesses so they don't fire repeatedly.
    pub fn drain_extensionality(&mut self) -> Vec<(Term, Term)> {
        std::mem::take(&mut self.pending_extensionality)
    }

    /// Inspect the locally-known disequalities — exposed primarily
    /// for tests and downstream consumers that want to reflect on
    /// what the theory has accumulated. Returned ordering is
    /// insertion order.
    pub fn local_disequalities(&self) -> &[(Term, Term)] {
        &self.local_disequalities
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Term, Type};

    fn int_() -> Type { Type::const_("Int", Kind::Type) }
    fn arr_int_int() -> Type { Type::const_("Array_Int_Int", Kind::Type) }

    fn select_const() -> Term {
        // select : Array -> Int -> Int
        let t = Type::fun(arr_int_int(), Type::fun(int_(), int_()).unwrap()).unwrap();
        Term::const_("select", t)
    }

    fn store_const() -> Term {
        // store : Array -> Int -> Int -> Array
        let t1 = Type::fun(int_(), arr_int_int()).unwrap();
        let t2 = Type::fun(int_(), t1).unwrap();
        let t = Type::fun(arr_int_int(), t2).unwrap();
        Term::const_("store", t)
    }

    fn mk_select(a: Term, i: Term) -> Term {
        Term::app(Term::app(select_const(), a).unwrap(), i).unwrap()
    }
    fn mk_store(a: Term, i: Term, v: Term) -> Term {
        Term::app(Term::app(Term::app(store_const(), a).unwrap(), i).unwrap(), v).unwrap()
    }

    #[test]
    fn handles_array_sorts() {
        let arr = Arrays::new();
        assert!(arr.handles_sort(&arr_int_int()));
        assert!(!arr.handles_sort(&int_()));
    }

    #[test]
    fn read_over_write_same_index_derives_equality() {
        // (select (store a i v) i) = w  ⟹  derive v = w
        let mut arr = Arrays::new();
        let a = Term::var("a", arr_int_int());
        let i = Term::var("i", int_());
        let v = Term::var("v", int_());
        let w = Term::var("w", int_());
        let lhs = mk_select(mk_store(a, i.clone(), v.clone()), i);
        let eq = Term::mk_eq(lhs, w.clone()).unwrap();
        let _ = arr.assert(Literal::positive(eq).unwrap());
        let derived = arr.derive_equalities();
        assert_eq!(derived.len(), 1);
        assert!(derived[0].0.alpha_eq(&v));
        assert!(derived[0].1.alpha_eq(&w));
    }

    #[test]
    fn read_over_write_different_index_without_disequality_is_deferred() {
        // (select (store a i v) j) — different indices, no rewrite
        // until the disequality `i ≠ j` is locally known.
        let mut arr = Arrays::new();
        let a = Term::var("a", arr_int_int());
        let i = Term::var("i", int_());
        let j = Term::var("j", int_());
        let v = Term::var("v", int_());
        let w = Term::var("w", int_());
        let lhs = mk_select(mk_store(a, i, v), j);
        let eq = Term::mk_eq(lhs, w).unwrap();
        let _ = arr.assert(Literal::positive(eq).unwrap());
        assert!(arr.derive_equalities().is_empty());
    }

    #[test]
    fn read_over_write_different_index_with_local_disequality_fires() {
        // Assert `i ≠ j` first, then `(select (store a i v) j) = w`
        // → derive `(select a j) = w`.
        let mut arr = Arrays::new();
        let a = Term::var("a", arr_int_int());
        let i = Term::var("i", int_());
        let j = Term::var("j", int_());
        let v = Term::var("v", int_());
        let w = Term::var("w", int_());
        // 1. Disequality.
        let i_eq_j = Term::mk_eq(i.clone(), j.clone()).unwrap();
        let _ = arr.assert(Literal::negative(i_eq_j).unwrap());
        assert_eq!(arr.local_disequalities().len(), 1);
        // 2. Read over write with non-matching index.
        let lhs = mk_select(mk_store(a.clone(), i, v), j.clone());
        let eq = Term::mk_eq(lhs, w.clone()).unwrap();
        let _ = arr.assert(Literal::positive(eq).unwrap());
        let derived = arr.derive_equalities();
        assert_eq!(derived.len(), 1);
        // derived[0].0 should be (select a j)
        let expected_select = mk_select(a, j);
        assert!(
            derived[0].0.alpha_eq(&expected_select),
            "expected `(select a j)` on LHS of derived, got {:?}",
            derived[0].0
        );
        assert!(derived[0].1.alpha_eq(&w));
    }

    #[test]
    fn array_disequality_queues_extensionality_witness() {
        // Assert `a1 ≠ a2` where both are of array sort
        // → extensionality witness `(diff a1 a2)` queued.
        let mut arr = Arrays::new();
        let a1 = Term::var("a1", arr_int_int());
        let a2 = Term::var("a2", arr_int_int());
        let eq = Term::mk_eq(a1.clone(), a2.clone()).unwrap();
        let _ = arr.assert(Literal::negative(eq).unwrap());
        assert_eq!(arr.pending_extensionality().len(), 1);
        let (ext_a, ext_b) = arr.pending_extensionality()[0].clone();
        assert!(ext_a.alpha_eq(&a1) || ext_a.alpha_eq(&a2));
        assert!(ext_b.alpha_eq(&a1) || ext_b.alpha_eq(&a2));
    }

    #[test]
    fn non_array_disequality_does_not_queue_extensionality() {
        // Int disequality should NOT generate extensionality.
        let mut arr = Arrays::new();
        let i = Term::var("i", int_());
        let j = Term::var("j", int_());
        let eq = Term::mk_eq(i, j).unwrap();
        let _ = arr.assert(Literal::negative(eq).unwrap());
        assert_eq!(arr.local_disequalities().len(), 1);
        assert!(arr.pending_extensionality().is_empty());
    }

    #[test]
    fn drain_extensionality_clears_the_queue() {
        let mut arr = Arrays::new();
        let a1 = Term::var("a1", arr_int_int());
        let a2 = Term::var("a2", arr_int_int());
        let eq = Term::mk_eq(a1, a2).unwrap();
        let _ = arr.assert(Literal::negative(eq).unwrap());
        let drained = arr.drain_extensionality();
        assert_eq!(drained.len(), 1);
        assert!(arr.pending_extensionality().is_empty());
    }

    #[test]
    fn push_pop_restores_disequalities_and_extensionality() {
        let mut arr = Arrays::new();
        let i = Term::var("i", int_());
        let j = Term::var("j", int_());
        let a1 = Term::var("a1", arr_int_int());
        let a2 = Term::var("a2", arr_int_int());
        arr.push();
        let _ = arr.assert(
            Literal::negative(Term::mk_eq(i, j).unwrap()).unwrap(),
        );
        let _ = arr.assert(
            Literal::negative(Term::mk_eq(a1, a2).unwrap()).unwrap(),
        );
        assert_eq!(arr.local_disequalities().len(), 1);
        assert_eq!(arr.pending_extensionality().len(), 1);
        arr.pop(1);
        assert!(arr.local_disequalities().is_empty());
        assert!(arr.pending_extensionality().is_empty());
    }

    #[test]
    fn push_pop_truncates_derived_eqs() {
        let mut arr = Arrays::new();
        let a = Term::var("a", arr_int_int());
        let i = Term::var("i", int_());
        let v = Term::var("v", int_());
        let w = Term::var("w", int_());
        let eq = Term::mk_eq(
            mk_select(mk_store(a, i.clone(), v), i),
            w,
        )
        .unwrap();
        arr.push();
        let _ = arr.assert(Literal::positive(eq).unwrap());
        assert_eq!(arr.derive_equalities().len(), 1);
        arr.pop(1);
        assert!(arr.derive_equalities().is_empty());
    }

    // === v0.19 C.3 store-store normalisation ===

    #[test]
    fn store_store_same_index_dominance() {
        let a = Term::var("a", arr_int_int());
        let i = Term::var("i", int_());
        let v1 = Term::var("v1", int_());
        let v2 = Term::var("v2", int_());
        let inner = mk_store(a.clone(), i.clone(), v1);
        let outer = mk_store(inner, i.clone(), v2.clone());
        // Same-index dominance — no disequalities needed.
        let result = Arrays::store_store_normalize(&outer, &[]);
        assert!(result.is_some(), "same-index dominance should fire");
        let (rewritten, _side) = result.unwrap();
        // Rewritten should be `(store a i v2)`.
        let expected = mk_store(a, i, v2);
        assert!(rewritten.alpha_eq(&expected));
    }

    #[test]
    fn store_store_disequal_index_commutativity() {
        let a = Term::var("a", arr_int_int());
        let i = Term::var("i", int_());
        let j = Term::var("j", int_());
        let v1 = Term::var("v1", int_());
        let v2 = Term::var("v2", int_());
        let inner = mk_store(a.clone(), i.clone(), v1.clone());
        let outer = mk_store(inner, j.clone(), v2.clone());
        // Without the disequality, no rewrite.
        assert!(Arrays::store_store_normalize(&outer, &[]).is_none());
        // With i ≠ j, the swap fires.
        let result = Arrays::store_store_normalize(
            &outer,
            &[(i.clone(), j.clone())],
        );
        assert!(result.is_some(), "diseq-index swap should fire");
        let (rewritten, _side) = result.unwrap();
        // Expected: (store (store a j v2) i v1).
        let expected_inner = mk_store(a, j, v2);
        let expected = mk_store(expected_inner, i, v1);
        assert!(rewritten.alpha_eq(&expected));
    }

    #[test]
    fn store_store_normalize_returns_none_for_non_store_store() {
        let a = Term::var("a", arr_int_int());
        let i = Term::var("i", int_());
        let v = Term::var("v", int_());
        // Single store — not a nested store.
        let single = mk_store(a, i, v);
        assert!(Arrays::store_store_normalize(&single, &[]).is_none());
    }
}
