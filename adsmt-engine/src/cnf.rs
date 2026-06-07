//! CNF decomposition for the v0.3 Boolean engine.
//!
//! [`flatten_to_clauses`] decomposes an asserted Boolean term into
//! a conjunction of clauses (each a disjunction of literals). Rules:
//!
//! - `(and p q)`              ⟶ flatten each side
//! - `(not (and p q))`        ⟶ flatten `(or (not p) (not q))`
//! - `(or p q)`               ⟶ single clause with each disjunct as literal
//! - `(not (or p q))`         ⟶ flatten each negated side as separate clauses
//! - `(=> p q)`               ⟶ `(or (not p) q)`
//! - `(not (not p))`          ⟶ flatten `p`
//! - `true`                   ⟶ empty clause set (vacuously true)
//! - `false`                  ⟶ a single empty clause (unsat)
//! - atomic literal `p` or `(not p)` ⟶ unit clause
//!
//! Nested OR-of-AND (`(or X (and Y Z))` and its De Morgan duals)
//! is handled by a **Tseitin transform** (rc.29 / verus-fork S.2):
//! a conjunction appearing where a flat literal list is required is
//! replaced by a fresh auxiliary Boolean `aux` carrying the defining
//! clauses `aux ⟺ subformula`, so the whole assertion flattens to
//! `Some(clauses)` instead of the pre-rc.29 `None` (which routed it
//! through the opaque `had_opaque` path and reported `Unknown` where
//! z3 returns `unsat`). The encoding is equisatisfiable and linear in
//! the term size — no exponential blow-up. Aux atoms are
//! *content-named* (`!tseitin!<subterm>`), so identical sub-formulas
//! share one definition and aux atoms never collide across separate
//! assertions: a per-call counter (`aux!0`, `aux!1`, …) would make
//! assertion A's `aux!0` and assertion B's `aux!0` the *same*
//! hash-consed `Term`, aliasing two different sub-formulas under one
//! contradictory definition — unsound. Soundness floor: the empty
//! clause stays sacred (the aux path never drops a genuine
//! contradiction), so the rc.26→28 soundness regressions hold.

use adsmt_core::Term;

/// A literal: an atom paired with its polarity (true = positive).
#[derive(Clone, Debug)]
pub struct Lit {
    pub atom: Term,
    pub polarity: bool,
}

impl Lit {
    pub fn new(atom: Term, polarity: bool) -> Self { Self { atom, polarity } }
    pub fn pos(atom: Term) -> Self { Self::new(atom, true) }
    pub fn neg(atom: Term) -> Self { Self::new(atom, false) }
    pub fn negate(self) -> Self { Self { atom: self.atom, polarity: !self.polarity } }

    /// α-equivalence on atoms, polarity exact.
    pub fn matches(&self, other: &Lit) -> bool {
        self.polarity == other.polarity && self.atom.alpha_eq(&other.atom)
    }

    /// `p` vs `¬p`.
    pub fn is_negation_of(&self, other: &Lit) -> bool {
        self.polarity != other.polarity && self.atom.alpha_eq(&other.atom)
    }
}

/// A clause: disjunction of literals. Empty clause = false.
pub type Clause = Vec<Lit>;

/// Decompose `t` (asserted positively) into a conjunction of clauses.
/// Returns `Some(clauses)` if the structure is fully handled.
/// Compound structures we can't decompose syntactically (nested OR
/// of AND, etc.) return `None` — the engine treats the assertion as
/// opaque and reports Unknown if it can't be solved otherwise.
pub fn flatten_to_clauses(t: &Term) -> Option<Vec<Clause>> {
    let mut ctx = Tseitin::new(None);
    let mut clauses = flatten(t, true, &mut ctx)?;
    // The Tseitin defining clauses are global constraints — conjoin
    // them with the main clause set (append == conjunction).
    clauses.append(&mut ctx.aux);
    Some(clauses)
}

/// Deadline-aware variant of [`flatten_to_clauses`].  Threads the
/// wall-clock budget into the recursive descent so a single large
/// term (a Verus prelude assertion can run to hundreds of nested
/// `and` / `or` / `=>` / `not` nodes) gives up promptly when the
/// caller's `:rlimit` lapses, instead of blocking the whole
/// `check_sat` loop on one CNF flattening.  Returning `None` here
/// would route the assertion through the theory-check fallback
/// (which itself respects the deadline) and surface Unknown to the
/// front-end with `:reason-unknown "rlimit exceeded"`.
///
/// We also impose a hard size guard via [`term_size_bounded`]: if
/// the input term already exceeds `MAX_FLATTEN_NODES` boolean-tree
/// nodes we bail to `None` up front rather than start the
/// recursion at all.  The destructuring primitives in
/// `adsmt-core::Term` build new `Box<Term>` clones on every `dest_*`
/// call, so a 10⁵-node assertion (Verus's `fuel_defaults` axiom
/// chain is in that range) generates work proportional to the node
/// count times the depth — fine for unbounded `check_sat`, fatal
/// for any wall-clock budget that doesn't catch the deadline
/// between recursion levels.
///
/// `term_size_bounded` is a `pub(crate)` helper documented in
/// source — the intra-doc link is intentional even though
/// rustdoc flags it as a private-item link, hence the
/// `#[allow(rustdoc::private_intra_doc_links)]` below.
#[allow(rustdoc::private_intra_doc_links)]
pub fn flatten_to_clauses_with_deadline(
    t: &Term,
    deadline: Option<std::time::Instant>,
) -> Option<Vec<Clause>> {
    // Pre-bound on the input term — a flattening that would touch
    // more than this many `(and|or|=>|not)` nodes is routed to the
    // theory-check fallback instead, which itself respects the
    // deadline and (more importantly) doesn't allocate.
    const MAX_FLATTEN_NODES: usize = 4096;
    if !term_size_bounded(t, MAX_FLATTEN_NODES) {
        return None;
    }
    let mut ctx = Tseitin::new(deadline);
    let mut clauses = flatten(t, true, &mut ctx)?;
    clauses.append(&mut ctx.aux);
    Some(clauses)
}

fn deadline_expired(d: Option<std::time::Instant>) -> bool {
    d.is_some_and(|dl| std::time::Instant::now() >= dl)
}

/// `true` when `t`'s boolean-tree node count (counting `and` / `or`
/// / `=>` / `not` connectives only) stays `≤ limit`.  Walks the
/// term without allocating — the recursion lives on the Rust call
/// stack and accumulates a counter.  Stops early as soon as the
/// limit is busted so wildly large inputs don't blow the stack
/// either.
fn term_size_bounded(t: &Term, limit: usize) -> bool {
    fn walk(t: &Term, budget: &mut usize) -> bool {
        if *budget == 0 { return false; }
        *budget -= 1;
        // We only ever recurse through `(not _)`, `(and _ _)`,
        // `(or _ _)`, `(=> _ _)` — everything else is an atom from
        // the flattener's point of view, so the recursion stops
        // there.
        if let Some(inner) = t.dest_not() {
            return walk(&inner, budget);
        }
        if let Some((p, q)) = t.dest_and() {
            return walk(&p, budget) && walk(&q, budget);
        }
        if let Some((p, q)) = t.dest_or() {
            return walk(&p, budget) && walk(&q, budget);
        }
        if let Some((p, q)) = t.dest_imp() {
            return walk(&p, budget) && walk(&q, budget);
        }
        true
    }
    let mut budget = limit;
    walk(t, &mut budget)
}

/// rc.29 (verus-fork S.2) — Tseitin transform working state threaded
/// through the recursive flattener.  Holds the wall-clock `deadline`,
/// the accumulator of auxiliary defining clauses (`aux ⟺ subformula`),
/// and the set of aux atoms already defined so a sub-formula that
/// recurs is encoded once.
struct Tseitin {
    deadline: Option<std::time::Instant>,
    aux: Vec<Clause>,
    defined: std::collections::HashSet<Term>,
}

impl Tseitin {
    fn new(deadline: Option<std::time::Instant>) -> Self {
        Self {
            deadline,
            aux: Vec::new(),
            defined: std::collections::HashSet::new(),
        }
    }
    fn expired(&self) -> bool {
        deadline_expired(self.deadline)
    }
}

/// A Tseitin sub-result for an arbitrary boolean sub-term: a resolved
/// constant, or a single literal standing in for the sub-formula (an
/// atom, or a fresh aux atom for a compound).
enum Encoded {
    True,
    False,
    Lit(Lit),
}

impl Encoded {
    fn negate(self) -> Self {
        match self {
            Encoded::True => Encoded::False,
            Encoded::False => Encoded::True,
            Encoded::Lit(l) => Encoded::Lit(l.negate()),
        }
    }
}

/// Content-derived aux atom for a sub-term.  Two structurally
/// identical sub-terms map to the same hash-consed `Term`, so they
/// share one definition; aux atoms never collide across separate
/// assertions (a per-call counter would alias different sub-formulas
/// under the same name — unsound, see the module docs).
fn aux_var_for(t: &Term) -> Term {
    Term::var(&format!("!tseitin!{t}"), adsmt_core::Type::bool_())
}

/// Encode an arbitrary boolean sub-term into a single [`Encoded`],
/// emitting `aux ⟺ subformula` defining clauses into `ctx.aux` for
/// every genuine compound node.  Constant-folds `true` / `false` so no
/// constant ever lands in an aux clause.  Equisatisfiable; linear in
/// the sub-term size.
fn encode(t: &Term, ctx: &mut Tseitin) -> Option<Encoded> {
    if ctx.expired() {
        return None;
    }
    if let Some(inner) = t.dest_not() {
        return Some(encode(&inner, ctx)?.negate());
    }
    if t.is_true_const() {
        return Some(Encoded::True);
    }
    if t.is_false_const() {
        return Some(Encoded::False);
    }
    if let Some((a, b)) = t.dest_and() {
        let ea = encode(&a, ctx)?;
        let eb = encode(&b, ctx)?;
        return Some(encode_and(t, ea, eb, ctx));
    }
    if let Some((a, b)) = t.dest_or() {
        let ea = encode(&a, ctx)?;
        let eb = encode(&b, ctx)?;
        return Some(encode_or(t, ea, eb, ctx));
    }
    if let Some((a, b)) = t.dest_imp() {
        // (a ⟹ b) ≡ (¬a ∨ b)
        let ea = encode(&a, ctx)?.negate();
        let eb = encode(&b, ctx)?;
        return Some(encode_or(t, ea, eb, ctx));
    }
    Some(Encoded::Lit(Lit::pos(t.clone())))
}

/// `aux ⟺ (la ∧ lb)` with constant folding.  `t` names the aux.
fn encode_and(t: &Term, ea: Encoded, eb: Encoded, ctx: &mut Tseitin) -> Encoded {
    match (ea, eb) {
        // (… ∧ false) ≡ false ; (false ∧ …) ≡ false
        (Encoded::False, _) | (_, Encoded::False) => Encoded::False,
        // (… ∧ true) ≡ … ; (true ∧ …) ≡ …
        (Encoded::True, e) | (e, Encoded::True) => e,
        (Encoded::Lit(la), Encoded::Lit(lb)) => {
            let aux = aux_var_for(t);
            if ctx.defined.insert(aux.clone()) {
                // aux ⟹ la, aux ⟹ lb, (la ∧ lb) ⟹ aux
                ctx.aux.push(vec![Lit::neg(aux.clone()), la.clone()]);
                ctx.aux.push(vec![Lit::neg(aux.clone()), lb.clone()]);
                ctx.aux
                    .push(vec![la.negate(), lb.negate(), Lit::pos(aux.clone())]);
            }
            Encoded::Lit(Lit::pos(aux))
        }
    }
}

/// `aux ⟺ (la ∨ lb)` with constant folding.  `t` names the aux.
fn encode_or(t: &Term, ea: Encoded, eb: Encoded, ctx: &mut Tseitin) -> Encoded {
    match (ea, eb) {
        // (… ∨ true) ≡ true ; (true ∨ …) ≡ true
        (Encoded::True, _) | (_, Encoded::True) => Encoded::True,
        // (… ∨ false) ≡ … ; (false ∨ …) ≡ …
        (Encoded::False, e) | (e, Encoded::False) => e,
        (Encoded::Lit(la), Encoded::Lit(lb)) => {
            let aux = aux_var_for(t);
            if ctx.defined.insert(aux.clone()) {
                // aux ⟹ (la ∨ lb), la ⟹ aux, lb ⟹ aux
                ctx.aux
                    .push(vec![Lit::neg(aux.clone()), la.clone(), lb.clone()]);
                ctx.aux.push(vec![la.negate(), Lit::pos(aux.clone())]);
                ctx.aux.push(vec![lb.negate(), Lit::pos(aux.clone())]);
            }
            Encoded::Lit(Lit::pos(aux))
        }
    }
}

/// Convert an [`Encoded`] (for sub-term `t`) into the literal
/// contribution this disjunct adds to its enclosing clause, at the
/// requested polarity (`true` → literals for `t`, `false` → for `¬t`).
/// A constant that folds to a tautological disjunct contributes the
/// `true_const` literal (matching the existing `(or … true …)`
/// convention); a `false` disjunct contributes nothing.
fn encoded_to_disjunct_lits(e: Encoded, polarity: bool) -> Vec<Lit> {
    match (e, polarity) {
        (Encoded::Lit(l), true) => vec![l],
        (Encoded::Lit(l), false) => vec![l.negate()],
        // disjunct resolves to `true` → tautological clause member
        (Encoded::True, true) | (Encoded::False, false) => {
            vec![Lit::pos(Term::true_const())]
        }
        // disjunct resolves to `false` → adds nothing to the OR
        (Encoded::True, false) | (Encoded::False, true) => Vec::new(),
    }
}

fn flatten(t: &Term, polarity: bool, ctx: &mut Tseitin) -> Option<Vec<Clause>> {
    // Bail out as soon as the deadline lapses anywhere in the
    // recursive descent.  Caller treats `None` as "engine can't
    // route this assertion" and falls back to the theory path,
    // which is itself deadline-aware.
    if ctx.expired() {
        return None;
    }
    // (not P): flip polarity, recurse.
    if let Some(inner) = t.dest_not() {
        return flatten(&inner, !polarity, ctx);
    }
    // true / false handling under polarity.
    if t.is_true_const() {
        return Some(if polarity { Vec::new() } else { vec![Vec::new()] });
    }
    if t.is_false_const() {
        return Some(if polarity { vec![Vec::new()] } else { Vec::new() });
    }
    // Compound destructuring.
    match polarity {
        true => flatten_positive(t, ctx),
        false => flatten_negative(t, ctx),
    }
}

fn flatten_positive(t: &Term, ctx: &mut Tseitin) -> Option<Vec<Clause>> {
    if ctx.expired() {
        return None;
    }
    // (and p q): conjunction → both flattened independently.
    if let Some((p, q)) = t.dest_and() {
        let mut out = flatten(&p, true, ctx)?;
        out.extend(flatten(&q, true, ctx)?);
        return Some(out);
    }
    // (or p q): single clause containing flattened disjuncts as literals.
    if let Some((p, q)) = t.dest_or() {
        let mut lits = literals_of_disjunct(&p, true, ctx)?;
        lits.extend(literals_of_disjunct(&q, true, ctx)?);
        return Some(vec![lits]);
    }
    // (=> p q) === (or (not p) q)
    if let Some((p, q)) = t.dest_imp() {
        let mut lits = literals_of_disjunct(&p, false, ctx)?;
        lits.extend(literals_of_disjunct(&q, true, ctx)?);
        return Some(vec![lits]);
    }
    // Atomic literal.
    Some(vec![vec![Lit::pos(t.clone())]])
}

fn flatten_negative(t: &Term, ctx: &mut Tseitin) -> Option<Vec<Clause>> {
    if ctx.expired() {
        return None;
    }
    // De Morgan: (not (and p q)) → (or (not p) (not q))
    if let Some((p, q)) = t.dest_and() {
        let mut lits = literals_of_disjunct(&p, false, ctx)?;
        lits.extend(literals_of_disjunct(&q, false, ctx)?);
        return Some(vec![lits]);
    }
    // (not (or p q)) → (and (not p) (not q))
    if let Some((p, q)) = t.dest_or() {
        let mut out = flatten(&p, false, ctx)?;
        out.extend(flatten(&q, false, ctx)?);
        return Some(out);
    }
    // (not (=> p q)) === (and p (not q))
    if let Some((p, q)) = t.dest_imp() {
        let mut out = flatten(&p, true, ctx)?;
        out.extend(flatten(&q, false, ctx)?);
        return Some(out);
    }
    // Negative atom — unit clause.
    Some(vec![vec![Lit::neg(t.clone())]])
}

/// Extract a flat list of literals from a disjunct sub-expression.
/// Handles `(or ...)`, `(=> ...)`, `(not ...)`, and atoms directly; a
/// conjunction inside a disjunct (the `(or … (and …) …)` shape and its
/// De Morgan duals) is Tseitin-encoded into a fresh aux literal whose
/// definition is emitted into `ctx.aux` — the rc.29 (S.2) completeness
/// fix that replaced the pre-rc.29 `None` return.
fn literals_of_disjunct(t: &Term, polarity: bool, ctx: &mut Tseitin) -> Option<Vec<Lit>> {
    if ctx.expired() {
        return None;
    }
    if let Some(inner) = t.dest_not() {
        return literals_of_disjunct(&inner, !polarity, ctx);
    }
    if polarity {
        if let Some((p, q)) = t.dest_or() {
            let mut out = literals_of_disjunct(&p, true, ctx)?;
            out.extend(literals_of_disjunct(&q, true, ctx)?);
            return Some(out);
        }
        if let Some((p, q)) = t.dest_imp() {
            let mut out = literals_of_disjunct(&p, false, ctx)?;
            out.extend(literals_of_disjunct(&q, true, ctx)?);
            return Some(out);
        }
        if t.dest_and().is_some() {
            // rc.29 (S.2): `(or … (and …) …)` — a conjunction in a
            // positive disjunct can't be split into OR-literals;
            // Tseitin-encode it to a fresh aux literal.
            return Some(encoded_to_disjunct_lits(encode(t, ctx)?, true));
        }
        if t.is_true_const() {
            return Some(vec![Lit::pos(Term::true_const())]);
        }
        if t.is_false_const() {
            return Some(Vec::new());
        }
        Some(vec![Lit::pos(t.clone())])
    } else {
        if let Some((p, q)) = t.dest_and() {
            let mut out = literals_of_disjunct(&p, false, ctx)?;
            out.extend(literals_of_disjunct(&q, false, ctx)?);
            return Some(out);
        }
        if t.dest_or().is_some() || t.dest_imp().is_some() {
            // rc.29 (S.2): `¬(p ∨ q)` / `¬(p ⟹ q)` is a conjunction in
            // a negative disjunct — Tseitin-encode and contribute the
            // negated aux literal.
            return Some(encoded_to_disjunct_lits(encode(t, ctx)?, false));
        }
        Some(vec![Lit::neg(t.clone())])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Type;

    fn p() -> Term { Term::var("p", Type::bool_()) }
    fn q() -> Term { Term::var("q", Type::bool_()) }
    fn r() -> Term { Term::var("r", Type::bool_()) }

    #[test]
    fn atom_is_unit_clause() {
        let cs = flatten_to_clauses(&p()).unwrap();
        assert_eq!(cs.len(), 1);
        assert_eq!(cs[0].len(), 1);
        assert!(cs[0][0].polarity);
    }

    #[test]
    fn negation_flips_polarity() {
        let t = Term::mk_not(p()).unwrap();
        let cs = flatten_to_clauses(&t).unwrap();
        assert!(!cs[0][0].polarity);
    }

    #[test]
    fn conjunction_splits_into_clauses() {
        let t = Term::mk_and(p(), q()).unwrap();
        let cs = flatten_to_clauses(&t).unwrap();
        assert_eq!(cs.len(), 2);
    }

    #[test]
    fn disjunction_stays_single_clause() {
        let t = Term::mk_or(p(), q()).unwrap();
        let cs = flatten_to_clauses(&t).unwrap();
        assert_eq!(cs.len(), 1);
        assert_eq!(cs[0].len(), 2);
    }

    #[test]
    fn implication_rewrites_to_or_not() {
        let t = Term::mk_imp(p(), q()).unwrap();
        let cs = flatten_to_clauses(&t).unwrap();
        assert_eq!(cs.len(), 1);
        assert_eq!(cs[0].len(), 2);
        assert!(!cs[0][0].polarity); // not p
        assert!(cs[0][1].polarity);  // q
    }

    #[test]
    fn de_morgan_negated_and() {
        // ¬(p ∧ q) → (¬p ∨ ¬q) — one clause with two negative literals.
        let t = Term::mk_not(Term::mk_and(p(), q()).unwrap()).unwrap();
        let cs = flatten_to_clauses(&t).unwrap();
        assert_eq!(cs.len(), 1);
        assert!(cs[0].iter().all(|l| !l.polarity));
    }

    #[test]
    fn de_morgan_negated_or() {
        // ¬(p ∨ q) → (¬p) ∧ (¬q) — two unit clauses, both negative.
        let t = Term::mk_not(Term::mk_or(p(), q()).unwrap()).unwrap();
        let cs = flatten_to_clauses(&t).unwrap();
        assert_eq!(cs.len(), 2);
        assert!(cs.iter().all(|c| !c[0].polarity));
    }

    #[test]
    fn double_negation_cancels() {
        let t = Term::mk_not(Term::mk_not(p()).unwrap()).unwrap();
        let cs = flatten_to_clauses(&t).unwrap();
        assert_eq!(cs[0].len(), 1);
        assert!(cs[0][0].polarity);
    }

    #[test]
    fn variadic_and_via_nested_terms() {
        // (and p (and q r)) — right-fold from the parser
        let inner = Term::mk_and(q(), r()).unwrap();
        let t = Term::mk_and(p(), inner).unwrap();
        let cs = flatten_to_clauses(&t).unwrap();
        assert_eq!(cs.len(), 3); // one unit clause per atom
    }

    #[test]
    fn true_asserts_to_empty_clause_set() {
        let cs = flatten_to_clauses(&Term::true_const()).unwrap();
        assert!(cs.is_empty());
    }

    #[test]
    fn false_asserts_to_empty_clause_meaning_unsat() {
        let cs = flatten_to_clauses(&Term::false_const()).unwrap();
        assert_eq!(cs.len(), 1);
        assert!(cs[0].is_empty());
    }

    // ----- rc.29 (verus-fork S.2) Tseitin OR-of-AND -----

    /// `(or X (and Y Z))` was `None` (opaque) pre-rc.29; the Tseitin
    /// transform now returns `Some` — a fresh aux atom with its
    /// defining clauses, plus the top clause `(X ∨ aux)`.
    #[test]
    fn or_of_and_is_tseitin_encoded_not_none() {
        // (or p (and q r))
        let t = Term::mk_or(p(), Term::mk_and(q(), r()).unwrap()).unwrap();
        let cs = flatten_to_clauses(&t).expect("OR-of-AND must flatten via Tseitin, not None");
        // Top clause (p ∨ aux) + three defining clauses for
        // aux ⟺ (q ∧ r) = 4 clauses total.
        assert_eq!(cs.len(), 4, "1 top clause + 3 aux-defining clauses");
        // Exactly one aux atom is introduced.
        let aux_atoms: std::collections::HashSet<String> = cs
            .iter()
            .flatten()
            .map(|l| l.atom.to_string())
            .filter(|n| n.starts_with("!tseitin!"))
            .collect();
        assert_eq!(aux_atoms.len(), 1, "one aux atom for the single (and q r)");
    }

    /// The verus-fork canonical witness:
    /// `(or (and P (not P)) (and P (not P)))` is structurally unsat.
    /// It must flatten (not return `None`); the buried contradiction
    /// is then resolvable by the SAT solve (verdict tested in
    /// `solver.rs`).
    #[test]
    fn structurally_unsat_or_of_and_witness_flattens() {
        let pnp = || Term::mk_and(p(), Term::mk_not(p()).unwrap()).unwrap();
        let t = Term::mk_or(pnp(), pnp()).unwrap();
        let cs = flatten_to_clauses(&t)
            .expect("the OR-of-AND unsat witness must flatten, not return None");
        // Both disjuncts are the *same* sub-term, so the
        // content-named aux is shared: only one aux definition set.
        let aux_atoms: std::collections::HashSet<String> = cs
            .iter()
            .flatten()
            .map(|l| l.atom.to_string())
            .filter(|n| n.starts_with("!tseitin!"))
            .collect();
        assert_eq!(
            aux_atoms.len(),
            1,
            "identical conjuncts share one content-named aux"
        );
    }

    /// Constant folding: `(or X (and Y true))` ≡ `(or X Y)` — no aux,
    /// a plain two-literal clause.
    #[test]
    fn tseitin_constant_folds_and_with_true() {
        let t = Term::mk_or(p(), Term::mk_and(q(), Term::true_const()).unwrap()).unwrap();
        let cs = flatten_to_clauses(&t).unwrap();
        assert_eq!(cs.len(), 1, "folds to a single (p ∨ q) clause, no aux");
        assert_eq!(cs[0].len(), 2);
        assert!(
            cs.iter()
                .flatten()
                .all(|l| !l.atom.to_string().starts_with("!tseitin!")),
            "no aux atom when the conjunction folds away"
        );
    }

    /// De Morgan dual: `(not (and (or p q) r))` flows through the
    /// negative-disjunct Tseitin arm and still flattens.
    #[test]
    fn negated_and_of_or_flattens_via_tseitin() {
        // (not (and (or p q) r)) ≡ (or (not (or p q)) (not r))
        let inner = Term::mk_and(Term::mk_or(p(), q()).unwrap(), r()).unwrap();
        let t = Term::mk_not(inner).unwrap();
        assert!(
            flatten_to_clauses(&t).is_some(),
            "negated AND-of-OR must flatten via Tseitin"
        );
    }
}
