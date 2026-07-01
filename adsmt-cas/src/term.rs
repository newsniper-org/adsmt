//! The typed-term classifier (design §6) — recognizes an adsmt-core HOL
//! **arith term** as a polynomial and lifts an obligation into a [`crate::Obligation`]
//! the dispatcher can route. Feature-gated (`term`) so the pure-math re-check
//! core stays dependency-light.
//!
//! ## Why this is the trusted reflection, not untrusted routing
//! [`term_to_mpoly`] is a **faithful partial recognizer**: for any term it either
//! returns the EXACT polynomial the term denotes (built from `+`/`-`/`*` over
//! integer literals and variables — exact `BigRational` arithmetic), or `None`
//! (an uninterpreted / `div` / `mod` / non-arith shape it does not claim). It
//! NEVER returns a *wrong* polynomial for a term. So building an [`crate::Obligation`]
//! through it is not the untrusted extraction the review warned about (§9-B2) —
//! the polynomials are the faithful reflection of the original terms, and
//! [`crate::admit`] re-checking against them IS re-checking against the original.
//!
//! For **ideal membership** this is enough on its own: the classifier may safely
//! ignore a non-polynomial or dropped hypothesis, because membership in a
//! *sub*-ideal implies membership in the full ideal (`f∈⟨subset⟩ ⟹ f∈⟨all⟩`) —
//! sound, only less complete. (The `∃`-Diophantine direction, where dropping a
//! conjunct WOULD be unsound, needs `admit` to re-derive the full system from the
//! term and is a later slice.)

use std::collections::BTreeMap;

use adsmt_core::term::{Term, TermInner};
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::poly::MPoly;
use crate::{Domain, Obligation, Ring};

/// Assigns a stable `MPoly` variable index to each HOL variable *name*, shared
/// across the conclusion and every hypothesis of one obligation.
#[derive(Default)]
pub struct VarIndex {
    map: BTreeMap<String, usize>,
}

impl VarIndex {
    fn index(&mut self, name: &str) -> usize {
        if let Some(&i) = self.map.get(name) {
            return i;
        }
        let i = self.map.len();
        self.map.insert(name.to_string(), i);
        i
    }

    /// Non-inserting lookup — the index already assigned to `name`, or `None`.
    fn get(&self, name: &str) -> Option<usize> {
        self.map.get(name).copied()
    }

    /// How many distinct variable names have been indexed.
    fn len(&self) -> usize {
        self.map.len()
    }
}

/// Parse an integer-literal constant. `None` for a non-integer constant (a real,
/// an operator symbol, an uninterpreted name) — which keeps [`term_to_mpoly`]
/// faithful (an unrecognized constant is not silently coerced to a polynomial).
///
/// Tolerates BOTH literal spellings the workspace uses: the **lowering** emits a
/// bare numeral `Const("3", Int)` (adsmt-ir-lower `fold_int_binop`/`as_int_lit`,
/// which `parse`s `c.name` directly), while the **engine** (`adsmt-theory`) uses
/// the `int:N` form. The CAS classifier consumes lowered adsmt-core terms, so it
/// sees the bare form; the `int:` tolerance is defensive coverage for the
/// engine-format path.
fn int_const(name: &str) -> Option<BigInt> {
    name.strip_prefix("int:").unwrap_or(name).parse::<BigInt>().ok()
}

/// **The faithful reflection** — an arith term → its polynomial over ℚ, or `None`.
/// Handles integer literals, variables, and the binary `+` / `-` / `*` ops
/// (adsmt builds arith curried-binary; `-x` reaches as `(- 0 x)`). Any other
/// shape — `div`/`mod`/`abs`/real-`/`, an uninterpreted application, a `λ`, a
/// non-integer constant — is NOT a polynomial and yields `None`.
///
/// The operator-name strings are the **lowered adsmt-core HOL** spellings the
/// `#325` lowering emits (source of truth: adsmt-ir-lower `lower.rs` — `Int.add`
/// → `"+"`, `Int.sub` → `"-"`, `Int.mul` → `"*"`; `div`/`mod`/`abs`/`/` are left
/// as their own non-arith heads, so they correctly fall through to `None`).
pub fn term_to_mpoly(t: &Term, vars: &mut VarIndex) -> Option<MPoly> {
    match t.kind() {
        TermInner::Const(c) => Some(MPoly::constant(BigRational::from(int_const(&c.name)?))),
        TermInner::Var(v) => Some(MPoly::var(vars.index(&v.name))),
        TermInner::App(outer, b) => {
            let TermInner::App(head, a) = outer.kind() else { return None };
            let TermInner::Const(c) = head.kind() else { return None };
            let pa = term_to_mpoly(a, vars)?;
            let pb = term_to_mpoly(b, vars)?;
            match c.name.as_str() {
                "+" => Some(pa.add(&pb)),
                "-" => Some(pa.sub(&pb)),
                "*" => Some(pa.mul(&pb)),
                _ => None, // div / mod / uninterpreted / power-by-symbol ⇒ not a polynomial
            }
        }
        TermInner::Lam(..) => None,
    }
}

/// Classify a sequent `hyps ⊢ goal` as an **ideal-membership** obligation, if it
/// fits: `goal` is a polynomial equation `f = g` (⤳ the conclusion `f−g = 0`),
/// and each hypothesis that is itself a polynomial equation `p = q` contributes a
/// generator `p−q`. Non-equation / non-polynomial hypotheses are skipped (sound —
/// a sub-ideal). `None` when the goal is not a polynomial equation or there are no
/// polynomial-equation hypotheses (nothing to be a member of). Ring = ℤ,
/// re-checked over ℚ (a ℚ-cofactor identity proves the integer implication).
pub fn classify_membership(hyps: &[Term], goal: &Term) -> Option<Obligation> {
    let mut vars = VarIndex::default();
    let (f, g) = goal.dest_eq()?;
    let concl = term_to_mpoly(&f, &mut vars)?.sub(&term_to_mpoly(&g, &mut vars)?);
    let mut generators = Vec::new();
    for h in hyps {
        if let Some((p, q)) = h.dest_eq()
            && let (Some(pp), Some(qq)) = (term_to_mpoly(&p, &mut vars), term_to_mpoly(&q, &mut vars))
        {
            generators.push(pp.sub(&qq));
        }
    }
    if generators.is_empty() {
        return None;
    }
    Some(Obligation::IdealMembership { ring: Ring::Z, f: concl, generators })
}

/// Peel a leading `∃`-prefix `∃v₁ … ∃vₙ. body`, returning the bound-variable
/// NAMES in prefix order and the innermost body. (adsmt-core builds a multi-var
/// `∃` as nested single-var `exists` applications; `dest_exists` peels one at a
/// time.) `None` if there is no leading `∃`.
fn peel_exists(goal: &Term) -> Option<(Vec<String>, Term)> {
    let mut names = Vec::new();
    let mut cur = goal.clone();
    while let Some((v, body)) = cur.dest_exists() {
        names.push(v.name);
        cur = body;
    }
    if names.is_empty() {
        return None;
    }
    Some((names, cur))
}

/// Flatten a conjunction `a ∧ b ∧ …` into its list of conjuncts (recursively
/// through `dest_and`). A non-conjunction is a one-element list.
fn conjuncts(t: &Term) -> Vec<Term> {
    if let Some((a, b)) = t.dest_and() {
        let mut v = conjuncts(&a);
        v.extend(conjuncts(&b));
        v
    } else {
        vec![t.clone()]
    }
}

/// Recognize the CANONICAL Nat/WNat domain guard the lowering emits for an
/// `∃`-bound refinement variable — `(>= x 1)` ⇒ [`Domain::Nat`], `(>= x 0)` ⇒
/// [`Domain::WNat`] (and `(> x 0)` ≡ `x ≥ 1` over ℤ). This is exactly the shape
/// of `Lowerer::positivity` (adsmt-ir-lower): `App(App(Const(">="), Var), lit)`,
/// variable on the LEFT, bare-numeral bound on the right. Returns `(var, dom)`.
///
/// ANY other comparison — a different bound (`x ≥ 2`), an upper bound (`x ≤ n`,
/// which makes it a BOUNDED existential that routes to the native engine, §8), a
/// compound side — is unrecognized ⇒ `None`, and the caller BAILS all-or-nothing
/// (§9-B3: a dropped/mis-read guard would widen the domain and admit a spurious
/// out-of-domain witness).
fn dest_domain_guard(t: &Term) -> Option<(String, Domain)> {
    let TermInner::App(outer, rhs) = t.kind() else { return None };
    let TermInner::App(head, lhs) = outer.kind() else { return None };
    let TermInner::Const(op) = head.kind() else { return None };
    let TermInner::Var(v) = lhs.kind() else { return None };
    let TermInner::Const(bound) = rhs.kind() else { return None };
    let b = int_const(&bound.name)?;
    let (one, zero) = (BigInt::from(1), BigInt::from(0));
    match op.name.as_str() {
        ">=" if b == one => Some((v.name.clone(), Domain::Nat)),
        ">=" if b == zero => Some((v.name.clone(), Domain::WNat)),
        ">" if b == zero => Some((v.name.clone(), Domain::Nat)),
        _ => None,
    }
}

/// The stricter of two domains (`Nat ⊂ WNat ⊂ Int`) — used if one variable
/// somehow carries two recognized guards (the real lowering emits at most one).
fn narrower(a: Domain, b: Domain) -> Domain {
    match (a, b) {
        (Domain::Nat, _) | (_, Domain::Nat) => Domain::Nat,
        (Domain::WNat, _) | (_, Domain::WNat) => Domain::WNat,
        _ => Domain::Int,
    }
}

/// Classify a goal `∃x̄. ⋀ⱼ (…)` as an **existential-Diophantine** obligation
/// over ℤ, if it fits. The `∃`-body is split into conjuncts, each of which must
/// be EITHER a polynomial equation `l = r` (⇒ a system polynomial `l − r`) OR a
/// recognized Nat/WNat domain guard on a bound variable (⇒ that variable's
/// domain). **All-or-nothing (§9-B3): ANY unrecognized conjunct — an upper bound
/// (bounded ⇒ native, §8), a disequality, an uninterpreted atom, a nested
/// quantifier — makes the whole classification `None`.** This is the soundness
/// crux: unlike ideal membership (where dropping a generator is a sound
/// sub-ideal), dropping an `∃`-body conjunct WEAKENS the system and would admit a
/// witness that is not a real solution.
///
/// Hypotheses are IGNORED — a witness for the bare `∃x̄.body` proves the
/// existential conclusion regardless of the antecedents (weakening: `⊢ ∃…`
/// implies `Γ ⊢ ∃…`). Variable indices are seeded in `∃`-prefix order so the
/// `system` polynomials, the `domains` vector, and a witness `IntSolution` tuple
/// all align position-wise; a system polynomial mentioning a NON-`∃`-bound (free)
/// variable breaks that alignment ⇒ `None`.
///
/// This runs on POST-`#325`-lowered adsmt-core terms (§6.2 path ii): the Nat/WNat
/// refinement is recovered from the explicit relativization guard the lowering
/// leaves in the body (`∃x:Nat.P` → `∃x:Int. (>= x 1) ∧ P`), so no type
/// information is lost. Ring = ℤ; a witness is re-checked by [`crate::admit`]
/// against every coordinate domain AND every system polynomial.
pub fn classify_diophantine(goal: &Term) -> Option<Obligation> {
    let (var_names, body) = peel_exists(goal)?;
    let n = var_names.len();

    // DISTINCT binder names are required. The name-indexed `MPoly` representation
    // CONFLATES two `∃`-binders that share a name (shadowing, `∃x.∃x.…`): the
    // seeding loop below would create fewer index slots than `n`, desyncing the
    // `vars.len() > n` free-variable check (a free variable could then slip in
    // undetected → spurious Sat — the adversarial index-alignment break), and the
    // two semantically-distinct variables would merge onto one index anyway. The
    // real lowering assigns FRESH names (`x!k` counter), so this never costs
    // completeness; a shadowed input is soundly REFUSED.
    {
        let distinct: std::collections::BTreeSet<&String> = var_names.iter().collect();
        if distinct.len() != n {
            return None;
        }
    }

    // Seed the index map so MPoly variable `i` == `∃`-bound variable `i` (prefix
    // order). This makes `domains[i]` / the witness tuple's coordinate `i` refer
    // to the same variable the system polynomials do. (Names are now distinct, so
    // seeding creates exactly `n` slots and `vars.len() == n` here.)
    let mut vars = VarIndex::default();
    for name in &var_names {
        vars.index(name);
    }

    let mut domains = vec![Domain::Int; n];
    let mut system: Vec<MPoly> = Vec::new();

    for conj in conjuncts(&body) {
        if let Some((name, dom)) = dest_domain_guard(&conj) {
            // A guard must be on one of OUR `∃`-vars (index < n); a guard on a
            // free / not-yet-seen variable is unrecognized ⇒ bail.
            let i = vars.get(&name)?;
            if i >= n {
                return None;
            }
            domains[i] = narrower(domains[i], dom);
        } else if let Some((l, r)) = conj.dest_eq().and_then(|(l, r)| {
            Some((term_to_mpoly(&l, &mut vars)?, term_to_mpoly(&r, &mut vars)?))
        }) {
            system.push(l.sub(&r));
        } else {
            return None; // unrecognized conjunct ⇒ all-or-nothing bail (§9-B3)
        }
    }

    if system.is_empty() {
        return None; // no equation to solve
    }
    // Every variable used must be `∃`-bound (a free parameter would break the
    // domain / tuple alignment and is not a closed Diophantine system).
    if vars.len() > n {
        return None;
    }
    Some(Obligation::DiophantineExists { system, domains })
}

/// Classify a goal `¬ prime(k)` for a GROUND integer literal `k ≥ 2` as a
/// [`Compositeness`](Obligation::Compositeness) obligation. `prime` is a built-in
/// `Int → Prop` const (adsmt-ir `theory.rs`), lowered to `App(Const("prime"), k)`;
/// `composite` is NOT a const, so proving `k` NOT prime is exactly exhibiting a
/// proper divisor — `admit`'s `Divisor` re-check (`1 < d < k ∧ k mod d = 0`). A
/// divisor witness ⇒ `Sat` (k is composite) ⇒ the goal `¬prime(k)` is established.
///
/// ONLY the `¬prime` direction is a compositeness obligation: proving `prime(k)`
/// VALID needs a Pratt/ECPP **primality certificate** (the `Primality` class,
/// post-1.0 — a divisor cannot witness primality). A non-ground `prime(x)`, or
/// `k < 2` (composite undefined / `¬prime(1)` holds by unit-ness not a divisor),
/// is not recognized ⇒ `None`. The ground literal is what the lowering leaves
/// after constant-folding a numeral argument.
///
/// **PRECONDITION — `prime` must be the reserved built-in.** The re-check proves
/// the arithmetic fact "k is composite"; mapping that to `¬prime(k)` is valid
/// ONLY if `prime` denotes number-theoretic primality. The lu-kb / full-arith
/// prelude (`install_arith`) reserves `prime` as an `open` postulate the kernel
/// forbids redeclaring, so in the Verus / lu-kb path (where this classifier runs)
/// `prime` IS the built-in. The bare SMT-LIB face (`install_int_real`) does NOT
/// reserve `prime`, so a caller operating on raw SMT-LIB where a user declared
/// their own `prime` MUST NOT route it here (the integration layer, which holds
/// the `Env`, discharges this — cf. `term_to_mpoly` trusting `+`/`*`, which are
/// universally reserved and so need no such gate).
pub fn classify_compositeness(goal: &Term) -> Option<Obligation> {
    let inner = goal.dest_not()?; // ¬ (…)
    let TermInner::App(head, arg) = inner.kind() else { return None };
    let TermInner::Const(p) = head.kind() else { return None };
    if p.name != "prime" {
        return None;
    }
    let TermInner::Const(k) = arg.kind() else { return None };
    let n = int_const(&k.name)?;
    if n < BigInt::from(2) {
        return None; // composite is defined for n ≥ 2; ¬prime(1)/¬prime(0) is not a divisor fact
    }
    Some(Obligation::Compositeness { n })
}

/// The unified typed-term classifier: a sequent `hyps ⊢ goal` → a CAS
/// [`Obligation`], or `None` if it fits no recognized algebraic class. Tries
/// ideal membership (which consumes the equational hypotheses), the
/// existential-Diophantine goal shape, then a `¬prime(k)` compositeness goal.
/// The three target DISJOINT goal shapes (an equation vs a leading `∃` vs a
/// negated `prime` atom), so the order is immaterial.
pub fn classify_sequent(hyps: &[Term], goal: &Term) -> Option<Obligation> {
    classify_membership(hyps, goal)
        .or_else(|| classify_diophantine(goal))
        .or_else(|| classify_compositeness(goal))
}

/// **End-to-end CAS consult** — the one-call entry that ties the classifier to the
/// dispatcher: classify the sequent `hyps ⊢ goal`, and if it is a recognized
/// algebraic obligation, [`dispatch`](crate::dispatch) it to the manifest-enabled
/// backends and return the re-checked [`Disposition`](crate::Disposition). A
/// sequent that fits no class ⇒ `Unknown` (no backend runs). Soundness is
/// unchanged from `dispatch`: the same `Obligation` is sent to the backend and to
/// `admit`, and the classifier is a faithful all-or-nothing reflection (§6.2).
///
/// The returned `Disposition` is the **obligation-level** verdict `admit` derives
/// (membership ⇒ `Unsat` = the goal is valid; ∃-Diophantine ⇒ `Sat` = a solution
/// exists). Mapping that to a *goal* verdict for a specific query polarity is the
/// caller's (live-consult) concern — this layer certifies the algebraic fact, it
/// does not guess the query's intent.
pub fn consult(
    manifest: &crate::manifest::CasManifest,
    backends: &[&dyn crate::CasBackend],
    hyps: &[Term],
    goal: &Term,
) -> crate::Disposition {
    match classify_sequent(hyps, goal) {
        Some(ob) => crate::dispatch(manifest, backends, &ob),
        None => crate::Disposition::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Term, Type};

    fn int_ty() -> Type {
        Type::const_("Int", Kind::Type)
    }
    fn binop_ty() -> Type {
        Type::fun(int_ty(), Type::fun(int_ty(), int_ty()).unwrap()).unwrap()
    }
    fn v(name: &str) -> Term {
        Term::var(name, int_ty())
    }
    fn lit(n: i64) -> Term {
        // The BARE-numeral spelling the #325 lowering emits (adsmt-ir-lower
        // `fold_int_binop`/`as_int_lit`), NOT the engine's `int:N`. The
        // classifier consumes lowered terms; `int_const` tolerates both, but the
        // tests exercise reality ([[feedback_roundtrip_through_real_producer]]).
        Term::const_(&n.to_string(), int_ty())
    }
    fn binop(op: &str, a: Term, b: Term) -> Term {
        Term::app(Term::app(Term::const_(op, binop_ty()), a).unwrap(), b).unwrap()
    }
    fn cmp_ty() -> Type {
        Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap()
    }
    /// A Bool-typed comparison `(op a b)` — the shape the lowering emits for
    /// `Int.ge`/`Int.le`/… (`>=`/`<=` head over two Ints, Bool result).
    fn cmp(op: &str, a: Term, b: Term) -> Term {
        Term::app(Term::app(Term::const_(op, cmp_ty()), a).unwrap(), b).unwrap()
    }
    fn eq(a: Term, b: Term) -> Term {
        Term::mk_eq(a, b).unwrap()
    }
    fn conj(a: Term, b: Term) -> Term {
        Term::mk_and(a, b).unwrap()
    }
    /// `∃name:Int. body` — mirrors the lowered form (the `∃`-binder is `Int`;
    /// the Nat/WNat refinement rides as a `(>= name 1|0)` guard in `body`).
    fn exists(name: &str, body: Term) -> Term {
        Term::mk_exists(adsmt_core::Var { name: name.to_string(), ty: int_ty() }, body).unwrap()
    }
    fn not(t: Term) -> Term {
        Term::mk_not(t).unwrap()
    }
    /// `(prime k)` — the lowered EUF application of the built-in `Int → Bool` const.
    fn prime_of(k: Term) -> Term {
        let prime_ty = Type::fun(int_ty(), Type::bool_()).unwrap();
        Term::app(Term::const_("prime", prime_ty), k).unwrap()
    }

    #[test]
    fn recognizes_a_polynomial() {
        // (x*x) - 1  ⤳  v0² - 1
        let t = binop("-", binop("*", v("x"), v("x")), lit(1));
        let mut vars = VarIndex::default();
        let p = term_to_mpoly(&t, &mut vars).expect("polynomial");
        let expect = MPoly::var(0).mul(&MPoly::var(0)).sub(&MPoly::constant(BigRational::from(BigInt::from(1))));
        assert!(p.sub(&expect).is_zero());
    }

    #[test]
    fn rejects_a_non_polynomial() {
        // an uninterpreted application (f x) is not a polynomial ⇒ None.
        let f_ty = Type::fun(int_ty(), int_ty()).unwrap();
        let fx = Term::app(Term::const_("f", f_ty), v("x")).unwrap();
        let mut vars = VarIndex::default();
        assert!(term_to_mpoly(&fx, &mut vars).is_none());
        // div is not a polynomial op.
        let d = binop("div", v("x"), v("y"));
        assert!(term_to_mpoly(&d, &mut VarIndex::default()).is_none());
    }

    #[test]
    fn classifies_membership_and_admits_via_the_flow() {
        use crate::{admit, Disposition, Verdict, Witness};
        // hyp: x - 1 = 0 ; goal: x*x - 1 = 0.  x²−1 ∈ ⟨x−1⟩ with cofactor x+1.
        let hyp = eq(binop("-", v("x"), lit(1)), lit(0));
        let goal = eq(binop("-", binop("*", v("x"), v("x")), lit(1)), lit(0));
        let ob = classify_membership(std::slice::from_ref(&hyp), &goal).expect("classified");
        // The classifier built the ideal from the ORIGINAL terms; admit re-checks
        // the cofactor against it (§9-B2 satisfied — the polys are the faithful
        // reflection). Feed the (known) cofactor x+1.
        let x = MPoly::var(0);
        let one = MPoly::constant(BigRational::from(BigInt::from(1)));
        let w = Witness::Cofactors(vec![(0, x.add(&one))]);
        assert_eq!(admit(&ob, &w), Disposition::Verdict(Verdict::Unsat));
    }

    #[test]
    fn non_polynomial_goal_is_unclassified() {
        // goal mentions an uninterpreted f ⇒ not a polynomial equation ⇒ None.
        let f_ty = Type::fun(int_ty(), int_ty()).unwrap();
        let fx = Term::app(Term::const_("f", f_ty), v("x")).unwrap();
        let goal = eq(fx, lit(0));
        let hyp = eq(binop("-", v("x"), lit(1)), lit(0));
        assert!(classify_membership(&[hyp], &goal).is_none());
    }

    #[test]
    fn forbidden_ops_are_not_polynomials() {
        // div / mod / real-`/` are NOT polynomial ops ⇒ None, so they can never
        // be silently coerced into an obligation (the soundness firewall relies on
        // `term_to_mpoly` never returning a WRONG polynomial for a non-poly term).
        for op in ["div", "mod", "/"] {
            let t = binop(op, v("x"), v("y"));
            assert!(term_to_mpoly(&t, &mut VarIndex::default()).is_none(), "{op} must be None");
        }
        // abs is unary — (abs x) is likewise not a polynomial.
        let absx = Term::app(Term::const_("abs", Type::fun(int_ty(), int_ty()).unwrap()), v("x")).unwrap();
        assert!(term_to_mpoly(&absx, &mut VarIndex::default()).is_none());
    }

    // ── existential-Diophantine classifier ──────────────────────────────────

    #[test]
    fn classifies_and_admits_a_wnat_diophantine() {
        use crate::{admit, Disposition, Verdict, Witness};
        // ∃x:WNat. x*x − 4 = 0  (lowered: ∃x:Int. (>= x 0) ∧ (x*x−4 = 0)).
        let eqn = eq(binop("-", binop("*", v("x"), v("x")), lit(4)), lit(0));
        let goal = exists("x", conj(cmp(">=", v("x"), lit(0)), eqn));
        let ob = classify_diophantine(&goal).expect("classified");
        match &ob {
            Obligation::DiophantineExists { system, domains } => {
                assert_eq!(system.len(), 1);
                assert_eq!(domains, &vec![Domain::WNat]);
            }
            _ => panic!("expected DiophantineExists"),
        }
        // witness x = 2 ∈ WNat, 2²−4 = 0 ⇒ Sat.
        assert_eq!(
            admit(&ob, &Witness::IntSolution(vec![BigInt::from(2)])),
            Disposition::Verdict(Verdict::Sat)
        );
    }

    #[test]
    fn nat_guard_becomes_nat_domain() {
        // ∃x:Nat. x*x − 4 = 0  → the `(>= x 1)` guard recovers Domain::Nat.
        let eqn = eq(binop("-", binop("*", v("x"), v("x")), lit(4)), lit(0));
        let goal = exists("x", conj(cmp(">=", v("x"), lit(1)), eqn));
        let Obligation::DiophantineExists { domains, .. } =
            classify_sequent(&[], &goal).expect("classified via the dispatcher")
        else {
            panic!("expected DiophantineExists")
        };
        assert_eq!(domains, vec![Domain::Nat]);
    }

    #[test]
    fn keeps_every_conjunct_so_a_partial_witness_fails() {
        use crate::{admit, Disposition, Witness};
        // ∃x:WNat. (x*x−4 = 0) ∧ (x−3 = 0) — an inconsistent system (2 vs 3).
        // The classifier must keep BOTH conjuncts (§9-B3: dropping one would let a
        // partial witness through). No integer roots both ⇒ admit rejects each.
        let e1 = eq(binop("-", binop("*", v("x"), v("x")), lit(4)), lit(0));
        let e2 = eq(binop("-", v("x"), lit(3)), lit(0));
        let goal = exists("x", conj(cmp(">=", v("x"), lit(0)), conj(e1, e2)));
        let ob = classify_diophantine(&goal).expect("classified");
        let Obligation::DiophantineExists { system, .. } = &ob else { panic!() };
        assert_eq!(system.len(), 2, "both equations must survive");
        // x=2 roots the first but not the second; x=3 vice-versa ⇒ neither admits.
        assert_eq!(admit(&ob, &Witness::IntSolution(vec![BigInt::from(2)])), Disposition::Unknown);
        assert_eq!(admit(&ob, &Witness::IntSolution(vec![BigInt::from(3)])), Disposition::Unknown);
    }

    #[test]
    fn upper_bound_makes_it_bounded_so_classifier_bails() {
        // ∃x:WNat. (x*x−4 = 0) ∧ (x <= 10). The `<=` is neither a poly equation
        // nor a recognized domain guard ⇒ a BOUNDED existential ⇒ None (routes to
        // the native engine, §8), never a widened CAS obligation.
        let eqn = eq(binop("-", binop("*", v("x"), v("x")), lit(4)), lit(0));
        let goal = exists("x", conj(cmp(">=", v("x"), lit(0)), conj(eqn, cmp("<=", v("x"), lit(10)))));
        assert!(classify_diophantine(&goal).is_none());
    }

    #[test]
    fn free_parameter_breaks_alignment_and_bails() {
        // ∃x. x*y − 1 = 0 with `y` FREE (not ∃-bound) ⇒ the system mentions a
        // non-∃ variable ⇒ None (the domains/tuple alignment would break).
        let goal = exists("x", eq(binop("-", binop("*", v("x"), v("y")), lit(1)), lit(0)));
        assert!(classify_diophantine(&goal).is_none());
    }

    #[test]
    fn no_equation_in_the_body_is_unclassified() {
        // ∃x:Nat. (>= x 1) with no equation ⇒ nothing to solve ⇒ None.
        let goal = exists("x", cmp(">=", v("x"), lit(1)));
        assert!(classify_diophantine(&goal).is_none());
    }

    #[test]
    fn a_bare_equation_goal_is_not_diophantine() {
        // No leading ∃ ⇒ classify_diophantine None (membership may still take it).
        let goal = eq(binop("-", v("x"), lit(1)), lit(0));
        assert!(classify_diophantine(&goal).is_none());
    }

    // ── adversarial regressions (workflow cas-p16-adversarial) ──────────────

    #[test]
    fn shadowed_binders_with_a_free_var_are_refused() {
        // THE index-alignment break: ∃x.∃x. (x≥0) ∧ (y=1) with `y` FREE. Duplicate
        // binder names made `vars.len()` (=1 distinct) miscount vs n (=2), so the
        // free-var check `vars.len() > n` was `2 > 2` = false and `y` slipped in →
        // DiophantineExists{[y-1],[WNat,Int]} → admit([0,1]) spurious Sat. The
        // distinct-name guard now refuses it.
        let goal = exists("x", exists("x", conj(cmp(">=", v("x"), lit(0)), eq(v("y"), lit(1)))));
        assert!(classify_diophantine(&goal).is_none(), "shadowed free-var goal must be None");
    }

    #[test]
    fn shadowed_binders_are_refused_even_without_a_free_var() {
        // ∃x.∃x. (x≥0) ∧ (x=1): sound in principle, but the name-indexed MPoly
        // can't tell the two `x`s apart ⇒ soundly refuse rather than conflate.
        let goal = exists("x", exists("x", conj(cmp(">=", v("x"), lit(0)), eq(v("x"), lit(1)))));
        assert!(classify_diophantine(&goal).is_none());
    }

    #[test]
    fn an_unrecognized_lower_bound_bails_all_or_nothing() {
        // ∃x. (>= x 2) ∧ (x−1 = 0). `(>= x 2)` is NOT a recognized domain guard
        // (only ≥1/≥0) and not a poly equation ⇒ the whole thing is None. Were it
        // dropped, x=1 would root [x−1] but violate x≥2 ⇒ spurious Sat.
        let goal = exists("x", conj(cmp(">=", v("x"), lit(2)), eq(binop("-", v("x"), lit(1)), lit(0))));
        assert!(classify_diophantine(&goal).is_none());
        // Likewise a strict upper-adjacent bound `(> x 100)` (not `> x 0`).
        let g2 = exists("x", conj(cmp(">", v("x"), lit(100)), eq(binop("-", v("x"), lit(2)), lit(0))));
        assert!(classify_diophantine(&g2).is_none());
    }

    #[test]
    fn a_partial_application_of_an_arith_op_is_not_a_polynomial() {
        // App(Const("+"), x) — a UNARY application of the binary `+`. The two-level
        // App/App match in term_to_mpoly is the arity firewall ⇒ None, never a
        // wrong polynomial.
        let partial = Term::app(Term::const_("+", binop_ty()), v("x")).unwrap();
        assert!(term_to_mpoly(&partial, &mut VarIndex::default()).is_none());
    }

    // ── end-to-end consult (classify → dispatch → admit) ────────────────────

    struct Mock {
        caps: Vec<crate::CasCapability>,
        reply: crate::CasReply,
    }
    impl crate::CasBackend for Mock {
        fn name(&self) -> &'static str {
            "mock"
        }
        fn capabilities(&self) -> &[crate::CasCapability] {
            &self.caps
        }
        fn decide(&self, _: &Obligation) -> crate::CasReply {
            self.reply.clone()
        }
    }

    #[test]
    fn consult_classifies_then_dispatches_a_membership_sequent() {
        use crate::{CasBackend, CasCapability, CasClass, CasReply, Disposition, Verdict, Witness, WitnessedDir};
        // hyp: x − 1 = 0 ; goal: x*x − 1 = 0 ⇒ membership, cofactor x+1 ⇒ Unsat.
        let hyp = eq(binop("-", v("x"), lit(1)), lit(0));
        let goal = eq(binop("-", binop("*", v("x"), v("x")), lit(1)), lit(0));
        let x = MPoly::var(0);
        let one = MPoly::constant(BigRational::from(BigInt::from(1)));
        let mock = Mock {
            caps: vec![CasCapability { class: CasClass::IdealMembership, witnessed: WitnessedDir::Unsat }],
            reply: CasReply::Witnessed(Witness::Cofactors(vec![(0, x.add(&one))])),
        };
        let backends: Vec<&dyn CasBackend> = vec![&mock];
        let m = crate::manifest::CasManifest::from_adsmt_toml("[cas]\nenabled=[\"mock\"]\n").unwrap();
        assert_eq!(consult(&m, &backends, std::slice::from_ref(&hyp), &goal), Disposition::Verdict(Verdict::Unsat));
    }

    #[test]
    fn consult_on_an_unclassifiable_goal_is_unknown_without_running_a_backend() {
        use crate::{CasBackend, Disposition};
        // A goal that fits no algebraic class ⇒ Unknown; the (would-panic) backend
        // is never consulted because classify_sequent returns None first.
        struct Boom;
        impl CasBackend for Boom {
            fn name(&self) -> &'static str { "boom" }
            fn capabilities(&self) -> &[crate::CasCapability] { panic!("must not be consulted") }
            fn decide(&self, _: &Obligation) -> crate::CasReply { panic!("must not be consulted") }
        }
        let f_ty = Type::fun(int_ty(), int_ty()).unwrap();
        let goal = eq(Term::app(Term::const_("f", f_ty), v("x")).unwrap(), lit(0));
        let backends: Vec<&dyn CasBackend> = vec![&Boom];
        let m = crate::manifest::CasManifest::from_adsmt_toml("[cas]\nenabled=[\"boom\"]\n").unwrap();
        assert_eq!(consult(&m, &backends, &[], &goal), Disposition::Unknown);
    }

    #[test]
    fn consult_with_no_eligible_backend_is_unknown() {
        use crate::{CasBackend, Disposition};
        // Classifiable (∃-Diophantine) but the manifest enables nothing ⇒ Unknown.
        let goal = exists("x", conj(cmp(">=", v("x"), lit(0)), eq(binop("-", binop("*", v("x"), v("x")), lit(4)), lit(0))));
        let backends: Vec<&dyn CasBackend> = vec![];
        let m = crate::manifest::CasManifest::default();
        assert_eq!(consult(&m, &backends, &[], &goal), Disposition::Unknown);
    }

    // ── compositeness (¬prime(k)) classifier ────────────────────────────────

    #[test]
    fn classifies_and_admits_not_prime_of_a_composite() {
        use crate::{admit, Disposition, Verdict, Witness};
        // goal ¬prime(91), 91 = 7·13. Divisor 7 ⇒ composite ⇒ Sat.
        let ob = classify_compositeness(&not(prime_of(lit(91)))).expect("classified");
        assert!(matches!(&ob, Obligation::Compositeness { n } if *n == BigInt::from(91)));
        assert_eq!(
            admit(&ob, &Witness::Divisor(BigInt::from(7))),
            Disposition::Verdict(Verdict::Sat)
        );
        // A non-divisor is rejected (7 ∤ 90 here would be), and a prime target
        // admits no proper divisor at all:
        let prime97 = classify_compositeness(&not(prime_of(lit(97)))).expect("classified");
        assert_eq!(admit(&prime97, &Witness::Divisor(BigInt::from(7))), Disposition::Unknown);
    }

    #[test]
    fn compositeness_only_recognizes_the_not_prime_direction_on_a_ground_n_ge_2() {
        // bare prime(91) (not negated) ⇒ not a compositeness obligation (proving
        // primality needs a cert, not a divisor).
        assert!(classify_compositeness(&prime_of(lit(91))).is_none());
        // ¬prime(x) with x a variable ⇒ not ground ⇒ None.
        assert!(classify_compositeness(&not(prime_of(v("x")))).is_none());
        // ¬prime(1) ⇒ true, but by unit-ness, not a proper divisor ⇒ None (n < 2).
        assert!(classify_compositeness(&not(prime_of(lit(1)))).is_none());
        // routed through the unified entry.
        let ob = classify_sequent(&[], &not(prime_of(lit(15)))).expect("routed");
        assert!(matches!(ob, Obligation::Compositeness { n } if n == BigInt::from(15)));
    }
}
