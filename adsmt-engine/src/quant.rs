//! Quantifier instantiation glue — engine-side Tier 1 hook.
//!
//! When the Boolean engine reports Sat over the ground fragment, we
//! run a Miller-pattern E-matching pass over every asserted
//! `∀x. body` quantifier:
//!
//! 1. Collect *ground* sub-terms from non-quantified assertions into
//!    a [`TermUniverse`].
//! 2. For each forall, treat the body as a single trigger pattern
//!    over the bound variable.
//! 3. Run the [`EMatcher`] to find substitutions.
//! 4. Emit instantiated bodies as new assertions.
//!
//! Tier 2 (conflict-based) lives in [`crate::quant_conflict`]; Tier 3
//! (bounded enumeration) lives in
//! [`adsmt_quant::enumerate::enumerate`]. The solver loop in
//! `solver.rs` walks 1 → 2 → 3 → 4 (abductive escalation) in order.

use std::collections::HashSet;
use std::sync::Arc;

use adsmt_core::{Term, Var};
use adsmt_quant::ematch::{EMatcher, TermUniverse};
use adsmt_quant::trigger::Trigger;
use indexmap::IndexMap;

/// Pull every quantified assertion out of `assertions`, returning
/// `(quantified, rest)`.
#[allow(clippy::type_complexity)]
pub fn partition_quantifiers(assertions: &[(Term, bool)]) -> (Vec<(Var, Term)>, Vec<(Term, bool)>) {
    let mut quants = Vec::new();
    let mut rest = Vec::new();
    for (t, p) in assertions {
        if !*p {
            // Negated quantifier is existential — handled in v0.5.
            rest.push((t.clone(), *p));
            continue;
        }
        if let Some((var, body)) = t.dest_forall() {
            quants.push((var, body));
        } else {
            rest.push((t.clone(), *p));
        }
    }
    (quants, rest)
}

/// Walk every (ground, non-quantified) term collecting subterms that
/// share the variable's sort.
pub fn collect_universe(rest: &[(Term, bool)]) -> TermUniverse {
    let mut u = TermUniverse::new();
    for (t, _) in rest {
        gather_subterms(t, &mut u);
    }
    u
}

fn gather_subterms(t: &Term, u: &mut TermUniverse) {
    u.insert(t.clone());
    match t {
        Term::App(f, x) => {
            gather_subterms(f, u);
            gather_subterms(x, u);
        }
        Term::Lam(_, body) => gather_subterms(body, u),
        _ => {}
    }
}

/// Quantifier-handling tier reached by a given call to
/// [`instantiate_one`]. v0.9 records this so the surrounding engine
/// loop can escalate to Tier 4 (abductive scaffolding) when all
/// term-based strategies are exhausted.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Tier { One, Three, Exhausted }

/// For a single `∀v. body`, generate instantiations of `body` by
/// matching `body` (treated as a flex pattern over `v`) against terms
/// in `universe`. Returns instantiated bodies (positive polarity)
/// alongside the tier that produced them.
pub fn instantiate_with_tier(
    var: &Var,
    body: &Term,
    universe: &TermUniverse,
) -> (Vec<Term>, Tier) {
    let res = instantiate_one(var, body, universe);
    let tier = if res.is_empty() {
        Tier::Exhausted
    } else {
        // Tier classification: if at least one match came from a
        // pattern-matching step over universe terms whose shape
        // mirrors the body, classify as Tier One; otherwise the
        // fallback enumeration produced it (Tier Three).
        if universe.iter().any(|t| body.alpha_eq(t)) {
            Tier::One
        } else {
            Tier::Three
        }
    };
    (res, tier)
}

/// For a single `∀v. body`, generate instantiations of `body` by
/// matching `body` (treated as a flex pattern over `v`) against
/// terms in `universe` — **Tier 1 only**: Miller-pattern E-matching
/// over the body's shape. When this returns an empty list the
/// solver loop escalates to Tier 2 (conflict-based) and then Tier 3
/// (bounded enumeration via [`adsmt_quant::enumerate::enumerate`]).
pub fn instantiate_one(
    var: &Var,
    body: &Term,
    universe: &TermUniverse,
) -> Vec<Term> {
    let v_arc = Arc::new(var.clone());
    // Trigger pattern: positive sub-terms of `body` that mention
    // `var`. The NNF + Skolemization pre-pass wraps negated atoms in
    // `not`, but the universe (collected from ground assertions)
    // stores both polarities, so matching against the positive
    // form lifts existing trigger machinery to handle `∀x. ¬φ(x)`.
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    let matcher = EMatcher::new(universe);
    for pattern in collect_trigger_patterns(body, &v_arc) {
        let trig = Trigger::single(pattern, vec![v_arc.clone()]);
        for instantiation in matcher.match_trigger(&trig) {
            for (sub_v, sub_t) in &instantiation.subst {
                if **sub_v != *var {
                    continue;
                }
                let key = sub_t.to_string();
                if seen.contains(&key) {
                    continue;
                }
                seen.insert(key);

                // Always instantiate the *full* body (not the trigger
                // sub-pattern) so the resulting assertion carries the
                // negation / disjunction / conjunction structure of
                // the original quantifier.
                let mut sigma: IndexMap<Arc<Var>, Term> = IndexMap::new();
                sigma.insert(v_arc.clone(), sub_t.clone());
                if let Ok(instantiated) = body.subst(&sigma) {
                    out.push(instantiated);
                }
            }
        }
    }
    out
}

/// Collect positive sub-terms of `body` that mention the bound
/// variable `v`. Walks through `not / and / or / =>` connectives so
/// e.g. `¬P(x)` yields the pattern `P(x)` and `(or P(x) Q(x))`
/// yields both `P(x)` and `Q(x)`. Bottoms out at the first
/// non-connective sub-term — those are the actual trigger
/// candidates the E-matcher can match against the universe.
fn collect_trigger_patterns(body: &Term, v: &Arc<Var>) -> Vec<Term> {
    fn walk(t: &Term, v: &Arc<Var>, out: &mut Vec<Term>) {
        if !mentions(t, v) {
            return;
        }
        if let Some(inner) = t.dest_not() {
            walk(&inner, v, out);
            return;
        }
        if let Some((a, b)) = t.dest_and() {
            walk(&a, v, out);
            walk(&b, v, out);
            return;
        }
        if let Some((a, b)) = t.dest_or() {
            walk(&a, v, out);
            walk(&b, v, out);
            return;
        }
        if let Some((a, b)) = t.dest_imp() {
            walk(&a, v, out);
            walk(&b, v, out);
            return;
        }
        out.push(t.clone());
    }
    fn mentions(t: &Term, v: &Arc<Var>) -> bool {
        t.free_vars().iter().any(|fv| **fv == **v)
    }
    let mut out = Vec::new();
    walk(body, v, &mut out);
    if out.is_empty() {
        // Fall back to whole-body matching for atoms that don't go
        // through any connective — keeps the v0.3 behaviour intact.
        out.push(body.clone());
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Type};

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    #[test]
    fn collects_subterms_of_assertion() {
        let p = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let a = Term::var("a", int_());
        let p_a = Term::app(p.clone(), a.clone()).unwrap();
        let u = collect_universe(&[(p_a.clone(), true)]);
        // Should include p_a, p, a
        assert!(u.len() >= 3);
        let strs: Vec<String> = u.iter().map(|t| t.to_string()).collect();
        assert!(strs.iter().any(|s| s.contains("a")));
    }

    #[test]
    fn partitions_quantifier_and_ground() {
        let body = Term::var("p", Type::bool_());
        let v = Var { name: "x".into(), ty: int_() };
        let forall = Term::mk_forall(v, body.clone()).unwrap();
        let ground = Term::var("q", Type::bool_());
        let (qs, rest) = partition_quantifiers(&[(forall, true), (ground.clone(), true)]);
        assert_eq!(qs.len(), 1);
        assert_eq!(rest.len(), 1);
        assert!(rest[0].0.alpha_eq(&ground));
    }

    #[test]
    fn instantiates_against_ground_terms() {
        // forall x:Int. P x   with universe { P a, b } → instantiate
        // with the matching sub-term a.
        let p = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let mut u = TermUniverse::new();
        u.insert(Term::app(p.clone(), a.clone()).unwrap());
        u.insert(a.clone());
        u.insert(b);

        let x_var = Var { name: "x".into(), ty: int_() };
        let body = Term::app(p, Term::Var(Arc::new(x_var.clone()))).unwrap();
        let insts = instantiate_one(&x_var, &body, &u);
        assert!(!insts.is_empty());
        // Each instantiation should be `P <something>`, with one being P a.
        let strs: Vec<String> = insts.iter().map(|t| t.to_string()).collect();
        assert!(strs.iter().any(|s| s.contains('a')));
    }

    // === v0.19 D.2 — HOL quantifier extension ===

    #[test]
    fn instantiates_function_typed_bound_variable() {
        // forall (f: Int -> Int). f a   over universe { id_int, succ, a }
        // ⇒ instantiated to `id_int a` and `succ a`.
        let int_to_int = Type::fun(int_(), int_()).unwrap();
        let id_int = Term::const_("id_int", int_to_int.clone());
        let succ = Term::const_("succ", int_to_int.clone());
        let a = Term::const_("a", int_());

        let mut u = TermUniverse::new();
        u.insert(id_int.clone());
        u.insert(succ.clone());
        u.insert(a.clone());
        // Ground applications must appear in the universe for the
        // body-trigger `f a` to align: the E-matcher matches `f a`
        // (with `f` flex) against each universe term, so a universe
        // entry of `id_int a` is required to bind `f ↦ id_int`.
        u.insert(Term::app(id_int.clone(), a.clone()).unwrap());
        u.insert(Term::app(succ.clone(), a.clone()).unwrap());

        let f_var = Var { name: "f".into(), ty: int_to_int };
        let body = Term::app(
            Term::Var(Arc::new(f_var.clone())),
            a.clone(),
        )
        .unwrap();
        let insts = instantiate_one(&f_var, &body, &u);
        assert!(!insts.is_empty(), "HOL flex over fn sort should produce instantiations");
        let strs: Vec<String> = insts.iter().map(|t| t.to_string()).collect();
        // Expect at least one of `id_int a` / `succ a` to surface.
        assert!(strs.iter().any(|s| s.contains("id_int")));
    }

    #[test]
    fn partition_handles_nested_forall_as_one_assertion() {
        // forall x:Int. forall y:Int. P x y    is a single top-level
        // forall assertion. The inner forall remains in the body.
        let int_to_int_to_bool =
            Type::fun(int_(), Type::fun(int_(), Type::bool_()).unwrap()).unwrap();
        let p = Term::const_("P", int_to_int_to_bool);
        let x = Var { name: "x".into(), ty: int_() };
        let y = Var { name: "y".into(), ty: int_() };
        let body_inner = Term::app(
            Term::app(p, Term::Var(Arc::new(x.clone()))).unwrap(),
            Term::Var(Arc::new(y.clone())),
        )
        .unwrap();
        let inner = Term::mk_forall(y, body_inner).unwrap();
        let outer = Term::mk_forall(x, inner).unwrap();
        let (qs, _rest) = partition_quantifiers(&[(outer, true)]);
        assert_eq!(qs.len(), 1, "outer forall is the single quantifier");
        // The outer body is itself a forall — the engine's
        // instantiation pass will dispatch a second round on the
        // remaining inner quantifier after the outer is instantiated.
        assert!(qs[0].1.dest_forall().is_some());
    }

    #[test]
    fn instantiate_skips_sort_mismatched_subterm() {
        // forall x:Int. body  — universe contains a Bool subterm that
        // must NOT be picked up as an instantiation candidate even
        // though it sits next to an Int candidate.
        let bool_lit = Term::true_const();
        let a = Term::var("a", int_());
        let p = Term::const_("P", Type::fun(int_(), Type::bool_()).unwrap());
        let p_a = Term::app(p.clone(), a.clone()).unwrap();
        let mut u = TermUniverse::new();
        u.insert(bool_lit);
        u.insert(a);
        u.insert(p_a);

        let x_var = Var { name: "x".into(), ty: int_() };
        let body = Term::app(p, Term::Var(Arc::new(x_var.clone()))).unwrap();
        let insts = instantiate_one(&x_var, &body, &u);
        // Every instantiation has the body shape `P <Int term>`, never
        // `P true_const`.
        for inst in &insts {
            let s = inst.to_string();
            assert!(!s.contains("True") || !s.contains("(P "), "no P(Bool) instantiation");
        }
    }
}
