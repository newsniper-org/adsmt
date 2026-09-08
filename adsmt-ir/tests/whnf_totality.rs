// The kernel's head reduction must TERMINATE on every environment it can be
// handed, not only on the ones the checked admitters build.
//
// `Env::declare` is `pub` and documented as unchecked ("this is `pub` only so
// out-of-kernel tooling can rebuild a known-good environment"), and the lu-kb
// face used it to admit a mutual `fn` group. The two shapes below are exactly
// what that produced, and both were measured before the fix:
//
//   f x = g x,      g x = f x        →  spins forever (flat δ/β cycle)
//   f x = g x + 1,  g x = f x + 1    →  stack overflow at ~3850 frames
//
// Neither term HAS a weak head normal form, so the honest result is the term
// itself, unreduced. These tests pin that `whnf` returns at all; what it
// returns is only required to be sound (stuck), not reduced.

use adsmt_ir::{Decl, Env, Modality, Term, is_def_eq, postulate, whnf};

/// `f`/`g` mutually defined through the raw, unchecked admitter.
fn cyclic_env(with_arith: bool) -> Env {
    let mut env = Env::new();
    postulate(&mut env, "A", Term::type_(0)).unwrap();
    let a = Term::cnst("A");
    let ty = Term::pi(a.clone(), a.clone());
    // The bodies mention each other, so both must exist first.
    postulate(&mut env, "f", ty.clone()).unwrap();
    postulate(&mut env, "g", ty.clone()).unwrap();
    postulate(&mut env, "h", Term::pi(a.clone(), ty.clone())).unwrap();
    let call = |n: &str| Term::apps(Term::cnst(n), [Term::bound(0)]);
    let (fb, gb) = if with_arith {
        // `f x = h (g x) x` — the recursive call sits under an argument, so
        // the reduction nests instead of looping flat. This is the shape that
        // overflowed the stack.
        (
            Term::lam(a.clone(), Term::apps(Term::cnst("h"), [call("g"), Term::bound(0)])),
            Term::lam(a.clone(), Term::apps(Term::cnst("h"), [call("f"), Term::bound(0)])),
        )
    } else {
        (Term::lam(a.clone(), call("g")), Term::lam(a.clone(), call("f")))
    };
    env.declare("f".into(), Decl { ty: ty.clone(), modality: Modality::Def(fb) });
    env.declare("g".into(), Decl { ty, modality: Modality::Def(gb) });
    postulate(&mut env, "c", a).unwrap();
    env
}

#[test]
fn a_flat_delta_cycle_returns_stuck_instead_of_spinning() {
    let env = cyclic_env(false);
    let t = Term::apps(Term::cnst("f"), [Term::cnst("c")]);
    let w = whnf(&env, &t);
    // Sound: whatever comes back must still be about `f`/`g` applied to `c`.
    let s = format!("{w}");
    assert!(s.contains('c'), "{s}");
}

#[test]
fn a_nested_delta_cycle_returns_stuck_instead_of_overflowing() {
    let env = cyclic_env(true);
    let t = Term::apps(Term::cnst("f"), [Term::cnst("c")]);
    let _ = whnf(&env, &t);
}

/// Conversion is built on `whnf`, so it inherits the totality.
#[test]
fn conversion_over_a_cyclic_definition_terminates() {
    let env = cyclic_env(false);
    let a = Term::cnst("A");
    // `f c` vs `f ((λy.y) c)` — convertible, and NOT syntactically equal, so
    // the `a == b` short-circuit in `is_def_eq` does not fire.
    let id_c = Term::apps(Term::lam(a, Term::bound(0)), [Term::cnst("c")]);
    let lhs = Term::apps(Term::cnst("f"), [Term::cnst("c")]);
    let rhs = Term::apps(Term::cnst("f"), [id_c]);
    let _ = is_def_eq(&env, &lhs, &rhs);
}

/// The cut must not poison the memo. A term reduced under a truncation is not
/// cached, so an unrelated later reduction of a NON-cyclic term is unaffected.
#[test]
fn a_cut_does_not_poison_the_conversion_cache() {
    let mut env = cyclic_env(false);
    let a = Term::cnst("A");
    // A perfectly ordinary definition in the same env.
    let ok_ty = Term::pi(a.clone(), a.clone());
    postulate(&mut env, "d", a.clone()).unwrap();
    let k_body = Term::lam(a, Term::cnst("d"));
    adsmt_ir::define(&mut env, "k", ok_ty, k_body).unwrap();
    // Force a cut first.
    let _ = whnf(&env, &Term::apps(Term::cnst("f"), [Term::cnst("c")]));
    // `k c` must still reduce to `d`.
    let w = whnf(&env, &Term::apps(Term::cnst("k"), [Term::cnst("c")]));
    assert_eq!(format!("{w}"), "d");
}

/// Nesting a definition inside ITSELF is not a cycle: `k (k c)` reduces `k`
/// twice on one path and must still reduce. A guard keyed on the CONSTANT
/// rather than the term would wrongly cut here.
#[test]
fn a_definition_nested_inside_itself_still_reduces() {
    let mut env = Env::new();
    postulate(&mut env, "A", Term::type_(0)).unwrap();
    let a = Term::cnst("A");
    postulate(&mut env, "c", a.clone()).unwrap();
    // `k x = x`
    adsmt_ir::define(
        &mut env,
        "k",
        Term::pi(a.clone(), a.clone()),
        Term::lam(a, Term::bound(0)),
    )
    .unwrap();
    let inner = Term::apps(Term::cnst("k"), [Term::cnst("c")]);
    let outer = Term::apps(Term::cnst("k"), [inner]);
    assert_eq!(format!("{}", whnf(&env, &outer)), "c");
}
