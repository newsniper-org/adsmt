// A mutually recursive group of DEFINITIONS goes in through a checked
// admitter, or not at all.
//
// No member of such a group can go through `define`: each body mentions the
// others, so none type-checks until all the signatures exist, and once they do
// `define` refuses the name as already declared. The lu-kb face worked around
// that with `Env::declare` — the raw insertion the kernel documents as
// unchecked — which skipped the admission journal (so the group could never be
// banked) and skipped every termination check. `f x = g x, g x = f x` was
// admitted, and the kernel's head reduction then had no normal form to find.

use adsmt_ir::{
    Env, Term, bank_decode, bank_encode, define_mutual, is_def_eq, postulate, whnf,
};

/// `Peano`, and the `ev`/`od` pair over it — the structural mutual group.
fn peano_env() -> Env {
    let mut env = Env::new();
    adsmt_ir::declare_inductive(
        &mut env,
        "Peano",
        vec![],
        adsmt_ir::Univ::Type(0),
        vec![
            ("zero".to_string(), vec![]),
            ("succ".to_string(), vec![Term::cnst("Peano")]),
        ],
    )
    .expect("Peano");
    postulate(&mut env, "B", Term::type_(0)).unwrap();
    postulate(&mut env, "tt", Term::cnst("B")).unwrap();
    postulate(&mut env, "ff", Term::cnst("B")).unwrap();
    env
}

/// `λn. match n { zero => base, succ(k) => other k }` — the body of one member.
fn member_body(base: &str, other: &str) -> Term {
    let motive = Term::lam(Term::cnst("Peano"), Term::cnst("B"));
    Term::lam(
        Term::cnst("Peano"),
        Term::mtch(
            "Peano".to_string(),
            motive,
            vec![
                Term::cnst(base),
                // succ's argument is `Bound(0)` inside the minor premise
                Term::lam(Term::cnst("Peano"), Term::apps(Term::cnst(other), [Term::bound(0)])),
            ],
            Term::bound(0),
        ),
    )
}

fn ev_od_group() -> Vec<(String, Term, Term)> {
    let ty = Term::pi(Term::cnst("Peano"), Term::cnst("B"));
    vec![
        ("ev".to_string(), ty.clone(), member_body("tt", "od")),
        ("od".to_string(), ty, member_body("ff", "ev")),
    ]
}

#[test]
fn a_structurally_decreasing_group_is_admitted_and_computes() {
    let mut env = peano_env();
    define_mutual(&mut env, &ev_od_group()).expect("the group destructures its argument");
    let two = Term::apps(
        Term::cnst("succ"),
        [Term::apps(Term::cnst("succ"), [Term::cnst("zero")])],
    );
    assert_eq!(format!("{}", whnf(&env, &Term::apps(Term::cnst("ev"), [two.clone()]))), "tt");
    assert_eq!(format!("{}", whnf(&env, &Term::apps(Term::cnst("od"), [two]))), "ff");
}

/// The face postulates the signatures first so the bodies can be elaborated;
/// the admitter must accept that starting state and upgrade them.
#[test]
fn signatures_may_already_be_postulated() {
    let mut env = peano_env();
    let ty = Term::pi(Term::cnst("Peano"), Term::cnst("B"));
    postulate(&mut env, "ev", ty.clone()).unwrap();
    postulate(&mut env, "od", ty).unwrap();
    define_mutual(&mut env, &ev_od_group()).expect("postulated signatures are upgraded");
    assert_eq!(
        format!("{}", whnf(&env, &Term::apps(Term::cnst("ev"), [Term::cnst("zero")]))),
        "tt"
    );
}

/// The defect this admitter exists to prevent. `f x = g x`, `g x = f x` passes
/// type-checking and has no structural measure at all.
#[test]
fn a_group_with_no_structural_measure_is_refused() {
    let mut env = Env::new();
    postulate(&mut env, "A", Term::type_(0)).unwrap();
    let a = Term::cnst("A");
    let ty = Term::pi(a.clone(), a.clone());
    let group = vec![
        (
            "f".to_string(),
            ty.clone(),
            Term::lam(a.clone(), Term::apps(Term::cnst("g"), [Term::bound(0)])),
        ),
        (
            "g".to_string(),
            ty,
            Term::lam(a, Term::apps(Term::cnst("f"), [Term::bound(0)])),
        ),
    ];
    let e = define_mutual(&mut env, &group).expect_err("no argument decreases");
    assert!(format!("{e}").contains("structurally decreasing"), "{e}");
    // And the refusal leaves NOTHING behind — not even the signatures.
    assert!(env.lookup("f").is_none(), "a refused group must not half-admit");
    assert!(env.lookup("g").is_none());
}

/// A member escaping into a non-call position defeats the measure, so it is
/// refused even though the calls that DO appear are decreasing.
#[test]
fn a_member_used_outside_a_guarded_call_is_refused() {
    let mut env = peano_env();
    postulate(
        &mut env,
        "apply",
        Term::pi(Term::pi(Term::cnst("Peano"), Term::cnst("B")), Term::cnst("B")),
    )
    .unwrap();
    let ty = Term::pi(Term::cnst("Peano"), Term::cnst("B"));
    // `ev n = apply od` — `od` is passed, not called.
    let group = vec![
        (
            "ev".to_string(),
            ty.clone(),
            Term::lam(Term::cnst("Peano"), Term::apps(Term::cnst("apply"), [Term::cnst("od")])),
        ),
        ("od".to_string(), ty, member_body("ff", "ev")),
    ];
    define_mutual(&mut env, &group).expect_err("a bare group member is not guarded");
}

/// The body is TYPE-CHECKED, which the raw `declare` never did.
#[test]
fn a_body_that_contradicts_its_signature_is_refused() {
    let mut env = peano_env();
    let ty = Term::pi(Term::cnst("Peano"), Term::cnst("B"));
    let mut group = ev_od_group();
    // `ev : Peano → B` with a body returning a `Peano`.
    group[0].2 = Term::lam(Term::cnst("Peano"), Term::cnst("zero"));
    group[0].1 = ty;
    define_mutual(&mut env, &group).expect_err("the body has the wrong sort");
}

/// The journal half: a banked env must reload, and `bank_encode` self-checks
/// that by replaying. A group admitted through the raw `declare` failed that
/// check (`IncompleteJournal`) — the bodies were simply not in the journal.
#[test]
fn a_mutual_group_survives_a_bank_round_trip() {
    let mut env = peano_env();
    define_mutual(&mut env, &ev_od_group()).unwrap();
    let bytes = bank_encode(&env).expect("the group is journalled");
    let back = bank_decode(&bytes).expect("and replays through the checked admitters");
    // The replay re-ran the guard and the type-check, and produced the same
    // reduction behaviour.
    let one = Term::apps(Term::cnst("succ"), [Term::cnst("zero")]);
    let call = Term::apps(Term::cnst("ev"), [one]);
    assert!(is_def_eq(&back, &whnf(&back, &call), &Term::cnst("ff")));
}
