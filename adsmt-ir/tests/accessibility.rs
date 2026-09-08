// What the kernel can already host of WELL-FOUNDED recursion, measured.
//
// `rec fn f(…) decreases [m] = …` is refused today (3efcc89): the surface
// branch that admits a non-structural recursion on a termination argument does
// not exist. The design (docs/design/LUKB_SUCCESSOR_SURFACE.md §11) says that
// branch "reduces it to `Acc`", and nothing had ever checked whether the kernel
// can express `Acc` at all. It can, with one constraint that decides the route.
//
// These tests are the record. They pin the two facts a future slice needs and
// will fail loudly if either changes.

use adsmt_ir::{Ctx, Env, Term, Univ, declare_inductive_indexed, infer, postulate};

/// `A`, `R : A → A → Prop`, and `B` — the ambient signature.
fn signature() -> Env {
    let mut env = Env::new();
    postulate(&mut env, "A", Term::type_(0)).unwrap();
    let a = Term::cnst("A");
    postulate(&mut env, "R", Term::pi(a.clone(), Term::pi(a.clone(), Term::prop()))).unwrap();
    postulate(&mut env, "B", Term::type_(0)).unwrap();
    env
}

/// `acc_intro : Π(x : A). (Π(y : A). R y x → Acc y) → Acc x`.
///
/// `x` is a constructor ARGUMENT, not a binder standing for the index: a
/// constructor's telescope is checked under the PARAMETERS only
/// (`process_constructor`), so an index is never in scope there, and the
/// conclusion's index expression is written over the arguments instead. Coq
/// declares the same inductive with `x` as an index; the two differ only in
/// where `x` is bound, and that difference is what the second test is about.
fn declare_acc(env: &mut Env, sort: Univ) -> Result<(), adsmt_ir::TypeError> {
    let a = Term::cnst("A");
    // under arg0 (`x`): inside the `y` binder, y = Bound(0) and x = Bound(1);
    // `arrow` shifts its codomain, so `Acc y` is written `Bound(0)` there.
    let hyp = Term::pi(
        a.clone(),
        Term::arrow(
            Term::apps(Term::cnst("R"), [Term::bound(0), Term::bound(1)]),
            Term::apps(Term::cnst("Acc"), [Term::bound(0)]),
        ),
    );
    declare_inductive_indexed(
        env,
        "Acc",
        vec![],
        vec![a.clone()],
        sort,
        vec![("acc_intro".to_string(), vec![a, hyp], vec![Term::bound(1)])],
    )
}

/// The introduction rule is admitted — including strict positivity, which is
/// the interesting part: `Acc` occurs under two function domains
/// (`Π(y : A). R y x → _`), and only in the CODOMAIN, so the occurrence is
/// positive and the checker accepts it.
#[test]
fn acc_is_a_genuine_inductive_the_kernel_admits() {
    let mut env = signature();
    declare_acc(&mut env, Univ::Type(0)).expect("Acc declares");
    let ty = env.lookup("acc_intro").expect("acc_intro").ty.to_string();
    assert!(ty.contains("Acc"), "{ty}");
}

/// The constraint that decides the route: at `Prop` the recursor cannot
/// eliminate into a computational sort, and a function justified by an
/// accessibility proof returns DATA.
///
/// Coq admits `Acc_rect` by the singleton criterion — one constructor, every
/// argument either a parameter or `Prop`-sorted. This encoding cannot meet it,
/// because `x : A` is a constructor argument at `Type` rather than an index.
/// So a future slice either declares `Acc` at `Type(0)` (what the next test
/// shows works, and what costs nothing here — this kernel has no proof
/// irrelevance to preserve) or teaches `process_constructor` to bind indices.
#[test]
fn acc_in_prop_cannot_eliminate_into_data() {
    let mut env = signature();
    declare_acc(&mut env, Univ::Prop).expect("Acc declares in Prop too");
    let a = Term::cnst("A");
    postulate(&mut env, "x0", a.clone()).unwrap();
    postulate(&mut env, "h0", Term::apps(Term::cnst("Acc"), [Term::cnst("x0")])).unwrap();
    let motive = Term::lam(
        a,
        Term::lam(Term::apps(Term::cnst("Acc"), [Term::bound(0)]), Term::cnst("B")),
    );
    let e = Term::elim("Acc", motive, vec![Term::cnst("B")], Term::cnst("h0"));
    let err = infer(&env, &Ctx::new(), &e).expect_err("large elimination is refused");
    assert!(format!("{err}").contains("large elimination"), "{err}");
}

/// At `Type(0)` the elimination is accepted, and the minor premise the kernel
/// demands IS the well-founded recursion step:
///
/// ```text
/// Π(x : A).
/// Π(h : Π(y : A). R y x → Acc y).
/// Π(ih : Π(y : A). Π(r : R y x). P y (h y r)).
///   P x (acc_intro x h)
/// ```
///
/// So the recursion scheme needs no kernel change — only a way to OBTAIN the
/// `Acc` argument, which is the open half: the surface has no proof terms, and
/// postulating well-foundedness is the non-recheckable trust source §11 rules
/// out. The route left is to CONSTRUCT the accessibility proof, which the
/// kernel would then check like any other term.
#[test]
fn acc_in_type_gives_exactly_the_well_founded_recursion_step() {
    let mut env = signature();
    declare_acc(&mut env, Univ::Type(0)).expect("Acc declares");
    let a = Term::cnst("A");
    postulate(&mut env, "x0", a.clone()).unwrap();
    postulate(&mut env, "h0", Term::apps(Term::cnst("Acc"), [Term::cnst("x0")])).unwrap();
    let motive = Term::lam(
        a,
        Term::lam(Term::apps(Term::cnst("Acc"), [Term::bound(0)]), Term::cnst("B")),
    );
    // A deliberately wrong minor premise, so the error names the type the
    // kernel wants — that expected type is the assertion.
    let e = Term::elim("Acc", motive, vec![Term::cnst("B")], Term::cnst("h0"));
    let err = format!("{}", infer(&env, &Ctx::new(), &e).expect_err("B is not the step"));
    assert!(!err.contains("large elimination"), "elimination itself is fine: {err}");
    // The step binds `x`, the accessibility hypothesis, and one induction
    // hypothesis per recursive sub-call.
    assert!(err.contains("acc_intro"), "the step's conclusion is about acc_intro: {err}");
    assert!(err.contains("R"), "the induction hypothesis is guarded by R: {err}");
}
