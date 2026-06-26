//! M2.6 conformance: **mutual induction**. A group of inductives declared
//! together, whose constructors cross-reference each other's types
//! (`Tree`/`Forest`, `Even`/`Odd`). The recursors are independent (a
//! self-recursive argument gets an IH; a cross-reference does not), which
//! is sound; mutual recursors are a later step.

use adsmt_ir::{
    Env, MutualMember, Term, Univ, declare_inductive, declare_mutual, define, is_def_eq,
    postulate, type_of,
};

fn nat() -> Term {
    Term::cnst("Nat")
}
fn s(n: Term) -> Term {
    Term::app(Term::cnst("S"), n)
}
fn o() -> Term {
    Term::cnst("O")
}
fn nat_env() -> Env {
    let mut env = Env::new();
    declare_inductive(
        &mut env,
        "Nat",
        vec![],
        Univ::Type(0),
        vec![("O".into(), vec![]), ("S".into(), vec![nat()])],
    )
    .unwrap();
    env
}

/// `plus` by guarded recursion (for the mutual-recursor size measure).
fn define_plus(env: &mut Env) {
    let m_s = Term::lam(nat(), s(Term::apps(Term::bound(3), [Term::bound(0), Term::bound(1)])));
    let body = Term::lam(
        nat(),
        Term::lam(
            nat(),
            Term::mtch("Nat", Term::lam(nat(), nat()), vec![Term::bound(0), m_s], Term::bound(1)),
        ),
    );
    let ty = Term::arrow(nat(), Term::arrow(nat(), nat()));
    define(env, "plus", ty.clone(), Term::fix(0, ty, body)).unwrap();
}

/// Declare the `Tree`/`Forest` mutual group used by several tests.
fn tree_forest(env: &mut Env) {
    declare_mutual(
        env,
        vec![
            MutualMember {
                name: "Tree".into(),
                params: vec![],
                indices: vec![],
                sort: Univ::Type(0),
                ctors: vec![("node".into(), vec![Term::cnst("Forest")], vec![])],
            },
            MutualMember {
                name: "Forest".into(),
                params: vec![],
                indices: vec![],
                sort: Univ::Type(0),
                ctors: vec![
                    ("fnil".into(), vec![], vec![]),
                    (
                        "fcons".into(),
                        vec![Term::cnst("Tree"), Term::cnst("Forest")],
                        vec![],
                    ),
                ],
            },
        ],
    )
    .unwrap();
}

/// `Tree`/`Forest`: `node : Forest → Tree`, `fnil : Forest`,
/// `fcons : Tree → Forest → Forest`. `Tree` references `Forest` and vice
/// versa — only simultaneous declaration makes both type-check.
#[test]
fn tree_forest_mutual() {
    let mut env = nat_env();
    declare_mutual(
        &mut env,
        vec![
            MutualMember {
                name: "Tree".into(),
                params: vec![],
                indices: vec![],
                sort: Univ::Type(0),
                // node : Forest → Tree   (cross-reference to Forest, no IH)
                ctors: vec![("node".into(), vec![Term::cnst("Forest")], vec![])],
            },
            MutualMember {
                name: "Forest".into(),
                params: vec![],
                indices: vec![],
                sort: Univ::Type(0),
                ctors: vec![
                    ("fnil".into(), vec![], vec![]),
                    // fcons : Tree → Forest → Forest  (Forest self-recursive)
                    (
                        "fcons".into(),
                        vec![Term::cnst("Tree"), Term::cnst("Forest")],
                        vec![],
                    ),
                ],
            },
        ],
    )
    .unwrap();

    // Constructors type-check at the expected (cross-referencing) types.
    let leaf = Term::app(Term::cnst("node"), Term::cnst("fnil")); // node fnil : Tree
    assert!(is_def_eq(&env, &type_of(&env, &leaf).unwrap(), &Term::cnst("Tree")));
    let f1 = Term::apps(Term::cnst("fcons"), [leaf.clone(), Term::cnst("fnil")]); // : Forest
    assert!(is_def_eq(&env, &type_of(&env, &f1).unwrap(), &Term::cnst("Forest")));

    // The independent recursor for Forest still works: count the top-level
    // trees in a forest by recursion on the (self-recursive) Forest tail.
    // Forest.rec (λ_.Nat) [O (fnil), λ(t)(rest)(ih). S ih (fcons)]
    let motive = Term::lam(Term::cnst("Forest"), nat());
    let m_fnil = Term::cnst("O");
    // fcons method : Π(t:Tree)(rest:Forest)(ih:Nat). S ih   (t has no IH)
    let m_fcons = Term::lam(
        Term::cnst("Tree"),
        Term::lam(
            Term::cnst("Forest"),
            Term::lam(nat(), Term::app(Term::cnst("S"), Term::bound(0))),
        ),
    );
    let count = |f: Term| Term::elim("Forest", motive.clone(), vec![m_fnil.clone(), m_fcons.clone()], f);
    let f2 = Term::apps(Term::cnst("fcons"), [leaf, f1]);
    // count fnil = 0, count [leaf,leaf] = 2
    assert!(is_def_eq(&env, &count(Term::cnst("fnil")), &Term::cnst("O")));
    assert!(
        is_def_eq(
            &env,
            &count(f2),
            &Term::app(Term::cnst("S"), Term::app(Term::cnst("S"), Term::cnst("O")))
        ),
        "count of a 2-tree forest = 2"
    );
}

/// `Even`/`Odd` as mutually-recursive predicates over `Nat` (indexed):
/// `ev0 : Even 0`, `evS : Π n. Odd n → Even (S n)`,
/// `odS : Π n. Even n → Odd (S n)`.
#[test]
fn even_odd_mutual_indexed() {
    let mut env = nat_env();
    let s = |n: Term| Term::app(Term::cnst("S"), n);
    declare_mutual(
        &mut env,
        vec![
            MutualMember {
                name: "Even".into(),
                params: vec![],
                indices: vec![nat()],
                sort: Univ::Prop,
                ctors: vec![
                    // ev0 : Even 0
                    ("ev0".into(), vec![], vec![Term::cnst("O")]),
                    // evS : Π(n:Nat). Odd n → Even (S n)
                    (
                        "evS".into(),
                        vec![nat(), Term::apps(Term::cnst("Odd"), [Term::bound(0)])],
                        vec![s(Term::bound(1))],
                    ),
                ],
            },
            MutualMember {
                name: "Odd".into(),
                params: vec![],
                indices: vec![nat()],
                sort: Univ::Prop,
                ctors: vec![
                    // odS : Π(n:Nat). Even n → Odd (S n)
                    (
                        "odS".into(),
                        vec![nat(), Term::apps(Term::cnst("Even"), [Term::bound(0)])],
                        vec![s(Term::bound(1))],
                    ),
                ],
            },
        ],
    )
    .unwrap();

    // Even 2 is inhabited: evS 1 (odS 0 ev0).
    let p0 = Term::cnst("ev0"); // : Even 0
    let p1 = Term::apps(Term::cnst("odS"), [Term::cnst("O"), p0]); // : Odd 1
    let p2 = Term::apps(Term::cnst("evS"), [s(Term::cnst("O")), p1]); // : Even 2
    let ty = type_of(&env, &p2).unwrap();
    let expected = Term::apps(Term::cnst("Even"), [s(s(Term::cnst("O")))]);
    assert!(is_def_eq(&env, &ty, &expected), "evS 1 (odS 0 ev0) : Even 2");
}

/// Mutual positivity is enforced over the whole group: a group member in a
/// **negative** position (left of an arrow) is rejected.
#[test]
fn rejects_negative_cross_reference() {
    let mut env = nat_env();
    // Bad references its sibling Sib negatively: mk : (Sib → Bad) → Bad.
    let r = declare_mutual(
        &mut env,
        vec![
            MutualMember {
                name: "Bad".into(),
                params: vec![],
                indices: vec![],
                sort: Univ::Type(0),
                ctors: vec![(
                    "mk".into(),
                    vec![Term::arrow(Term::cnst("Sib"), Term::cnst("Bad"))],
                    vec![],
                )],
            },
            MutualMember {
                name: "Sib".into(),
                params: vec![],
                indices: vec![],
                sort: Univ::Type(0),
                ctors: vec![("s0".into(), vec![], vec![])],
            },
        ],
    );
    assert!(r.is_err(), "a negative cross-reference must be rejected");
    assert!(env.inductive("Bad").is_none() && env.inductive("Sib").is_none());
}

// ── Mutual RECURSORS (the M2.7 cross-member-IH eliminator) ──────────────

/// The mutual recursor computes **across members** with cross-member IHs —
/// the thing the independent recursor cannot express. `treeSize`/
/// `forestSize` defined as one `MutElim` pair.
#[test]
fn mutual_recursor_tree_size() {
    let mut env = nat_env();
    define_plus(&mut env);
    tree_forest(&mut env);

    // motives (group order [Tree, Forest]): both ↦ Nat.
    let motives = vec![
        Term::lam(Term::cnst("Tree"), nat()),
        Term::lam(Term::cnst("Forest"), nat()),
    ];
    // minors (member, ctor order): [node, fnil, fcons]
    //   node f  (ih_f : forestSize f) ↦ S ih_f          (a tree = 1 + its forest)
    //   fnil                          ↦ O
    //   fcons t rest (ih_t)(ih_rest)  ↦ plus ih_t ih_rest
    let m_node = Term::lam(Term::cnst("Forest"), Term::lam(nat(), s(Term::bound(0))));
    let m_fnil = o();
    let m_fcons = Term::lam(
        Term::cnst("Tree"),
        Term::lam(
            Term::cnst("Forest"),
            Term::lam(
                nat(),
                Term::lam(nat(), Term::apps(Term::cnst("plus"), [Term::bound(1), Term::bound(0)])),
            ),
        ),
    );
    let minors = vec![m_node, m_fnil, m_fcons];
    let tree_size =
        |t: Term| Term::mutelim("Tree", motives.clone(), minors.clone(), t);

    let leaf = Term::app(Term::cnst("node"), Term::cnst("fnil")); // node fnil
    // treeSize(leaf) = 1
    assert!(is_def_eq(&env, &tree_size(leaf.clone()), &s(o())), "size(node fnil) = 1");
    // and it type-checks to Nat
    assert!(is_def_eq(&env, &type_of(&env, &tree_size(leaf.clone())).unwrap(), &nat()));

    // tree2 = node (fcons leaf fnil) — root + one child leaf ⇒ size 2
    let f1 = Term::apps(Term::cnst("fcons"), [leaf, Term::cnst("fnil")]);
    let tree2 = Term::app(Term::cnst("node"), f1);
    assert!(is_def_eq(&env, &tree_size(tree2), &s(s(o()))), "size(node [leaf]) = 2");
}

/// A mutual recursor over an **indexed, `Prop`-sorted** group (`Even`/`Odd`),
/// eliminating into `Prop` (small elimination, allowed). Exercises index
/// recovery + per-member motive validation + cross-member methods.
#[test]
fn mutual_recursor_even_odd_into_prop() {
    let mut env = nat_env();
    postulate(&mut env, "Top", Term::prop()).unwrap();
    postulate(&mut env, "tt", Term::cnst("Top")).unwrap();
    declare_mutual(
        &mut env,
        vec![
            MutualMember {
                name: "Even".into(),
                params: vec![],
                indices: vec![nat()],
                sort: Univ::Prop,
                ctors: vec![
                    ("ev0".into(), vec![], vec![o()]),
                    (
                        "evS".into(),
                        vec![nat(), Term::apps(Term::cnst("Odd"), [Term::bound(0)])],
                        vec![s(Term::bound(1))],
                    ),
                ],
            },
            MutualMember {
                name: "Odd".into(),
                params: vec![],
                indices: vec![nat()],
                sort: Univ::Prop,
                ctors: vec![(
                    "odS".into(),
                    vec![nat(), Term::apps(Term::cnst("Even"), [Term::bound(0)])],
                    vec![s(Term::bound(1))],
                )],
            },
        ],
    )
    .unwrap();

    // motives: λn.λ_:Even n. Top  and  λn.λ_:Odd n. Top
    let motives = vec![
        Term::lam(nat(), Term::lam(Term::apps(Term::cnst("Even"), [Term::bound(0)]), Term::cnst("Top"))),
        Term::lam(nat(), Term::lam(Term::apps(Term::cnst("Odd"), [Term::bound(0)]), Term::cnst("Top"))),
    ];
    // minors (member,ctor order): [ev0, evS, odS], each ↦ tt (Top has one proof)
    let m_ev0 = Term::cnst("tt");
    // evS : Π(n)(o:Odd n). method Π(n)(o:Odd n)(ih:P_Odd n o = Top). Top  ↦ λn.λo.λih. tt
    let m_evs = Term::lam(
        nat(),
        Term::lam(Term::apps(Term::cnst("Odd"), [Term::bound(0)]), Term::lam(Term::cnst("Top"), Term::cnst("tt"))),
    );
    let m_ods = Term::lam(
        nat(),
        Term::lam(Term::apps(Term::cnst("Even"), [Term::bound(0)]), Term::lam(Term::cnst("Top"), Term::cnst("tt"))),
    );
    let minors = vec![m_ev0, m_evs, m_ods];

    // ev0 : Even 0
    let elim = Term::mutelim("Even", motives, minors, Term::cnst("ev0"));
    let ty = type_of(&env, &elim).unwrap();
    // result = P_Even 0 ev0 = Top
    assert!(is_def_eq(&env, &ty, &Term::cnst("Top")), "Even.mrec … ev0 : Top");
}

/// R1: a mutual recursor requires a shared parameter telescope — a group
/// whose members differ in params is rejected.
#[test]
fn rejects_mutual_recursor_differing_params() {
    let mut env = nat_env();
    declare_mutual(
        &mut env,
        vec![
            MutualMember {
                name: "AA".into(),
                params: vec![Term::type_(0)], // 1 param
                indices: vec![],
                sort: Univ::Type(0),
                ctors: vec![("mkA".into(), vec![], vec![])],
            },
            MutualMember {
                name: "BB".into(),
                params: vec![], // 0 params — differs
                indices: vec![],
                sort: Univ::Type(0),
                ctors: vec![("mkB".into(), vec![], vec![])],
            },
        ],
    )
    .unwrap();
    // a mutual eliminator over this group must be rejected (shared-params R1).
    let motives = vec![
        Term::lam(Term::apps(Term::cnst("AA"), [nat()]), nat()),
        Term::lam(Term::cnst("BB"), nat()),
    ];
    let elim = Term::mutelim(
        "BB",
        motives,
        vec![o(), o()],
        Term::cnst("mkB"),
    );
    assert!(type_of(&env, &elim).is_err(), "differing-params mutual recursor must be rejected");
}

/// R4 / P0-3: **large elimination from a `Prop` member into `Type`** must be
/// rejected per-member — the central adversarial landmine (a Prop member's
/// motive landing in `Type`, even when the major is at another member, is the
/// classic Prop+large-elim inconsistency).
#[test]
fn rejects_mutual_large_elim_from_prop_member() {
    let mut env = nat_env();
    // Even/Odd, both Prop.
    declare_mutual(
        &mut env,
        vec![
            MutualMember {
                name: "Even".into(),
                params: vec![],
                indices: vec![nat()],
                sort: Univ::Prop,
                ctors: vec![
                    ("ev0".into(), vec![], vec![o()]),
                    (
                        "evS".into(),
                        vec![nat(), Term::apps(Term::cnst("Odd"), [Term::bound(0)])],
                        vec![s(Term::bound(1))],
                    ),
                ],
            },
            MutualMember {
                name: "Odd".into(),
                params: vec![],
                indices: vec![nat()],
                sort: Univ::Prop,
                ctors: vec![(
                    "odS".into(),
                    vec![nat(), Term::apps(Term::cnst("Even"), [Term::bound(0)])],
                    vec![s(Term::bound(1))],
                )],
            },
        ],
    )
    .unwrap();
    // Motives into Type0 (large elimination) — must be rejected. The actual
    // minors are irrelevant; the per-member Prop guard fires first.
    let motives = vec![
        Term::lam(nat(), Term::lam(Term::apps(Term::cnst("Even"), [Term::bound(0)]), nat())),
        Term::lam(nat(), Term::lam(Term::apps(Term::cnst("Odd"), [Term::bound(0)]), nat())),
    ];
    let elim = Term::mutelim("Even", motives, vec![o(), o(), o()], Term::cnst("ev0"));
    assert!(
        type_of(&env, &elim).is_err(),
        "large elimination from a Prop member into Type must be rejected"
    );
}

/// R5: a mutual recursor with the wrong number of minor premises is rejected.
#[test]
fn rejects_mutual_recursor_wrong_minor_count() {
    let mut env = nat_env();
    tree_forest(&mut env);
    let motives = vec![
        Term::lam(Term::cnst("Tree"), nat()),
        Term::lam(Term::cnst("Forest"), nat()),
    ];
    // group has 3 constructors total (node, fnil, fcons); give 2 minors.
    let elim = Term::mutelim(
        "Tree",
        motives,
        vec![o(), o()],
        Term::app(Term::cnst("node"), Term::cnst("fnil")),
    );
    assert!(type_of(&env, &elim).is_err());
}
