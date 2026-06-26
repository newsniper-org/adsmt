//! M3-1 conformance: the **AOT-bank as an admission journal**. The bank is
//! built and reloaded through the **real producer** (the checked admitters),
//! per the rc.34.1 lesson — a hand-built payload can pass while the actual
//! produce→encode→decode→re-admit path is broken. The soundness property:
//! loading a bank *re-admits* every declaration, so a loaded `Env` behaves
//! identically to the freshly-elaborated one, and a bad/incompatible/corrupt
//! bank is rejected (⇒ the caller falls through to elaboration), never trusted.

use adsmt_ir::{
    BankError, Decl, Env, Modality, MutualMember, Term, Univ, bank_decode, bank_encode,
    declare_inductive, declare_inductive_indexed, declare_mutual, define, is_def_eq, postulate,
    type_of,
};

fn nat() -> Term {
    Term::cnst("Nat")
}
fn o() -> Term {
    Term::cnst("O")
}
fn s(n: Term) -> Term {
    Term::app(Term::cnst("S"), n)
}
fn num(n: u32) -> Term {
    (0..n).fold(o(), |acc, _| s(acc))
}

/// A rich, multi-paradigm prelude built **only** through the checked admitters
/// — exercising every `AdmissionStep` kind (`postulate`, `define` with `Fix`/
/// `Match`/`Let`/`Elim`, non-indexed + parameterized + indexed `Inductive`,
/// and a `Mutual` group).
fn rich_prelude() -> Env {
    let mut env = Env::new();
    // inductive Nat
    declare_inductive(
        &mut env,
        "Nat",
        vec![],
        Univ::Type(0),
        vec![("O".into(), vec![]), ("S".into(), vec![nat()])],
    )
    .unwrap();
    // open z : Nat
    postulate(&mut env, "z", nat()).unwrap();
    // parameterized inductive List
    declare_inductive(
        &mut env,
        "List",
        vec![Term::type_(0)],
        Univ::Type(0),
        vec![
            ("nil".into(), vec![]),
            ("cons".into(), vec![Term::bound(0), Term::apps(Term::cnst("List"), [Term::bound(1)])]),
        ],
    )
    .unwrap();
    // plus : Nat → Nat → Nat   (guarded fix + Match)
    let m_s = Term::lam(nat(), s(Term::apps(Term::bound(3), [Term::bound(0), Term::bound(1)])));
    let plus_body = Term::lam(
        nat(),
        Term::lam(
            nat(),
            Term::mtch("Nat", Term::lam(nat(), nat()), vec![Term::bound(0), m_s], Term::bound(1)),
        ),
    );
    let plus_ty = Term::arrow(nat(), Term::arrow(nat(), nat()));
    define(&mut env, "plus", plus_ty.clone(), Term::fix(0, plus_ty, plus_body)).unwrap();
    // len : List Nat → Nat   (fix over a parameterized inductive)
    let list_nat = Term::apps(Term::cnst("List"), [nat()]);
    let m_cons =
        Term::lam(nat(), Term::lam(list_nat.clone(), s(Term::apps(Term::bound(3), [Term::bound(0)]))));
    let len_body = Term::lam(
        list_nat.clone(),
        Term::mtch("List", Term::lam(list_nat.clone(), nat()), vec![o(), m_cons], Term::bound(0)),
    );
    let len_ty = Term::arrow(list_nat.clone(), nat());
    define(&mut env, "len", len_ty.clone(), Term::fix(0, len_ty, len_body)).unwrap();
    // idnat : Nat → Nat   (covers Term::Let)
    define(
        &mut env,
        "idnat",
        Term::arrow(nat(), nat()),
        Term::lam(nat(), Term::let_(nat(), Term::bound(0), Term::bound(0))),
    )
    .unwrap();
    // double : Nat → Nat   via the recursor (covers Term::Elim): O↦O, S k↦S(S ih)
    let s_method = Term::lam(nat(), Term::lam(nat(), s(s(Term::bound(0)))));
    let double_body = Term::lam(
        nat(),
        Term::elim("Nat", Term::lam(nat(), nat()), vec![o(), s_method], Term::bound(0)),
    );
    define(&mut env, "double", Term::arrow(nat(), nat()), double_body).unwrap();
    // indexed inductive Vec (GADT)
    declare_inductive_indexed(
        &mut env,
        "Vec",
        vec![Term::type_(0)],
        vec![nat()],
        Univ::Type(0),
        vec![
            ("vnil".into(), vec![], vec![o()]),
            (
                "vcons".into(),
                vec![
                    nat(),
                    Term::bound(1),
                    Term::apps(Term::cnst("Vec"), [Term::bound(2), Term::bound(1)]),
                ],
                vec![s(Term::bound(2))],
            ),
        ],
    )
    .unwrap();
    // mutual Tree / Forest
    declare_mutual(
        &mut env,
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
                    ("fcons".into(), vec![Term::cnst("Tree"), Term::cnst("Forest")], vec![]),
                ],
            },
        ],
    )
    .unwrap();
    env
}

/// A battery of positive and negative checks that must hold *identically* on a
/// freshly-built and a bank-loaded `Env` — the proof that loading is faithful.
fn assert_battery(env: &Env) {
    // computations (ι/μ) reduce identically
    let plus = |a: Term, b: Term| Term::apps(Term::cnst("plus"), [a, b]);
    assert!(is_def_eq(env, &plus(num(2), num(1)), &num(3)), "plus 2 1 = 3");
    assert!(is_def_eq(env, &Term::app(Term::cnst("double"), num(3)), &num(6)), "double 3 = 6");
    assert!(is_def_eq(env, &Term::app(Term::cnst("idnat"), num(4)), &num(4)), "idnat 4 = 4");
    let nil = Term::app(Term::cnst("nil"), nat());
    let cons = |h: Term, t: Term| Term::apps(Term::cnst("cons"), [nat(), h, t]);
    let l2 = cons(Term::cnst("z"), cons(Term::cnst("z"), nil));
    assert!(is_def_eq(env, &Term::app(Term::cnst("len"), l2), &num(2)), "len [z,z] = 2");

    // a dependent (GADT) type computes: vcons Nat 0 z vnil : Vec Nat 1
    let vnil = Term::app(Term::cnst("vnil"), nat());
    let v1 = Term::apps(Term::cnst("vcons"), [nat(), o(), Term::cnst("z"), vnil]);
    let v1_ty = type_of(env, &v1).unwrap();
    assert!(is_def_eq(env, &v1_ty, &Term::apps(Term::cnst("Vec"), [nat(), num(1)])), "Vec Nat 1");

    // a mutual constructor types: node fnil : Tree
    let node = Term::app(Term::cnst("node"), Term::cnst("fnil"));
    assert!(is_def_eq(env, &type_of(env, &node).unwrap(), &Term::cnst("Tree")), "node fnil : Tree");

    // negative: an ill-typed application is rejected (O applied to O)
    assert!(type_of(env, &Term::app(o(), o())).is_err(), "O O must not type-check");
}

#[test]
fn rich_prelude_round_trips_through_real_producer() {
    let env = rich_prelude();
    assert_battery(&env); // sanity on the source

    let bytes = bank_encode(&env).expect("encode");
    let loaded = bank_decode(&bytes).expect("decode");

    // the loaded Env replays the same admission sequence AND behaves
    // identically (the journal round-trips; the declaration count matches).
    assert_eq!(env.journal(), loaded.journal(), "loaded admission journal differs");
    assert_eq!(env.len(), loaded.len());
    assert_battery(&loaded);

    // re-encoding the loaded Env reproduces the same bytes (determinism)
    assert_eq!(bank_encode(&loaded).unwrap(), bytes);
}

#[test]
fn incomplete_journal_is_rejected_on_encode() {
    // an Env that used the raw, journal-less `declare` cannot be banked: the
    // self-check detects the journal would not reproduce it.
    let mut env = rich_prelude();
    env.declare("rawextra".to_string(), Decl { ty: Term::type_(0), modality: Modality::Open });
    assert_eq!(bank_encode(&env), Err(BankError::IncompleteJournal));
}

#[test]
fn corruption_is_rejected() {
    let good = bank_encode(&rich_prelude()).unwrap();
    assert!(bank_decode(&good).is_ok());

    // bad magic
    let mut m = good.clone();
    m[0] ^= 0xFF;
    assert_eq!(bank_decode(&m).unwrap_err(), BankError::BadMagic);

    // unsupported format version (checked before the digest)
    let mut v = good.clone();
    v[8] = 99;
    assert_eq!(bank_decode(&v).unwrap_err(), BankError::UnsupportedFormat(99));

    // a flipped payload byte → digest mismatch
    let mut p = good.clone();
    let last = p.len() - 1;
    p[last] ^= 0x01;
    assert_eq!(bank_decode(&p).unwrap_err(), BankError::DigestMismatch);

    // a flipped digest byte → digest mismatch
    let mut d = good.clone();
    d[20] ^= 0x01;
    assert_eq!(bank_decode(&d).unwrap_err(), BankError::DigestMismatch);

    // truncation
    assert_eq!(bank_decode(&good[..good.len() - 1]).unwrap_err(), BankError::Truncated);
    assert_eq!(bank_decode(&good[..20]).unwrap_err(), BankError::Truncated);
    assert_eq!(bank_decode(&[]).unwrap_err(), BankError::Truncated);
}

/// Single-byte corruption anywhere in a real bank must always yield a result
/// (some `BankError`, or — vanishingly unlikely — an `Ok`), **never a panic**.
#[test]
fn single_byte_corruption_never_panics() {
    let good = bank_encode(&rich_prelude()).unwrap();
    for i in 0..good.len() {
        let mut bad = good.clone();
        bad[i] ^= 0xFF;
        // a panic here fails the test; we only require non-panic.
        let _ = bank_decode(&bad);
    }
}
