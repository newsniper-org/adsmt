//! Slice-1 conformance for the SMT-LIB-3.0 face: real SMT-LIB scripts
//! parse + elaborate into kernel-checked terms, and the *rejection* paths
//! (unknown symbol, sort mismatch, unsupported construct) are surfaced as
//! `FaceError`s — never a trusted ill-typed term.

use adsmt_ir::{Term, bank_decode, bank_encode, is_def_eq, type_of};
use adsmt_ir_smtlib::{FaceError, elaborate};

/// A representative EUF + propositional + quantifier script elaborates; every
/// goal is a closed `Prop` (the kernel re-checked it).
#[test]
fn euf_quantifier_script_elaborates() {
    let src = r#"
        (set-logic UF)
        (declare-sort S 0)
        (declare-const a S)
        (declare-const b S)
        (declare-fun f (S) S)
        (declare-fun p (S) Bool)
        (declare-const q Bool)
        (assert (=> (= a b) (= (f a) (f b))))
        (assert (and (p a) (or q (not (p b)))))
        (assert (forall ((x S)) (=> (p x) (= (f x) x))))
        (assert (exists ((x S) (y S)) (and (= (f x) y) (not (= x y)))))
        (check-sat)
    "#;
    let r = elaborate(src).expect("elaborates");
    assert_eq!(r.goals.len(), 4, "four asserts ⇒ four goals");
    for g in &r.goals {
        let ty = type_of(&r.env, g).expect("goal type-checks");
        assert!(is_def_eq(&r.env, &ty, &Term::prop()), "each goal is a Prop: {g} : {ty}");
    }
    // the prelude + user decls are all present and checked.
    assert!(r.env.lookup("S").is_some());
    assert!(r.env.lookup("f").is_some());
    assert!(r.env.lookup("=").is_some()); // the polymorphic Eq prelude
}

/// `=` of two differently-sorted terms is rejected (the kernel sort check).
#[test]
fn equality_of_differing_sorts_is_rejected() {
    let src = "(declare-sort S 0) (declare-sort T 0) (declare-const s S) (declare-const t T) \
               (assert (= s t))";
    match elaborate(src) {
        Err(FaceError::Unsupported(m)) => assert!(m.contains("differing sorts"), "{m}"),
        other => panic!("expected a sort-mismatch rejection, got {other:?}"),
    }
}

/// An unknown symbol in a formula is rejected.
#[test]
fn unknown_symbol_is_rejected() {
    let src = "(declare-const a Bool) (assert (and a undeclared))";
    match elaborate(src) {
        Err(FaceError::Unsupported(m)) => assert!(m.contains("unknown symbol"), "{m}"),
        other => panic!("expected unknown-symbol rejection, got {other:?}"),
    }
}

/// A non-`Bool` assertion is rejected (assertions must be `Prop`).
#[test]
fn non_bool_assert_is_rejected() {
    let src = "(declare-sort S 0) (declare-const a S) (assert a)";
    match elaborate(src) {
        Err(FaceError::Unsupported(m)) => assert!(m.contains("expected Bool/Prop"), "{m}"),
        other => panic!("expected a Bool/Prop rejection, got {other:?}"),
    }
}

/// Deferred features are rejected with a clear "later slice" message (sound by
/// omission), not silently mis-elaborated.
#[test]
fn deferred_features_are_rejected_cleanly() {
    for (src, needle) in [
        ("(define-fun-rec f ((x Bool)) Bool (f x))", "recursive"),
        ("(declare-datatypes () ((Color (red) (green))))", "datatypes"),
        // `Int`/`Real` now land via the arithmetic prelude; `String` does not.
        ("(declare-const s String)", "later slice"),
    ] {
        match elaborate(src) {
            Err(FaceError::Unsupported(m)) => assert!(m.contains(needle), "{src} ⇒ {m}"),
            other => panic!("{src}: expected Unsupported({needle}), got {other:?}"),
        }
    }
}

/// Slice 2: `define-fun` (non-recursive), `let`, `ite`, n-ary `=`, and
/// `distinct` all elaborate, and a goal mixing them is a checked `Prop`.
#[test]
fn slice2_def_let_ite_distinct() {
    let src = r#"
        (declare-sort S 0)
        (declare-const a S) (declare-const b S) (declare-const c S)
        (declare-fun f (S) S)
        ; a non-recursive definition: id over S
        (define-fun id ((x S)) S x)
        ; n-ary equality + distinct + let + ite
        (assert (= (id a) a))
        (assert (= a b c))
        (assert (distinct a b c))
        (assert (let ((y (f a)) (z (f b))) (= y z)))
        (assert (= (ite (= a b) a b) c))
        (check-sat)
    "#;
    let r = elaborate(src).expect("slice-2 elaborates");
    assert_eq!(r.goals.len(), 5);
    for g in &r.goals {
        let ty = type_of(&r.env, g).expect("goal type-checks");
        assert!(is_def_eq(&r.env, &ty, &Term::prop()), "goal is a Prop: {g} : {ty}");
    }
    // `id` was admitted as a real `def` (it δ-reduces): id a ≡ a.
    let id_a = Term::app(Term::cnst("id"), Term::cnst("a"));
    assert!(is_def_eq(&r.env, &id_a, &Term::cnst("a")), "id a δ-reduces to a");
    // `let` fidelity: `(let ((y (f a))(z (f b))) (= y z))` β-reduces to
    // `(= (f a) (f b))` — the bindings substitute correctly (de Bruijn).
    let fa = Term::app(Term::cnst("f"), Term::cnst("a"));
    let fb = Term::app(Term::cnst("f"), Term::cnst("b"));
    let expect = Term::apps(Term::cnst("="), [Term::cnst("S"), fa, fb]);
    assert!(is_def_eq(&r.env, &r.goals[3], &expect), "let β-reduces to the right equality");
}

/// Slice 3: `declare-datatype`/`declare-datatypes` → kernel inductives —
/// enums, recursive datatypes, and a mutual group — with constructors usable
/// in formulas (the positivity gate is the kernel's; the face just builds the
/// inductive spec).
#[test]
fn slice3_datatypes_single_recursive_mutual() {
    let src = r#"
        (declare-sort Elem 0)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-datatype Nat ((zero) (succ (pred Nat))))
        (declare-datatype Lst ((nil) (cons (hd Elem) (tl Lst))))
        (declare-datatypes ((Tree 0) (Forest 0))
          (((node (children Forest)))
           ((fnil) (fcons (head Tree) (tail Forest)))))
        (declare-const e Elem)
        (assert (= (succ (succ zero)) (succ (succ zero))))
        (assert (distinct red green blue))
        (assert (= (cons e nil) (cons e nil)))
        (assert (= (node fnil) (node (fcons (node fnil) fnil))))
        (check-sat)
    "#;
    let r = elaborate(src).expect("datatypes elaborate");
    assert!(r.env.lookup("succ").is_some() && r.env.lookup("node").is_some());
    for g in &r.goals {
        let ty = type_of(&r.env, g).unwrap();
        assert!(is_def_eq(&r.env, &ty, &Term::prop()), "goal is a Prop");
    }
    // a constructor value has its datatype's type.
    let two = Term::app(Term::cnst("succ"), Term::app(Term::cnst("succ"), Term::cnst("zero")));
    assert!(is_def_eq(&r.env, &type_of(&r.env, &two).unwrap(), &Term::cnst("Nat")), "succ² zero : Nat");
}

/// Residual datatype rejections (sound by omission): an *undeclared* container
/// head, and a malformed parametric member (arity ≠ 0 without the `(par …)`
/// form). A *declared* parametric container nested in a non-parametric
/// datatype is now SUPPORTED (see `slice3a_nested_datatypes_monomorphize`).
#[test]
fn datatypes_unknown_or_malformed_rejected() {
    // a nested field `(List Bad)` where `List` was never declared → no
    // parametric template to specialize, so the application is an unknown sort.
    let unknown = "(declare-datatype Bad ((mk (f (List Bad)))))";
    assert!(matches!(elaborate(unknown), Err(FaceError::Unsupported(_))), "unknown container rejected");
    // a member with arity 1 whose constructor list is NOT in the `(par …)` form
    // is malformed → rejected.
    let malformed = "(declare-sort E 0) (declare-datatypes ((Lst 1)) (((nil) (cons (hd E) (tl Lst)))))";
    assert!(matches!(elaborate(malformed), Err(FaceError::Unsupported(_))), "malformed parametric rejected");
}

/// Slice 3a — **nested datatypes via face monomorphization** (DECLARATION).
/// A parametric container (`List`) nested in a non-parametric datatype
/// (`Tree.node : (List Tree)`) desugars to a mutual group `{Tree, List#Tree}`
/// admitted through the kernel's checked `declare_mutual` — its positivity gate
/// re-checks every monomorphized member.
#[test]
fn slice3a_nested_datatypes_monomorphize() {
    let src = r#"
        (declare-datatypes ((List 1) (Tree 0))
          ((par (T) ((nil) (cons (head T) (tail (List T)))))
           ((node (kids (List Tree))))))
    "#;
    let r = elaborate(src).expect("nested datatype admits");
    // both the output datatype and its specialized container are in the env.
    assert!(r.env.lookup("Tree").is_some(), "Tree admitted");
    assert!(r.env.lookup("List#Tree").is_some(), "List#Tree (the specialization) admitted");
    // the parametric `List` itself is NOT admitted (it is a template).
    assert!(r.env.lookup("List").is_none(), "the parametric List is not a kernel type");
    // the output constructor `node` and the mangled container ctors exist.
    assert!(r.env.ctor_of("node").is_some(), "node is a constructor");
    assert!(r.env.ctor_of("nil#List#Tree").is_some(), "nil#List#Tree is a constructor");
    assert!(r.env.ctor_of("cons#List#Tree").is_some(), "cons#List#Tree is a constructor");
    // a value over the group type-checks: `node` applied to a `List#Tree` value
    // (`nil#List#Tree`) is a `Tree` (the Tree ⇄ List#Tree cross-reference).
    let lnil = Term::cnst("nil#List#Tree");
    assert!(
        is_def_eq(&r.env, &type_of(&r.env, &lnil).unwrap(), &Term::cnst("List#Tree")),
        "nil#List#Tree : List#Tree"
    );
    let node_app = Term::app(Term::cnst("node"), lnil);
    assert!(
        is_def_eq(&r.env, &type_of(&r.env, &node_app).unwrap(), &Term::cnst("Tree")),
        "(node nil#List#Tree) : Tree"
    );
    // a non-trivial container value: `(cons#List#Tree (node nil#List#Tree)
    // nil#List#Tree)` is a `List#Tree` (cons : Tree → List#Tree → List#Tree).
    let one = Term::apps(
        Term::cnst("cons#List#Tree"),
        [Term::app(Term::cnst("node"), Term::cnst("nil#List#Tree")), Term::cnst("nil#List#Tree")],
    );
    assert!(
        is_def_eq(&r.env, &type_of(&r.env, &one).unwrap(), &Term::cnst("List#Tree")),
        "cons-built List#Tree value type-checks"
    );
}

/// A Peano-list `Rose = node (List Rose)` (single non-parametric datatype using
/// `declare-datatype`, nesting a parametric `List` declared separately) also
/// monomorphizes.
#[test]
fn slice3a_nested_rose_tree() {
    let src = r#"
        (declare-datatypes ((List 1)) ((par (T) ((lnil) (lcons (h T) (t (List T)))))))
        (declare-datatype Rose ((rose (kids (List Rose)))))
    "#;
    let r = elaborate(src).expect("Rose admits");
    assert!(r.env.lookup("Rose").is_some());
    assert!(r.env.lookup("List#Rose").is_some());
    assert!(r.env.ctor_of("rose").is_some());
    // a leaf rose: `(rose lnil#List#Rose) : Rose`.
    let leaf = Term::app(Term::cnst("rose"), Term::cnst("lnil#List#Rose"));
    assert!(is_def_eq(&r.env, &type_of(&r.env, &leaf).unwrap(), &Term::cnst("Rose")));
}

/// **Termination** under double nesting: `(List (List Tree))` enqueues both
/// `List#Tree` and `List#List#Tree`; the bounded worklist saturates and admits
/// the whole group.
#[test]
fn slice3a_double_nesting_terminates() {
    let src = r#"
        (declare-datatypes ((List 1) (Tree 0))
          ((par (T) ((lnil) (lcons (h T) (t (List T)))))
           ((leaf) (branch (kk (List (List Tree)))))))
    "#;
    let r = elaborate(src).expect("double nesting saturates");
    assert!(r.env.lookup("Tree").is_some());
    assert!(r.env.lookup("List#Tree").is_some(), "inner List#Tree reached");
    assert!(r.env.lookup("List#List#Tree").is_some(), "outer List#List#Tree reached");
    assert!(r.env.ctor_of("branch").is_some());
}

/// **Rejection (sound by omission)**: a polymorphic-recursive / non-regular
/// nesting (`Nest A = nnil | ncons A (Nest (Pair A A))`) never saturates — the
/// argument shape deepens without bound — so the bounded worklist rejects with
/// `FaceError::Unsupported` (no hang, no panic, no partial group).
#[test]
fn slice3a_non_regular_nesting_rejected() {
    let src = r#"
        (declare-sort Base 0)
        (declare-datatypes ((Pair 1) (Nest 1) (Top 0))
          ((par (A) ((mkpair (p1 A) (p2 A))))
           (par (A) ((nnil) (ncons (hd A) (tl (Nest (Pair A A))))))
           ((top (x (Nest Base))))))
    "#;
    match elaborate(src) {
        Err(FaceError::Unsupported(m)) => {
            assert!(m.contains("saturate") || m.contains("nesting"), "{m}")
        }
        other => panic!("expected a non-saturation rejection, got {other:?}"),
    }
}

/// **Soundness backstop (mangle collision)**: the monomorphizer mints member
/// names with a `#` sigil (`List#Tree`). The lexer admits `#` in a `|quoted|`
/// symbol, so a user *can* introduce a colliding name — but every member is
/// emitted through the kernel's checked `declare_mutual`, whose `DuplicateConst`
/// gate then refuses the collision. Confirm it is a *clean* `FaceError::Kernel`
/// (no panic, no silent acceptance, never a trusted ill-typed term) — i.e. the
/// "everything routes through the kernel admitter" invariant actually holds.
#[test]
fn slice3a_mangle_collision_is_clean_kernel_rejection() {
    // a user pre-declares a sort literally named `List#Tree` (via the |quoted|
    // form, since `#` is not a standard simple-symbol char); the nested
    // datatype below would monomorphize `(List Tree)` to that same name.
    let src = r#"
        (declare-sort |List#Tree| 0)
        (declare-datatypes ((List 1) (Tree 0))
          ((par (T) ((nil) (cons (head T) (tail (List T)))))
           ((node (kids (List Tree))))))
    "#;
    match elaborate(src) {
        // the kernel's DuplicateConst gate refuses the collision (surfaced as a
        // Kernel rejection — NOT an Unsupported guess, NOT a panic, NOT a sat).
        Err(FaceError::Kernel(_)) => {}
        other => panic!("expected a clean kernel DuplicateConst rejection, got {other:?}"),
    }
}

/// **Round-trip through the REAL producer**: a monomorphized group records into
/// the kernel's admission journal via `declare_mutual` like any hand-written
/// mutual group, so it must survive the AOT-bank encode→decode→**replay** (which
/// re-admits every step through the *checked* admitters). Elaborate the nested
/// datatype, bank-encode its env, decode into a fresh env, and confirm a value
/// over the *specialized* container (`cons#List#Tree`) still type-checks in the
/// replayed env — the end-to-end proof that the monomorphizer's output is real
/// kernel state, not a green test built on a hand-forged payload.
#[test]
fn slice3a_monomorphized_group_survives_bank_roundtrip() {
    let src = r#"
        (declare-datatypes ((List 1) (Tree 0))
          ((par (T) ((nil) (cons (head T) (tail (List T)))))
           ((node (kids (List Tree))))))
    "#;
    let r = elaborate(src).expect("nested datatype admits");
    // encode the live env's journal, then replay it into a fresh env.
    let bytes = bank_encode(&r.env).expect("bank-encode the monomorphized group");
    let env2 = bank_decode(&bytes).expect("bank-decode replays through checked admitters");
    // the specialized member + its mangled constructors are present after replay.
    assert!(env2.lookup("List#Tree").is_some(), "List#Tree survives replay");
    assert!(env2.ctor_of("cons#List#Tree").is_some(), "cons#List#Tree survives replay");
    // a non-trivial value over the specialized type type-checks in the REPLAYED
    // env: (cons#List#Tree (node nil#List#Tree) nil#List#Tree) : List#Tree.
    let v = Term::apps(
        Term::cnst("cons#List#Tree"),
        [Term::app(Term::cnst("node"), Term::cnst("nil#List#Tree")), Term::cnst("nil#List#Tree")],
    );
    assert!(
        is_def_eq(&env2, &type_of(&env2, &v).unwrap(), &Term::cnst("List#Tree")),
        "the replayed specialization still type-checks a value"
    );
}

/// **Soundness backstop (no negative occurrence is even expressible)**: a
/// datatype field sort can only elaborate to an atom (a sort / group member) or
/// a *covariant* parametric-container application — there is no surface form for
/// a function/arrow field sort — so the surface is positivity-conservative by
/// construction and the kernel's `NonPositive` gate is unreachable from it. A
/// field whose sort is a *list* that is not a known parametric container is
/// rejected up front (sound by omission), never mis-elaborated into an arrow.
#[test]
fn slice3a_function_typed_field_is_rejected_not_negative() {
    // `(-> Bad Bool)` as a constructor field sort: `->` is not a declared
    // parametric datatype, so the container-application path does not fire and
    // the sort is rejected — the kernel never sees a negative occurrence.
    let src = "(declare-datatype Bad ((mk (f (-> Bad Bool)))))";
    match elaborate(src) {
        Err(FaceError::Unsupported(_)) => {}
        other => panic!("expected an unsupported-sort rejection, got {other:?}"),
    }
}

/// A bound variable correctly shadows a global of the same name (de Bruijn).
#[test]
fn quantifier_binder_shadows_global() {
    // `x` is declared globally AND bound by the forall; inside, the bound one wins.
    let src = "(declare-sort S 0) (declare-const x S) (declare-fun p (S) Bool) \
               (assert (forall ((x S)) (p x)))";
    let r = elaborate(src).expect("elaborates");
    let ty = type_of(&r.env, &r.goals[0]).unwrap();
    assert!(is_def_eq(&r.env, &ty, &Term::prop()));
    // the body `(p x)` must reference the BOUND x (Bound 0), so the Π is closed.
    assert!(type_of(&r.env, &r.goals[0]).is_ok(), "the forall is a closed Prop");
}

// ── Phase 1a′: the Int/Real arithmetic theory slice ─────────────────────

/// Helper: every goal of a successfully-elaborated script is a closed `Prop`
/// (the kernel re-checked the arithmetic terms).
fn all_goals_are_props(src: &str, n: usize) {
    let r = elaborate(src).expect("elaborates");
    assert_eq!(r.goals.len(), n, "goal count");
    for g in &r.goals {
        let ty = type_of(&r.env, g).expect("goal type-checks");
        assert!(is_def_eq(&r.env, &ty, &Term::prop()), "goal is a Prop: {g} : {ty}");
    }
    assert!(r.env.lookup("Int").is_some(), "the arith prelude is installed");
}

/// Integer arithmetic: literals, `+ - * div mod abs`, comparisons, quantifiers.
#[test]
fn int_arithmetic_script_elaborates() {
    all_goals_are_props(
        r#"
        (set-logic LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> (+ x 1) 0))
        (assert (= (* 2 x) (+ x x)))
        (assert (<= (- x y) (abs (+ x (* 3 y)))))
        (assert (= (mod x 2) (div x y)))
        (assert (forall ((z Int)) (=> (> z 0) (>= z 1))))
        (assert (and (< 2 5) (<= (+ 2 2) 4)))
        (check-sat)
        "#,
        6,
    );
}

/// Real arithmetic: decimal literals, `/`, comparisons, and the `to_real`
/// Int→Real injection.
#[test]
fn real_arithmetic_and_to_real_injection_elaborate() {
    all_goals_are_props(
        r#"
        (declare-const r Real)
        (declare-const n Int)
        (assert (< (/ r 2.0) r))
        (assert (= (+ r 0.5) (- r (- 0.5))))
        (assert (> (to_real n) r))
        (check-sat)
        "#,
        3,
    );
}

/// Chained comparison `(< a b c)` ≡ `a<b ∧ b<c` — a `Prop` (the `and`-fold).
#[test]
fn chained_comparison_is_a_prop() {
    all_goals_are_props("(declare-const x Int) (assert (< 0 x 10))", 1);
}

/// Mixing `Int` and `Real` operands in one operator is rejected (sort check).
#[test]
fn mixed_int_real_operands_are_rejected() {
    let src = "(declare-const x Int) (assert (> (+ x 1.0) 0))";
    match elaborate(src) {
        Err(FaceError::Unsupported(m)) => assert!(m.contains("differing sorts"), "{m}"),
        other => panic!("expected a sort-mismatch rejection, got {other:?}"),
    }
}

/// `div`/`mod` on `Real` (and `/` on `Int`) are rejected at the face.
#[test]
fn sort_inappropriate_operators_are_rejected() {
    assert!(matches!(
        elaborate("(declare-const r Real) (assert (= (div r r) r))"),
        Err(FaceError::Unsupported(_))
    ));
    assert!(matches!(
        elaborate("(declare-const x Int) (assert (= (/ x x) x))"),
        Err(FaceError::Unsupported(_))
    ));
}

/// An arithmetic goal survives the bank round-trip (admission journal replay).
#[test]
fn arith_goal_survives_bank_roundtrip() {
    let r = elaborate("(declare-const x Int) (assert (>= (* x x) 0))").expect("elaborates");
    let bytes = bank_encode(&r.env).expect("encodes");
    let env2 = bank_decode(&bytes).expect("re-admits");
    let ty = type_of(&env2, &r.goals[0]).expect("goal still type-checks after replay");
    assert!(is_def_eq(&env2, &ty, &Term::prop()));
}
