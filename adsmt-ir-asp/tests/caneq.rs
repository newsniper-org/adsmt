//! **CanEq typed equality** — the comparison operator `=`/`!=` in a rule body
//! is routed by the *inferred operand sort*: arithmetic on `Int`, structural
//! (dis)equality on any enum / datatype, and a **cross-sort comparison is an
//! elaboration error**, not a silent atom (the recurring `Int = Node` bug class
//! killed at the face). End-to-end (`parse → elaborate → solve`).

use adsmt_ir_asp::{FaceError, elaborate, parse, solve};

/// Solve a source program and collect a query's single-column answer, sorted.
fn col0(src: &str) -> Vec<String> {
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    let mut out: Vec<String> = sol.answers[0].tuples.iter().map(|t| t[0].clone()).collect();
    out.sort();
    out
}

/// Solve and collect a query's two-column answer, sorted.
fn col01(src: &str) -> Vec<(String, String)> {
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    let mut out: Vec<(String, String)> =
        sol.answers[0].tuples.iter().map(|t| (t[0].clone(), t[1].clone())).collect();
    out.sort();
    out
}

// ---------------------------------------------------------------------------
// Int equality (the existing behaviour, now via the unified operand grammar).
// ---------------------------------------------------------------------------

/// `{ X = Y }` with `Int` operands is still arithmetic equality.
#[test]
fn int_equality_is_arithmetic() {
    let src = r#"
        pred v(Int).
        pred same(Int, Int).
        v(1). v(2).
        same(X, Y) :- v(X), v(Y), { X = Y }.
        ?- same(X, Y).
    "#;
    assert_eq!(col01(src), vec![("1".into(), "1".into()), ("2".into(), "2".into())]);
}

/// Arithmetic still mixes into an `Int` equality: `{ X = Y + 1 }`.
#[test]
fn int_equality_with_arithmetic() {
    let src = r#"
        pred v(Int).
        pred succ(Int, Int).
        v(1). v(2). v(3).
        succ(X, Y) :- v(X), v(Y), { X = Y + 1 }.
        ?- succ(X, Y).
    "#;
    assert_eq!(col01(src), vec![("2".into(), "1".into()), ("3".into(), "2".into())]);
}

// ---------------------------------------------------------------------------
// enum (dis)equality — structural, routed by CanEq.
// ---------------------------------------------------------------------------

/// `{ X = Y }` at an enum sort is **structural equality** → the diagonal only.
#[test]
fn enum_equality_is_structural() {
    let src = r#"
        enum Color = {red, green, blue}.
        pred c(Color).
        pred eqp(Color, Color).
        c(red). c(green). c(blue).
        eqp(X, Y) :- c(X), c(Y), { X = Y }.
        ?- eqp(X, Y).
    "#;
    assert_eq!(
        col01(src),
        vec![("blue".into(), "blue".into()), ("green".into(), "green".into()), ("red".into(), "red".into())]
    );
}

/// `{ X != Y }` at an enum sort is structural **dis**equality → the off-diagonal.
#[test]
fn enum_disequality_is_structural() {
    let src = r#"
        enum Color = {red, blue}.
        pred c(Color).
        pred diff(Color, Color).
        c(red). c(blue).
        diff(X, Y) :- c(X), c(Y), { X != Y }.
        ?- diff(X, Y).
    "#;
    assert_eq!(col01(src), vec![("blue".into(), "red".into()), ("red".into(), "blue".into())]);
}

/// A nullary-ctor operand: `{ X = green }` filters to the matching value (and the
/// constant is seeded into the enum domain even if it appears nowhere else).
#[test]
fn enum_equality_against_constant() {
    let src = r#"
        enum Color = {red, green, blue}.
        pred c(Color).
        pred isgreen(Color).
        c(red). c(green). c(blue).
        isgreen(X) :- c(X), { X = green }.
        ?- isgreen(X).
    "#;
    assert_eq!(col0(src), vec!["green"]);
}

// ---------------------------------------------------------------------------
// datatype (ctor-term) equality.
// ---------------------------------------------------------------------------

/// Structural equality over a *destructured* datatype: `selfpair` keeps the pairs
/// whose two fields are equal.
#[test]
fn datatype_field_equality() {
    let src = r#"
        enum N = {a, b}.
        data P = mk(N, N).
        pred p(P).
        pred selfpair(N).
        p(mk(a, a)).
        p(mk(a, b)).
        selfpair(X) :- p(mk(X, Y)), { X = Y }.
        ?- selfpair(X).
    "#;
    assert_eq!(col0(src), vec!["a"]);
}

/// Structural equality against a **ground constructor term**: `{ Z = mk(a, b) }`.
#[test]
fn datatype_equality_against_ground_term() {
    let src = r#"
        enum N = {a, b}.
        data P = mk(N, N).
        pred p(P).
        pred hit(P).
        p(mk(a, b)).
        p(mk(b, a)).
        hit(Z) :- p(Z), { Z = mk(a, b) }.
        ?- hit(Z).
    "#;
    assert_eq!(col0(src), vec!["mk(a,b)"]);
}

// ---------------------------------------------------------------------------
// CanEq rejections — the cross-sort bug class, refused at elaboration.
// ---------------------------------------------------------------------------

/// A cross-sort comparison (`Int` vs an enum constant) is an elaboration error.
#[test]
fn cross_sort_equality_rejected() {
    let src = r#"
        enum Color = {red, green}.
        pred d(Int).
        pred bad(Int).
        bad(X) :- d(X), { X = red }.
    "#;
    let prog = parse(src).expect("parses (the parser is sort-blind)");
    assert!(matches!(elaborate(&prog), Err(FaceError::Unsupported(_))), "CanEq must reject Int = Color");
}

/// Two different enum sorts do not unify either.
#[test]
fn cross_enum_equality_rejected() {
    let src = r#"
        enum A = {a1, a2}.
        enum B = {b1, b2}.
        pred pa(A).
        pred pb(B).
        pred bad(A, B).
        bad(X, Y) :- pa(X), pb(Y), { X = Y }.
    "#;
    assert!(matches!(elaborate(&parse(src).unwrap()), Err(FaceError::Unsupported(_))));
}

/// An ordering operator is undefined on a non-`Int` sort (an enum carries
/// equality, not `<`) → an elaboration error.
#[test]
fn ordering_on_enum_rejected() {
    let src = r#"
        enum Color = {red, green}.
        pred c(Color).
        pred bad(Color, Color).
        bad(X, Y) :- c(X), c(Y), { X < Y }.
    "#;
    assert!(matches!(elaborate(&parse(src).unwrap()), Err(FaceError::Unsupported(_))));
}

/// Arithmetic inside a constructor-term operand (`mk(1 + 1, a)`) is refused —
/// it would force the structural path to compare an un-reduced expression. A
/// clean elaboration error, never a panic.
#[test]
fn arithmetic_in_ctor_operand_rejected() {
    let src = r#"
        enum N = {a, b}.
        data P = mk(Int, N).
        pred p(P).
        pred bad(P).
        p(mk(2, a)).
        bad(Z) :- p(Z), { Z = mk(1 + 1, a) }.
    "#;
    assert!(matches!(elaborate(&parse(src).unwrap()), Err(FaceError::Unsupported(_))));
}

/// A comparison variable not bound by a positive body atom is still unsafe
/// (range restriction holds for the new operand grammar too).
#[test]
fn unbound_comparison_variable_rejected() {
    let src = r#"
        enum Color = {red, green}.
        pred c(Color).
        pred bad(Color).
        bad(X) :- c(X), { X = Y }.
    "#;
    assert!(matches!(elaborate(&parse(src).unwrap()), Err(FaceError::Unsafe(_))));
}
