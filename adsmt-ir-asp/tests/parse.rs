//! The **round-trip oracle** for the typed-ASP parser. The existing hand-built
//! programs in `tests/solve.rs` / `tests/datatypes.rs` are re-expressed here as
//! *source strings*; we `parse` → `elaborate` → `solve` and assert the SAME
//! results those hand-built tests assert. Plus a handful of pure-parse AST
//! equality tests and rejection tests (malformed input → `FaceError::Parse`,
//! never a panic).
//!
//! Source uses the variable/constant convention: lowercase-leading identifiers
//! are constants / constructors (e.g. `enum Color = {red, green, blue}.`,
//! `data Tree = leaf | node(Tree, Int, Tree).`); uppercase/`_`-leading
//! identifiers in term position are variables.

use adsmt_ir_asp::ast::{
    Atom, CmpOp, Ctor, DataDef, EnumDef, Expr, Item, Literal, PredDecl, Program, Rule, Term,
    Theory,
};
use adsmt_ir_asp::{FaceError, elaborate, parse, solve};

// ----------------------------------------------------------------------------
// round-trip oracle: parse → elaborate → solve, same answers as the hand-built
// tests.
// ----------------------------------------------------------------------------

/// Transitive closure — the canonical recursive Datalog program. `?- reach(a, X)`
/// over `a→b→c→d` returns exactly `{b, c, d}` (mirrors
/// `solve::transitive_closure_find_all`).
#[test]
fn roundtrip_transitive_closure() {
    let src = r#"
        sort Node.
        pred edge(Node, Node).
        pred reach(Node, Node).
        reach(X, Y) :- edge(X, Y).
        reach(X, Z) :- reach(X, Y), edge(Y, Z).
        edge(a, b).
        edge(b, c).
        edge(c, d).
        ?- reach(a, X).
    "#;
    let prog = parse(src).expect("parses");
    let elab = elaborate(&prog).expect("elaborates");
    let sol = solve(&elab).expect("solves");
    let ans = &sol.answers[0];
    assert_eq!(ans.vars, vec!["X".to_string()]);
    let mut reached: Vec<String> = ans.tuples.iter().map(|t| t[0].clone()).collect();
    reached.sort();
    assert_eq!(reached, vec!["b", "c", "d"]);
}

/// The L1 theory interior: `big(T) :- dur(T, D), { D >= 4 }.` keeps only the
/// long tasks → `{t2, t3}` (mirrors `solve::theory_interior_filters_by_arithmetic`).
#[test]
fn roundtrip_theory_interior() {
    let src = r#"
        sort Task.
        pred dur(Task, Int).
        pred big(Task).
        big(T) :- dur(T, D), { D >= 4 }.
        dur(t1, 3).
        dur(t2, 5).
        dur(t3, 4).
        ?- big(T).
    "#;
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    let mut big: Vec<String> = sol.answers[0].tuples.iter().map(|t| t[0].clone()).collect();
    big.sort();
    assert_eq!(big, vec!["t2", "t3"], "only durations >= 4");
}

/// The abductive build-system: abducing `rebuild(main)` yields the single
/// minimal hypothesis `{ needs_rebuild(main) }` (mirrors
/// `solve::abductive_build_system`).
#[test]
fn roundtrip_abductive_build_system() {
    let src = r#"
        sort File.
        pred stale(File).
        pred rebuild(File).
        abducible needs_rebuild(File).
        rebuild(T) :- stale(T), needs_rebuild(T).
        stale(main).
        ?- abduce rebuild(main).
    "#;
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    let ab = &sol.abductions[0];
    assert!(!ab.entailed(), "rebuild(main) is not deductively entailed");
    assert_eq!(ab.explanations.len(), 1, "exactly one minimal explanation");
    let exp = &ab.explanations[0];
    assert_eq!(exp.len(), 1);
    assert_eq!(exp[0].pred, "needs_rebuild");
    assert_eq!(exp[0].args, vec![Term::Const("main".into())]);
}

/// First-order matching — destructuring in a body: `connects(X, Y) :-
/// edge(pair(X, Y)).` binds the subterm variables (mirrors
/// `datatypes::destructuring_match_in_body`).
#[test]
fn roundtrip_destructuring_match() {
    let src = r#"
        enum Node = {a, b, cc}.
        data Pair = pair(Node, Node).
        pred edge(Pair).
        pred connects(Node, Node).
        connects(X, Y) :- edge(pair(X, Y)).
        edge(pair(a, b)).
        edge(pair(b, cc)).
        ?- connects(X, Y).
    "#;
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    let mut pairs: Vec<(String, String)> =
        sol.answers[0].tuples.iter().map(|t| (t[0].clone(), t[1].clone())).collect();
    pairs.sort();
    assert_eq!(pairs, vec![("a".into(), "b".into()), ("b".into(), "cc".into())]);
}

/// First-order matching — structural recursion (list membership). `member(b, …)`
/// holds, `member(cc, …)` does not (mirrors
/// `datatypes::structural_recursion_list_membership`).
#[test]
fn roundtrip_structural_recursion_membership() {
    let base = r#"
        enum Node = {a, b, cc}.
        data List = nil | cons(Node, List).
        pred member(Node, List).
        member(X, cons(X, T)).
        member(X, cons(Y, T)) :- member(X, T).
    "#;
    let yes = format!("{base}\n?- member(b, cons(a, cons(b, nil))).");
    assert!(
        solve(&elaborate(&parse(&yes).unwrap()).unwrap()).unwrap().answers[0].holds(),
        "b ∈ [a, b]"
    );
    let no = format!("{base}\n?- member(cc, cons(a, cons(b, nil))).");
    assert!(
        !solve(&elaborate(&parse(&no).unwrap()).unwrap()).unwrap().answers[0].holds(),
        "cc ∉ [a, b]"
    );
}

/// An integrity constraint: `:- edge(A,B), color(A,C), color(B,C).` is violated
/// when adjacent nodes share a color, satisfied otherwise (mirrors
/// `solve::integrity_constraint_consistency`).
#[test]
fn roundtrip_integrity_constraint() {
    let base = |ca: &str, cb: &str| {
        format!(
            r#"
            sort Node.
            enum Color = {{red, blue}}.
            pred edge(Node, Node).
            pred color(Node, Color).
            edge(x, y).
            color(x, {ca}).
            color(y, {cb}).
            :- edge(A, B), color(A, C), color(B, C).
        "#
        )
    };
    // adjacent, both red → constraint violated → inconsistent.
    assert!(!solve(&elaborate(&parse(&base("red", "red")).unwrap()).unwrap()).unwrap().consistent);
    // different colors → satisfied → consistent.
    assert!(solve(&elaborate(&parse(&base("red", "blue")).unwrap()).unwrap()).unwrap().consistent);
}

// Extra round-trips to exercise more of the grammar end-to-end.

/// A ground query on the datatype slice: `?- tree(X).` enumerates the
/// subterm-closed universe (mirrors `datatypes::datatype_ground_terms`).
#[test]
fn roundtrip_datatype_ground_terms() {
    let src = r#"
        data Tree = leaf | node(Tree, Tree).
        pred tree(Tree).
        tree(node(leaf, leaf)).
        tree(leaf).
        ?- tree(X).
    "#;
    let elab = elaborate(&parse(src).unwrap()).expect("datatype elaborates");
    assert!(elab.env.ctor_of("node").is_some(), "node is a kernel constructor");
    let sol = solve(&elab).unwrap();
    let mut trees: Vec<String> = sol.answers[0].tuples.iter().map(|t| t[0].clone()).collect();
    trees.sort();
    assert_eq!(trees, vec!["leaf", "node(leaf,leaf)"]);
}

/// A constraint carrying a theory atom: `:- dur(T, D), { D > 100 }.` (mirrors
/// `solve::integrity_constraint_with_theory`).
#[test]
fn roundtrip_constraint_with_theory() {
    let prog = |d: i64| {
        format!(
            r#"
            sort Task.
            pred dur(Task, Int).
            dur(t1, {d}).
            :- dur(T, D), {{ D > 100 }}.
        "#
        )
    };
    assert!(
        !solve(&elaborate(&parse(&prog(150)).unwrap()).unwrap()).unwrap().consistent,
        "150 > 100 violates"
    );
    assert!(
        solve(&elaborate(&parse(&prog(50)).unwrap()).unwrap()).unwrap().consistent,
        "50 is fine"
    );
}

// ----------------------------------------------------------------------------
// pure-parse AST equality
// ----------------------------------------------------------------------------

/// A representative program parses to exactly the hand-built `Program`, covering
/// every item kind, the variable/constant convention, a string literal, a
/// negative integer, a nested constructor application, and an arithmetic theory
/// atom with precedence.
#[test]
fn parse_ast_equality_full_program() {
    let src = r#"
        % the whole surface in one program
        sort Node.
        enum Color = {red, green, blue}.
        data Tree = leaf | node(Tree, Int, Tree).
        pred edge(Node, Node).
        abducible guess(Node).
        edge(a, b).
        path(X, Z) :- edge(X, Y), edge(Y, Z), { X < Z + 1 }.
        :- edge(A, A).
        ?- edge(a, X).
        ?- abduce guess(b).
        v(-7).
        label("hi\"there").
    "#;
    let got = parse(src).expect("parses");

    let want = Program {
        items: vec![
            Item::Sort("Node".into()),
            Item::Enum(EnumDef {
                name: "Color".into(),
                ctors: vec!["red".into(), "green".into(), "blue".into()],
            }),
            Item::Data(DataDef {
                name: "Tree".into(),
                ctors: vec![
                    Ctor { name: "leaf".into(), arg_sorts: vec![] },
                    Ctor {
                        name: "node".into(),
                        arg_sorts: vec!["Tree".into(), "Int".into(), "Tree".into()],
                    },
                ],
            }),
            Item::Pred(PredDecl {
                name: "edge".into(),
                arg_sorts: vec!["Node".into(), "Node".into()],
            }),
            Item::Abducible(PredDecl { name: "guess".into(), arg_sorts: vec!["Node".into()] }),
            Item::Fact(Atom {
                pred: "edge".into(),
                args: vec![Term::Const("a".into()), Term::Const("b".into())],
            }),
            Item::Rule(Rule {
                head: Atom {
                    pred: "path".into(),
                    args: vec![Term::Var("X".into()), Term::Var("Z".into())],
                },
                body: vec![
                    Literal::Pos(Atom {
                        pred: "edge".into(),
                        args: vec![Term::Var("X".into()), Term::Var("Y".into())],
                    }),
                    Literal::Pos(Atom {
                        pred: "edge".into(),
                        args: vec![Term::Var("Y".into()), Term::Var("Z".into())],
                    }),
                    Literal::Theory(Theory {
                        op: CmpOp::Lt,
                        lhs: Expr::Var("X".into()),
                        rhs: Expr::Add(
                            Box::new(Expr::Var("Z".into())),
                            Box::new(Expr::Lit(1)),
                        ),
                    }),
                ],
            }),
            Item::Constraint(vec![Literal::Pos(Atom {
                pred: "edge".into(),
                args: vec![Term::Var("A".into()), Term::Var("A".into())],
            })]),
            Item::Query(Atom {
                pred: "edge".into(),
                args: vec![Term::Const("a".into()), Term::Var("X".into())],
            }),
            Item::Abduce(Atom { pred: "guess".into(), args: vec![Term::Const("b".into())] }),
            Item::Fact(Atom { pred: "v".into(), args: vec![Term::Int(-7)] }),
            Item::Fact(Atom {
                pred: "label".into(),
                args: vec![Term::Const("hi\"there".into())],
            }),
        ],
    };
    assert_eq!(got, want);
}

/// A `_`-leading identifier in term position is a variable (per the
/// convention), so a head-only `p(_X).` is a variable-bearing (non-ground)
/// statement → an empty-body `Rule`, not a `Fact`. A nullary `pred` declaration
/// parses with empty arg sorts. A head-only statement with a *ground* head IS a
/// `Fact`.
#[test]
fn parse_ast_equality_underscore_var_and_nullary_pred() {
    let got = parse("pred ok. p(_X). q(c).").expect("parses");
    assert_eq!(
        got,
        Program {
            items: vec![
                Item::Pred(PredDecl { name: "ok".into(), arg_sorts: vec![] }),
                // `_X` is a variable → variable-bearing head → empty-body rule.
                Item::Rule(Rule {
                    head: Atom { pred: "p".into(), args: vec![Term::Var("_X".into())] },
                    body: vec![],
                }),
                // ground head → fact.
                Item::Fact(Atom { pred: "q".into(), args: vec![Term::Const("c".into())] }),
            ],
        }
    );
}

/// `=` doubles as the theory equality operator (`CmpOp::Eq`, not `==`), and `!=`
/// is `CmpOp::Ne`.
#[test]
fn parse_ast_equality_theory_eq_and_ne() {
    let got = parse("p(X) :- q(X), { X = 0 }, { X != 1 }.").expect("parses");
    let Item::Rule(r) = &got.items[0] else { panic!() };
    let Literal::Theory(t0) = &r.body[1] else { panic!() };
    let Literal::Theory(t1) = &r.body[2] else { panic!() };
    assert_eq!(t0.op, CmpOp::Eq);
    assert_eq!(t1.op, CmpOp::Ne);
}

// ----------------------------------------------------------------------------
// rejection tests — malformed input is a clean Parse error, never a panic.
// ----------------------------------------------------------------------------

#[test]
fn rejects_unterminated_atom() {
    assert!(matches!(parse("edge(a, b"), Err(FaceError::Parse(_))));
}

#[test]
fn rejects_missing_dot() {
    assert!(matches!(parse("sort Node"), Err(FaceError::Parse(_))));
    assert!(matches!(parse("edge(a, b)"), Err(FaceError::Parse(_))));
}

#[test]
fn rejects_unbalanced_parens_and_braces() {
    assert!(matches!(parse("edge(a, b)) ."), Err(FaceError::Parse(_))));
    assert!(matches!(parse("enum C = {a, b."), Err(FaceError::Parse(_))));
    assert!(matches!(parse("p(X) :- q(X), { X < 1 ."), Err(FaceError::Parse(_))));
}

#[test]
fn rejects_garbage_token() {
    assert!(matches!(parse("@garbage."), Err(FaceError::Parse(_))));
    assert!(matches!(parse("edge(a) # b."), Err(FaceError::Parse(_))));
}

#[test]
fn rejects_unterminated_string() {
    assert!(matches!(parse(r#"label("oops)."#), Err(FaceError::Parse(_))));
}

#[test]
fn rejects_empty_body_and_bad_theory() {
    assert!(matches!(parse("p(X) :- ."), Err(FaceError::Parse(_))));
    assert!(matches!(parse("p(X) :- { X }."), Err(FaceError::Parse(_))));
    assert!(matches!(parse("?- ."), Err(FaceError::Parse(_))));
}

#[test]
fn empty_input_is_empty_program() {
    assert_eq!(parse("").unwrap(), Program { items: vec![] });
    assert_eq!(parse("  % only a comment\n").unwrap(), Program { items: vec![] });
}

#[test]
fn deeply_nested_does_not_overflow() {
    let depth = 5_000;
    let src = format!("p({}leaf{}).", "f(".repeat(depth), ")".repeat(depth));
    assert!(matches!(parse(&src), Err(FaceError::Parse(_))));
}

/// A long *flat* arithmetic chain (`1+1+…+1`) left-nests one `Expr` node per
/// operator; the operator loops must count toward the depth bound, else the
/// unbounded tree overflows the stack on Drop/walk. A clean error, never a crash.
#[test]
fn flat_arithmetic_chain_does_not_overflow() {
    let plus = std::iter::repeat_n("1", 5_000).collect::<Vec<_>>().join("+");
    assert!(matches!(parse(&format!("p(X) :- q(X), {{ Z = {plus} }}.")), Err(FaceError::Parse(_))));
    let times = std::iter::repeat_n("2", 5_000).collect::<Vec<_>>().join("*");
    assert!(matches!(parse(&format!("p(X) :- q(X), {{ Z = {times} }}.")), Err(FaceError::Parse(_))));
}

/// Anonymous `_` is a distinct fresh variable each occurrence: `src(X) :-
/// e(X, _).` is the projection "X has an outgoing edge". Were the two roles of
/// `_` aliased to one variable (the pre-desugaring bug), `e(X, _)` would mean
/// `e(X, X)` (a self-loop) and `src` would be empty — so this end-to-end answer
/// is exactly what distinguishes the correct desugaring.
#[test]
fn anonymous_underscore_is_a_dont_care_projection() {
    let src = r#"
        sort Node.
        pred e(Node, Node).
        pred src(Node).
        e(a, b).
        e(a, c).
        src(X) :- e(X, _).
        ?- src(X).
    "#;
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    let srcs: Vec<String> = sol.answers[0].tuples.iter().map(|t| t[0].clone()).collect();
    assert_eq!(srcs, vec!["a"], "a has outgoing edges (the `_` target is a don't-care)");
}

/// Pooling `;` and integer intervals `..` expand a fact into many — end-to-end,
/// `value(1..3).` + `value(5; 7).` populates the relation, and a rule over it
/// keeps the even values.
#[test]
fn pooling_and_interval_drive_solving() {
    let src = r#"
        pred value(Int).
        pred big(Int).
        value(1..3).
        value(5; 7).
        big(X) :- value(X), { X >= 3 }.
        ?- big(X).
    "#;
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    let mut big: Vec<i64> =
        sol.answers[0].tuples.iter().map(|t| t[0].parse().unwrap()).collect();
    big.sort();
    assert_eq!(big, vec![3, 5, 7], "values {{1,2,3,5,7}} filtered to >= 3");
}

/// Whole-rule pooling expands the head — end-to-end, `lit(red; blue) :- on.`
/// becomes two rules sharing the body, deriving exactly red and blue.
#[test]
fn whole_rule_pooling_drives_solving() {
    let src = r#"
        enum Color = {red, green, blue}.
        pred on.
        pred lit(Color).
        on.
        lit(red; blue) :- on.
        ?- lit(C).
    "#;
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    let mut lit: Vec<String> = sol.answers[0].tuples.iter().map(|t| t[0].clone()).collect();
    lit.sort();
    assert_eq!(lit, vec!["blue", "red"], "the head pool lights red and blue, not green");
}

/// Body `let` names a constructor subterm and reuses it — end-to-end, `loop(X)
/// :- let E = mk(X, X), edge(E).` keeps the nodes with a self-edge.
#[test]
fn body_let_drives_solving() {
    let src = r#"
        enum N = {a, b}.
        data P = mk(N, N).
        pred edge(P).
        pred loop(N).
        edge(mk(a, a)).
        edge(mk(b, a)).
        loop(X) :- let E = mk(X, X), edge(E).
        ?- loop(X).
    "#;
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    let loops: Vec<String> = sol.answers[0].tuples.iter().map(|t| t[0].clone()).collect();
    assert_eq!(loops, vec!["a"], "only a has a self-edge mk(a,a)");
}

/// A **non-ground** abductive goal `?- abduce rebuild(X)` enumerates the goal
/// variable and abduces per binding — one answer per File that has an
/// explanation, each with its own `needs_rebuild(F)` hypothesis.
#[test]
fn non_ground_abduce_enumerates_bindings() {
    let src = r#"
        sort File.
        pred stale(File).
        pred rebuild(File).
        abducible needs_rebuild(File).
        rebuild(T) :- stale(T), needs_rebuild(T).
        stale(main).
        stale(util).
        ?- abduce rebuild(X).
    "#;
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    assert_eq!(sol.abductions.len(), 2, "one binding per stale file");
    let mut files: Vec<String> = sol
        .abductions
        .iter()
        .map(|ab| {
            let Term::Const(f) = &ab.goal.args[0] else { panic!("a ground File value") };
            // the single minimal explanation is `needs_rebuild(F)` for this F.
            assert_eq!(ab.explanations.len(), 1);
            let exp = &ab.explanations[0];
            assert_eq!(exp.len(), 1);
            assert_eq!(exp[0].pred, "needs_rebuild");
            assert_eq!(exp[0].args, vec![Term::Const(f.clone())]);
            f.clone()
        })
        .collect();
    files.sort();
    assert_eq!(files, vec!["main", "util"]);
}

/// An uppercase-leading constructor name is a variable in term position, so it
/// would be unreferenceable; the parser rejects it at the `data`/`enum`
/// declaration (a clean error) instead of silently building a wrong AST.
#[test]
fn rejects_uppercase_constructor_name() {
    assert!(matches!(parse("data L = Nil | Cons(L)."), Err(FaceError::Parse(_))));
    assert!(matches!(parse("enum Color = {Red, Green}."), Err(FaceError::Parse(_))));
    // field/argument *sort* names stay uppercase; only the ctor name is lowercase.
    assert!(parse("data L = nil | cons(Int, L).").is_ok());
}
