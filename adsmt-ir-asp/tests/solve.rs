//! End-to-end definite-Datalog: a typed-ASP program elaborates (through the
//! kernel firewall) and `solve` grounds it + runs the least-fixpoint + answers
//! queries. The headline is transitive closure — the canonical recursive
//! Datalog program.

use adsmt_ir_asp::ast::{
    Atom, CmpOp, Expr, Item, Literal, PredDecl, Program, Rule, Term as T, Theory,
};
use adsmt_ir_asp::{elaborate, solve};

fn v(s: &str) -> T {
    T::Var(s.into())
}
fn c(s: &str) -> T {
    T::Const(s.into())
}
fn atom(pred: &str, args: Vec<T>) -> Atom {
    Atom { pred: pred.into(), args }
}
fn pos(pred: &str, args: Vec<T>) -> Literal {
    Literal::Pos(atom(pred, args))
}

/// Build a reachability program over a fixed graph, with a given query.
fn reach_program(edges: &[(&str, &str)], query: Atom) -> Program {
    let mut items = vec![
        Item::Sort("Node".into()),
        Item::Pred(PredDecl { name: "edge".into(), arg_sorts: vec!["Node".into(), "Node".into()] }),
        Item::Pred(PredDecl { name: "reach".into(), arg_sorts: vec!["Node".into(), "Node".into()] }),
        // reach(X,Y) :- edge(X,Y).
        Item::Rule(Rule {
            head: atom("reach", vec![v("X"), v("Y")]),
            body: vec![pos("edge", vec![v("X"), v("Y")])],
        }),
        // reach(X,Z) :- reach(X,Y), edge(Y,Z).
        Item::Rule(Rule {
            head: atom("reach", vec![v("X"), v("Z")]),
            body: vec![pos("reach", vec![v("X"), v("Y")]), pos("edge", vec![v("Y"), v("Z")])],
        }),
    ];
    for &(a, b) in edges {
        items.push(Item::Fact(atom("edge", vec![c(a), c(b)])));
    }
    items.push(Item::Query(query));
    Program { items }
}

/// `?- reach(a, X)` over `a→b→c→d` returns exactly `{b, c, d}`.
#[test]
fn transitive_closure_find_all() {
    let prog = reach_program(&[("a", "b"), ("b", "c"), ("c", "d")], atom("reach", vec![c("a"), v("X")]));
    let elab = elaborate(&prog).expect("elaborates");
    let sol = solve(&elab).expect("solves");
    let ans = &sol.answers[0];
    assert_eq!(ans.vars, vec!["X".to_string()]);
    let mut reached: Vec<String> = ans.tuples.iter().map(|t| t[0].clone()).collect();
    reached.sort();
    assert_eq!(reached, vec!["b", "c", "d"]);
}

/// A ground query `?- reach(a, d)` holds; `?- reach(d, a)` does not (the graph
/// is acyclic and forward-only).
#[test]
fn ground_queries_yes_and_no() {
    let yes = reach_program(&[("a", "b"), ("b", "c"), ("c", "d")], atom("reach", vec![c("a"), c("d")]));
    let sol = solve(&elaborate(&yes).unwrap()).unwrap();
    assert!(sol.answers[0].holds(), "a reaches d");

    let no = reach_program(&[("a", "b"), ("b", "c"), ("c", "d")], atom("reach", vec![c("d"), c("a")]));
    let sol = solve(&elaborate(&no).unwrap()).unwrap();
    assert!(!sol.answers[0].holds(), "d does not reach a");
}

/// A cyclic graph (`a→b→a`) terminates and reaches everything in the cycle
/// (including self-reach via the cycle).
#[test]
fn cyclic_graph_terminates() {
    let prog = reach_program(&[("a", "b"), ("b", "a")], atom("reach", vec![c("a"), v("X")]));
    let sol = solve(&elaborate(&prog).unwrap()).unwrap();
    let mut reached: Vec<String> = sol.answers[0].tuples.iter().map(|t| t[0].clone()).collect();
    reached.sort();
    assert_eq!(reached, vec!["a", "b"], "a reaches b and (via the cycle) itself");
}

/// An enum domain participates: `primary(C) :- likes(C)` over an enum, queried
/// for all colors.
#[test]
fn enum_domain_grounds() {
    use adsmt_ir_asp::ast::EnumDef;
    let prog = Program {
        items: vec![
            Item::Enum(EnumDef { name: "Color".into(), ctors: vec!["Red".into(), "Green".into(), "Blue".into()] }),
            Item::Pred(PredDecl { name: "likes".into(), arg_sorts: vec!["Color".into()] }),
            Item::Pred(PredDecl { name: "primary".into(), arg_sorts: vec!["Color".into()] }),
            Item::Rule(Rule {
                head: atom("primary", vec![v("C")]),
                body: vec![pos("likes", vec![v("C")])],
            }),
            Item::Fact(atom("likes", vec![c("Red")])),
            Item::Fact(atom("likes", vec![c("Blue")])),
            Item::Query(atom("primary", vec![v("C")])),
        ],
    };
    let sol = solve(&elaborate(&prog).unwrap()).unwrap();
    let mut got: Vec<String> = sol.answers[0].tuples.iter().map(|t| t[0].clone()).collect();
    got.sort();
    assert_eq!(got, vec!["Blue", "Red"]);
}

/// A rule whose head variable is not bound by the body is unsafe.
#[test]
fn unsafe_rule_rejected() {
    use adsmt_ir_asp::FaceError;
    let prog = Program {
        items: vec![
            Item::Sort("Node".into()),
            Item::Pred(PredDecl { name: "p".into(), arg_sorts: vec!["Node".into()] }),
            Item::Pred(PredDecl { name: "q".into(), arg_sorts: vec!["Node".into()] }),
            // p(X) :- q(Y).   — X unbound by the body.
            Item::Rule(Rule {
                head: atom("p", vec![v("X")]),
                body: vec![pos("q", vec![v("Y")])],
            }),
        ],
    };
    assert!(matches!(elaborate(&prog), Err(FaceError::Unsafe(_))));
}

/// **L1 theory interior**: a rule with an integer comparison body atom. `dur`
/// facts bind the Int variable; `{ D >= 4 }` is evaluated arithmetically during
/// grounding (the gate's θ) → only the long tasks are `big`.
#[test]
fn theory_interior_filters_by_arithmetic() {
    let prog = Program {
        items: vec![
            Item::Sort("Task".into()),
            Item::Pred(PredDecl { name: "dur".into(), arg_sorts: vec!["Task".into(), "Int".into()] }),
            Item::Pred(PredDecl { name: "big".into(), arg_sorts: vec!["Task".into()] }),
            // big(T) :- dur(T, D), { D >= 4 }.
            Item::Rule(Rule {
                head: atom("big", vec![v("T")]),
                body: vec![
                    pos("dur", vec![v("T"), v("D")]),
                    Literal::Theory(Theory { op: CmpOp::Ge, lhs: Expr::Var("D".into()), rhs: Expr::Lit(4) }),
                ],
            }),
            Item::Fact(atom("dur", vec![c("t1"), T::Int(3)])),
            Item::Fact(atom("dur", vec![c("t2"), T::Int(5)])),
            Item::Fact(atom("dur", vec![c("t3"), T::Int(4)])),
            Item::Query(atom("big", vec![v("T")])),
        ],
    };
    let sol = solve(&elaborate(&prog).unwrap()).unwrap();
    let mut big: Vec<String> = sol.answers[0].tuples.iter().map(|t| t[0].clone()).collect();
    big.sort();
    assert_eq!(big, vec!["t2", "t3"], "only durations >= 4");
}

/// Theory arithmetic: `{ Sa < Sb + Db }` over bound integer variables. Two
/// intervals overlap iff each starts before the other ends.
#[test]
fn theory_arithmetic_expression() {
    // overlaps(A,B) :- iv(A,Sa,Da), iv(B,Sb,Db), { Sa < Sb + Db }, { Sb < Sa + Da }.
    let prog = Program {
        items: vec![
            Item::Sort("Iv".into()),
            Item::Pred(PredDecl {
                name: "iv".into(),
                arg_sorts: vec!["Iv".into(), "Int".into(), "Int".into()],
            }),
            Item::Pred(PredDecl { name: "overlaps".into(), arg_sorts: vec!["Iv".into(), "Iv".into()] }),
            Item::Rule(Rule {
                head: atom("overlaps", vec![v("A"), v("B")]),
                body: vec![
                    pos("iv", vec![v("A"), v("Sa"), v("Da")]),
                    pos("iv", vec![v("B"), v("Sb"), v("Db")]),
                    Literal::Theory(Theory {
                        op: CmpOp::Lt,
                        lhs: Expr::Var("Sa".into()),
                        rhs: Expr::Add(Box::new(Expr::Var("Sb".into())), Box::new(Expr::Var("Db".into()))),
                    }),
                    Literal::Theory(Theory {
                        op: CmpOp::Lt,
                        lhs: Expr::Var("Sb".into()),
                        rhs: Expr::Add(Box::new(Expr::Var("Sa".into())), Box::new(Expr::Var("Da".into()))),
                    }),
                ],
            }),
            // iv a: [0,3); iv b: [2,4); iv c: [10,12).
            Item::Fact(atom("iv", vec![c("a"), T::Int(0), T::Int(3)])),
            Item::Fact(atom("iv", vec![c("b"), T::Int(2), T::Int(2)])),
            Item::Fact(atom("iv", vec![c("z"), T::Int(10), T::Int(2)])),
            Item::Query(atom("overlaps", vec![c("a"), c("b")])),
            Item::Query(atom("overlaps", vec![c("a"), c("z")])),
        ],
    };
    let sol = solve(&elaborate(&prog).unwrap()).unwrap();
    assert!(sol.answers[0].holds(), "a [0,3) overlaps b [2,4)");
    assert!(!sol.answers[1].holds(), "a [0,3) does not overlap z [10,12)");
}

/// **The abductive merge** (DESIGN §4): an abducible is a completion-less atom;
/// abducing `rebuild(main)` over `rebuild(T) :- stale(T), needs_rebuild(T)`
/// (with `stale(main)` a fact) yields the ⊆-minimal hypothesis
/// `{ needs_rebuild(main) }`.
#[test]
fn abductive_build_system() {
    let prog = Program {
        items: vec![
            Item::Sort("File".into()),
            Item::Pred(PredDecl { name: "stale".into(), arg_sorts: vec!["File".into()] }),
            Item::Pred(PredDecl { name: "rebuild".into(), arg_sorts: vec!["File".into()] }),
            Item::Abducible(PredDecl { name: "needs_rebuild".into(), arg_sorts: vec!["File".into()] }),
            Item::Rule(Rule {
                head: atom("rebuild", vec![v("T")]),
                body: vec![pos("stale", vec![v("T")]), pos("needs_rebuild", vec![v("T")])],
            }),
            Item::Fact(atom("stale", vec![c("main")])),
            Item::Abduce(atom("rebuild", vec![c("main")])),
        ],
    };
    let sol = solve(&elaborate(&prog).unwrap()).unwrap();
    let ab = &sol.abductions[0];
    assert!(!ab.entailed(), "rebuild(main) is not deductively entailed");
    assert_eq!(ab.explanations.len(), 1, "exactly one minimal explanation");
    let exp = &ab.explanations[0];
    assert_eq!(exp.len(), 1);
    assert_eq!(exp[0].pred, "needs_rebuild");
    assert_eq!(exp[0].args, vec![c("main")]);
}

/// **Deduction = empty-abducible abduction**: abducing a goal that already holds
/// returns the empty explanation (and `entailed()` is true).
#[test]
fn abductive_deduction_is_the_empty_explanation() {
    let prog = Program {
        items: vec![
            Item::Sort("File".into()),
            Item::Pred(PredDecl { name: "done".into(), arg_sorts: vec!["File".into()] }),
            Item::Abducible(PredDecl { name: "assume".into(), arg_sorts: vec!["File".into()] }),
            Item::Fact(atom("done", vec![c("main")])),
            Item::Abduce(atom("done", vec![c("main")])),
        ],
    };
    let sol = solve(&elaborate(&prog).unwrap()).unwrap();
    assert!(sol.abductions[0].entailed(), "done(main) holds with no hypothesis");
}

/// No hypothesis (within budget) can make the goal hold → no explanation.
#[test]
fn abductive_no_explanation() {
    let prog = Program {
        items: vec![
            Item::Sort("File".into()),
            Item::Pred(PredDecl { name: "stale".into(), arg_sorts: vec!["File".into()] }),
            Item::Pred(PredDecl { name: "rebuild".into(), arg_sorts: vec!["File".into()] }),
            Item::Abducible(PredDecl { name: "needs_rebuild".into(), arg_sorts: vec!["File".into()] }),
            Item::Rule(Rule {
                head: atom("rebuild", vec![v("T")]),
                body: vec![pos("stale", vec![v("T")]), pos("needs_rebuild", vec![v("T")])],
            }),
            Item::Fact(atom("stale", vec![c("main")])),
            // ghost has no stale fact, so no needs_rebuild hypothesis helps.
            Item::Abduce(atom("rebuild", vec![c("ghost")])),
        ],
    };
    let sol = solve(&elaborate(&prog).unwrap()).unwrap();
    assert!(!sol.abductions[0].explained(), "rebuild(ghost) cannot be abduced");
}

/// **Integrity constraints** (`:- B`): the program is inconsistent iff a
/// constraint body holds in the least model. A graph-2-coloring constraint
/// `:- edge(A,B), color(A,C), color(B,C)` is violated when adjacent nodes share
/// a color, and satisfied otherwise.
#[test]
fn integrity_constraint_consistency() {
    let base = |c_a: &str, c_b: &str| Program {
        items: vec![
            Item::Sort("Node".into()),
            Item::Enum(adsmt_ir_asp::ast::EnumDef {
                name: "Color".into(),
                ctors: vec!["red".into(), "blue".into()],
            }),
            Item::Pred(PredDecl { name: "edge".into(), arg_sorts: vec!["Node".into(), "Node".into()] }),
            Item::Pred(PredDecl { name: "color".into(), arg_sorts: vec!["Node".into(), "Color".into()] }),
            Item::Fact(atom("edge", vec![c("x"), c("y")])),
            Item::Fact(atom("color", vec![c("x"), c(c_a)])),
            Item::Fact(atom("color", vec![c("y"), c(c_b)])),
            // :- edge(A,B), color(A,C), color(B,C).
            Item::Constraint(vec![
                pos("edge", vec![v("A"), v("B")]),
                pos("color", vec![v("A"), v("C")]),
                pos("color", vec![v("B"), v("C")]),
            ]),
        ],
    };
    // x,y adjacent, both red → constraint violated → inconsistent.
    assert!(!solve(&elaborate(&base("red", "red")).unwrap()).unwrap().consistent);
    // different colors → satisfied → consistent.
    assert!(solve(&elaborate(&base("red", "blue")).unwrap()).unwrap().consistent);
}

/// A constraint with a theory atom: `:- over(T), dur(T, D), { D > 100 }` flags a
/// too-long scheduled task.
#[test]
fn integrity_constraint_with_theory() {
    let prog = |d: i64| Program {
        items: vec![
            Item::Sort("Task".into()),
            Item::Pred(PredDecl { name: "dur".into(), arg_sorts: vec!["Task".into(), "Int".into()] }),
            Item::Fact(atom("dur", vec![c("t1"), T::Int(d)])),
            Item::Constraint(vec![
                pos("dur", vec![v("T"), v("D")]),
                Literal::Theory(Theory { op: CmpOp::Gt, lhs: Expr::Var("D".into()), rhs: Expr::Lit(100) }),
            ]),
        ],
    };
    assert!(!solve(&elaborate(&prog(150)).unwrap()).unwrap().consistent, "150 > 100 violates");
    assert!(solve(&elaborate(&prog(50)).unwrap()).unwrap().consistent, "50 is fine");
}

/// **L1 safety**: a theory variable not bound by a positive body atom is unsafe
/// (it would range over the infinite integers).
#[test]
fn unbound_theory_variable_is_unsafe() {
    use adsmt_ir_asp::FaceError;
    let prog = Program {
        items: vec![
            Item::Sort("Task".into()),
            Item::Pred(PredDecl { name: "p".into(), arg_sorts: vec!["Task".into()] }),
            Item::Pred(PredDecl { name: "q".into(), arg_sorts: vec!["Task".into()] }),
            // p(T) :- q(T), { N > 0 }.   — N unbound.
            Item::Rule(Rule {
                head: atom("p", vec![v("T")]),
                body: vec![
                    pos("q", vec![v("T")]),
                    Literal::Theory(Theory { op: CmpOp::Gt, lhs: Expr::Var("N".into()), rhs: Expr::Lit(0) }),
                ],
            }),
        ],
    };
    assert!(matches!(elaborate(&prog), Err(FaceError::Unsafe(_))));
}
