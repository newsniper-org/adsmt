//! Datatypes with argument-bearing constructors (`data Tree = leaf |
//! node(Tree, Tree)`), ground constructor terms in atoms, and the subterm-closed
//! active term universe. (Constructor *patterns* with variables — the binding
//! first-order matching — are the next sub-slice.)

use adsmt_ir_asp::ast::{
    Atom, Ctor, DataDef, EnumDef, Item, Literal, PredDecl, Program, Rule, Term as T,
};
use adsmt_ir_asp::{elaborate, solve};

fn v(s: &str) -> T {
    T::Var(s.into())
}
fn c(s: &str) -> T {
    T::Const(s.into())
}
fn app(name: &str, args: Vec<T>) -> T {
    T::App(name.into(), args)
}
fn leaf() -> T {
    T::Const("leaf".into())
}
fn atom(pred: &str, args: Vec<T>) -> Atom {
    Atom { pred: pred.into(), args }
}
fn pos(pred: &str, args: Vec<T>) -> Literal {
    Literal::Pos(atom(pred, args))
}

fn tree_data() -> Item {
    Item::Data(DataDef {
        name: "Tree".into(),
        ctors: vec![
            Ctor { name: "leaf".into(), arg_sorts: vec![] },
            Ctor { name: "node".into(), arg_sorts: vec!["Tree".into(), "Tree".into()] },
        ],
    })
}

/// A recursive datatype is admitted (the kernel's positivity gate accepts
/// `node : Tree -> Tree -> Tree`), its constructors are usable, and ground
/// constructor terms in facts are queryable.
#[test]
fn datatype_ground_terms() {
    let prog = Program {
        items: vec![
            tree_data(),
            Item::Pred(PredDecl { name: "tree".into(), arg_sorts: vec!["Tree".into()] }),
            Item::Fact(atom("tree", vec![app("node", vec![leaf(), leaf()])])),
            Item::Fact(atom("tree", vec![leaf()])),
            Item::Query(atom("tree", vec![v("X")])),
        ],
    };
    let elab = elaborate(&prog).expect("datatype elaborates");
    assert!(elab.env.lookup("Tree").is_some());
    assert!(elab.env.ctor_of("node").is_some(), "node is a kernel constructor");
    let sol = solve(&elab).unwrap();
    let mut trees: Vec<String> = sol.answers[0].tuples.iter().map(|t| t[0].clone()).collect();
    trees.sort();
    assert_eq!(trees, vec!["leaf", "node(leaf,leaf)"]);
}

/// The active term universe is **subterm-closed**: a single nested fact seeds
/// the domain with every subterm tree (so a later matching slice can range over
/// them).
#[test]
fn universe_is_subterm_closed() {
    let prog = Program {
        items: vec![
            tree_data(),
            Item::Pred(PredDecl { name: "tree".into(), arg_sorts: vec!["Tree".into()] }),
            // one deep fact: node(node(leaf,leaf), leaf).
            Item::Fact(atom(
                "tree",
                vec![app("node", vec![app("node", vec![leaf(), leaf()]), leaf()])],
            )),
        ],
    };
    let elab = elaborate(&prog).expect("elaborates");
    let dom = elab.domains.get("Tree").expect("Tree domain");
    for sub in ["leaf", "node(leaf,leaf)", "node(node(leaf,leaf),leaf)"] {
        assert!(dom.contains(&sub.to_string()), "subterm `{sub}` is in the universe; have {dom:?}");
    }
}

/// A rule over a whole datatype-sort variable grounds over the term universe.
#[test]
fn rule_over_datatype_variable() {
    let prog = Program {
        items: vec![
            tree_data(),
            Item::Pred(PredDecl { name: "tree".into(), arg_sorts: vec!["Tree".into()] }),
            Item::Pred(PredDecl { name: "known".into(), arg_sorts: vec!["Tree".into()] }),
            // known(T) :- tree(T).
            Item::Rule(Rule {
                head: atom("known", vec![v("T")]),
                body: vec![Literal::Pos(atom("tree", vec![v("T")]))],
            }),
            Item::Fact(atom("tree", vec![app("node", vec![leaf(), leaf()])])),
            Item::Query(atom("known", vec![app("node", vec![leaf(), leaf()])])),
        ],
    };
    let sol = solve(&elaborate(&prog).unwrap()).unwrap();
    assert!(sol.answers[0].holds(), "known(node(leaf,leaf)) derived from the tree fact");
}

/// **First-order matching — destructuring in a body**: `connects(X, Y) :-
/// edge(pair(X, Y))` matches each appearing `edge(pair(a, b))` fact, binding the
/// subterm variables `X`, `Y`.
#[test]
fn destructuring_match_in_body() {
    let prog = Program {
        items: vec![
            Item::Enum(EnumDef { name: "Node".into(), ctors: vec!["a".into(), "b".into(), "cc".into()] }),
            Item::Data(DataDef {
                name: "Pair".into(),
                ctors: vec![Ctor { name: "pair".into(), arg_sorts: vec!["Node".into(), "Node".into()] }],
            }),
            Item::Pred(PredDecl { name: "edge".into(), arg_sorts: vec!["Pair".into()] }),
            Item::Pred(PredDecl { name: "connects".into(), arg_sorts: vec!["Node".into(), "Node".into()] }),
            // connects(X, Y) :- edge(pair(X, Y)).
            Item::Rule(Rule {
                head: atom("connects", vec![v("X"), v("Y")]),
                body: vec![pos("edge", vec![app("pair", vec![v("X"), v("Y")])])],
            }),
            Item::Fact(atom("edge", vec![app("pair", vec![c("a"), c("b")])])),
            Item::Fact(atom("edge", vec![app("pair", vec![c("b"), c("cc")])])),
            Item::Query(atom("connects", vec![v("X"), v("Y")])),
        ],
    };
    let sol = solve(&elaborate(&prog).unwrap()).unwrap();
    let mut pairs: Vec<(String, String)> =
        sol.answers[0].tuples.iter().map(|t| (t[0].clone(), t[1].clone())).collect();
    pairs.sort();
    assert_eq!(pairs, vec![("a".into(), "b".into()), ("b".into(), "cc".into())]);
}

/// **First-order matching — structural recursion**: list membership, the
/// canonical recursive-matching program. `member(X, cons(X, T)).` is a head
/// pattern (range-restricted by the universe), and the recursive clause
/// destructures the tail. Queried over `cons(a, cons(b, nil))`.
#[test]
fn structural_recursion_list_membership() {
    let list = || {
        // cons(a, cons(b, nil))
        app("cons", vec![c("a"), app("cons", vec![c("b"), T::Const("nil".into())])])
    };
    let items = vec![
        Item::Enum(EnumDef { name: "Node".into(), ctors: vec!["a".into(), "b".into(), "cc".into()] }),
        Item::Data(DataDef {
            name: "List".into(),
            ctors: vec![
                Ctor { name: "nil".into(), arg_sorts: vec![] },
                Ctor { name: "cons".into(), arg_sorts: vec!["Node".into(), "List".into()] },
            ],
        }),
        Item::Pred(PredDecl { name: "member".into(), arg_sorts: vec!["Node".into(), "List".into()] }),
        // member(X, cons(X, T)).
        Item::Rule(Rule {
            head: atom("member", vec![v("X"), app("cons", vec![v("X"), v("T")])]),
            body: vec![],
        }),
        // member(X, cons(Y, T)) :- member(X, T).
        Item::Rule(Rule {
            head: atom("member", vec![v("X"), app("cons", vec![v("Y"), v("T")])]),
            body: vec![pos("member", vec![v("X"), v("T")])],
        }),
    ];
    // yes: b is in the list.
    let yes = Program {
        items: {
            let mut it = items.clone();
            it.push(Item::Query(atom("member", vec![c("b"), list()])));
            it
        },
    };
    assert!(solve(&elaborate(&yes).unwrap()).unwrap().answers[0].holds(), "b ∈ [a,b]");
    // no: cc is not in the list.
    let no = Program {
        items: {
            let mut it = items;
            it.push(Item::Query(atom("member", vec![c("cc"), list()])));
            it
        },
    };
    assert!(!solve(&elaborate(&no).unwrap()).unwrap().answers[0].holds(), "cc ∉ [a,b]");
}

/// A constructor used at the wrong sort, or with the wrong arity, is rejected.
#[test]
fn datatype_misuse_rejected() {
    use adsmt_ir_asp::FaceError;
    // node applied to one argument instead of two.
    let bad_arity = Program {
        items: vec![
            tree_data(),
            Item::Pred(PredDecl { name: "tree".into(), arg_sorts: vec!["Tree".into()] }),
            Item::Fact(atom("tree", vec![app("node", vec![leaf()])])),
        ],
    };
    assert!(matches!(elaborate(&bad_arity), Err(FaceError::Unsupported(_))));
}
