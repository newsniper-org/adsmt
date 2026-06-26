//! Elaborator-foundation conformance: a typed-ASP program's declarations
//! (`sort`/`enum`/`pred`) and ground atoms (facts/ground queries) elaborate
//! through the kernel's checked admitters, and the rejection paths (unknown
//! predicate, wrong arity, sort mismatch, unsafe variable) surface as
//! `FaceError`s — never a trusted ill-typed term.

use adsmt_ir::{Term, is_def_eq, type_of};
use adsmt_ir_asp::FaceError;
use adsmt_ir_asp::ast::{Atom, EnumDef, Item, Literal, PredDecl, Program, Rule, Term as T};
use adsmt_ir_asp::elaborate;

fn cst(s: &str) -> T {
    T::Const(s.into())
}
fn atom(pred: &str, args: Vec<T>) -> Atom {
    Atom { pred: pred.into(), args }
}

/// A representative L0 program: a sort, an enum, typed predicates, ground facts,
/// and a ground query all elaborate; every fact/query is a checked `Prop` and
/// the declarations + auto-declared object constants are in the env.
#[test]
fn l0_program_elaborates() {
    let prog = Program {
        items: vec![
            Item::Sort("Node".into()),
            Item::Enum(EnumDef { name: "Color".into(), ctors: vec!["Red".into(), "Green".into()] }),
            Item::Pred(PredDecl { name: "edge".into(), arg_sorts: vec!["Node".into(), "Node".into()] }),
            Item::Pred(PredDecl { name: "hue".into(), arg_sorts: vec!["Node".into(), "Color".into()] }),
            Item::Fact(atom("edge", vec![cst("a"), cst("b")])),
            Item::Fact(atom("hue", vec![cst("a"), cst("Red")])),
            Item::Query(atom("edge", vec![cst("a"), cst("b")])),
        ],
    };
    let r = elaborate(&prog).expect("elaborates");
    // declarations present.
    assert!(r.env.lookup("Node").is_some());
    assert!(r.env.lookup("Color").is_some());
    assert!(r.env.lookup("edge").is_some());
    assert!(r.env.ctor_of("Red").is_some(), "enum ctor usable");
    // auto-declared object constants present at their use sort.
    assert!(is_def_eq(&r.env, &type_of(&r.env, &Term::cnst("a")).unwrap(), &Term::cnst("Node")));
    // facts + query collected (each kernel-validated during elaboration).
    assert_eq!(r.facts.len(), 2);
    assert_eq!(r.queries.len(), 1);
    // the per-sort finite domains were recorded.
    assert_eq!(r.domains.get("Color").map(Vec::len), Some(2));
    assert!(r.domains.get("Node").unwrap().contains(&"a".to_string()));
}

/// An enum constructor used where a *different* sort is expected is a sort error.
#[test]
fn enum_ctor_sort_mismatch_rejected() {
    let prog = Program {
        items: vec![
            Item::Sort("Node".into()),
            Item::Enum(EnumDef { name: "Color".into(), ctors: vec!["Red".into()] }),
            Item::Pred(PredDecl { name: "edge".into(), arg_sorts: vec!["Node".into(), "Node".into()] }),
            // Red : Color used at a Node position.
            Item::Fact(atom("edge", vec![cst("a"), cst("Red")])),
        ],
    };
    assert!(matches!(elaborate(&prog), Err(FaceError::Unsupported(_))));
}

/// A constant reused at two different sorts is rejected (the precursor CanEq
/// sort-discipline).
#[test]
fn constant_at_two_sorts_rejected() {
    let prog = Program {
        items: vec![
            Item::Sort("Node".into()),
            Item::Sort("Edge".into()),
            Item::Pred(PredDecl { name: "p".into(), arg_sorts: vec!["Node".into()] }),
            Item::Pred(PredDecl { name: "q".into(), arg_sorts: vec!["Edge".into()] }),
            Item::Fact(atom("p", vec![cst("x")])),
            Item::Fact(atom("q", vec![cst("x")])), // x : Node already
        ],
    };
    assert!(matches!(elaborate(&prog), Err(FaceError::Unsupported(_))));
}

/// Unknown predicate, wrong arity, and an undeclared argument sort are each
/// rejected.
#[test]
fn malformed_declarations_and_atoms_rejected() {
    let unknown_pred = Program { items: vec![Item::Fact(atom("nope", vec![cst("a")]))] };
    assert!(matches!(elaborate(&unknown_pred), Err(FaceError::Unsupported(_))));

    let bad_arity = Program {
        items: vec![
            Item::Sort("S".into()),
            Item::Pred(PredDecl { name: "p".into(), arg_sorts: vec!["S".into()] }),
            Item::Fact(atom("p", vec![cst("a"), cst("b")])),
        ],
    };
    assert!(matches!(elaborate(&bad_arity), Err(FaceError::Unsupported(_))));

    let undeclared_sort = Program {
        items: vec![Item::Pred(PredDecl { name: "p".into(), arg_sorts: vec!["Ghost".into()] })],
    };
    assert!(matches!(elaborate(&undeclared_sort), Err(FaceError::Unsupported(_))));
}

/// A variable in a ground atom (fact) is an unsafe-rule rejection.
#[test]
fn variable_in_fact_is_unsafe() {
    let prog = Program {
        items: vec![
            Item::Sort("Node".into()),
            Item::Pred(PredDecl { name: "edge".into(), arg_sorts: vec!["Node".into(), "Node".into()] }),
            Item::Fact(atom("edge", vec![cst("a"), T::Var("X".into())])),
        ],
    };
    assert!(matches!(elaborate(&prog), Err(FaceError::Unsafe(_))));
}

/// Rules are collected (surface form) for the grounding slice, not yet checked.
#[test]
fn rules_are_collected_for_the_next_slice() {
    let prog = Program {
        items: vec![
            Item::Sort("Node".into()),
            Item::Pred(PredDecl { name: "edge".into(), arg_sorts: vec!["Node".into(), "Node".into()] }),
            Item::Pred(PredDecl { name: "reach".into(), arg_sorts: vec!["Node".into(), "Node".into()] }),
            Item::Rule(Rule {
                head: atom("reach", vec![T::Var("X".into()), T::Var("Y".into())]),
                body: vec![Literal::Pos(atom("edge", vec![T::Var("X".into()), T::Var("Y".into())]))],
            }),
        ],
    };
    let r = elaborate(&prog).expect("declarations elaborate");
    assert_eq!(r.rules.len(), 1, "the rule is collected for grounding");
}
