//! The advisory **unsoundness/vacuity linter** (`lint`) — a pure observer that
//! surfaces unsoundness-hygiene issues without changing a verdict. End-to-end
//! (`parse → lint`). All MVP findings are `Info` (advisory).

use adsmt_ir_asp::{Severity, lint, parse};

fn rules(src: &str) -> Vec<String> {
    lint(&parse(src).unwrap()).into_iter().map(|d| d.rule.to_string()).collect()
}

/// A clean, consistent program raises **no** lint.
#[test]
fn clean_program_is_silent() {
    let src = r#"
        sort Node.
        pred edge(Node, Node).
        pred reach(Node, Node).
        edge(a, b). edge(b, c).
        reach(X, Y) :- edge(X, Y).
        reach(X, Z) :- reach(X, Y), edge(Y, Z).
    "#;
    assert!(lint(&parse(src).unwrap()).is_empty());
}

/// `asp-vacuity` (the dual of LINT-VAC): an integrity constraint that eliminates
/// every model ⇒ no answer set ⇒ a soft `Info` vacuity note.
#[test]
fn vacuity_no_answer_set() {
    let src = r#"
        sort Node.
        pred node(Node).
        pred colored(Node).
        node(a). node(b).
        colored(a).
        :- node(X), not colored(X).
    "#;
    // b is uncolored ⇒ the constraint is violated ⇒ no answer set.
    let ds = lint(&parse(src).unwrap());
    assert!(ds.iter().any(|d| d.rule == "asp-vacuity" && d.severity == Severity::Info));
}

/// `asp-nonstratified`: a negative cycle is flagged (decided by the L3 gate,
/// not the perfect model). It is consistent (two answer sets), so NO vacuity.
#[test]
fn nonstratified_negative_cycle() {
    let src = r#"
        sort T.
        pred d(T).
        pred p(T).
        pred q(T).
        d(x).
        p(X) :- d(X), not q(X).
        q(X) :- d(X), not p(X).
    "#;
    let rs = rules(src);
    assert!(rs.contains(&"asp-nonstratified".to_string()));
    assert!(!rs.contains(&"asp-vacuity".to_string()), "it has answer sets ⇒ no vacuity");
}

/// A self-negation (no answer set) raises BOTH the negative-cycle note and the
/// vacuity note — distinct, both advisory.
#[test]
fn self_negation_is_nonstratified_and_vacuous() {
    let src = r#"
        sort T.
        pred d(T).
        pred p(T).
        d(x).
        p(X) :- d(X), not p(X).
    "#;
    let rs = rules(src);
    assert!(rs.contains(&"asp-nonstratified".to_string()));
    assert!(rs.contains(&"asp-vacuity".to_string()));
}

/// `asp-unsafe`: an unsafe variable (the elaborator's hard `Unsafe` error)
/// surfaced as an advisory diagnostic.
#[test]
fn unsafe_variable_surfaced() {
    let src = r#"
        sort T.
        pred p(T).
        pred q(T).
        pred bad(T).
        bad(X) :- p(X), not q(Y).
    "#;
    let ds = lint(&parse(src).unwrap());
    assert!(ds.iter().any(|d| d.rule == "asp-unsafe" && d.severity == Severity::Info));
}

/// `lint_source` attaches a **precise source location** to the per-item
/// `asp-unsafe` finding (the IDE-squiggle position), pointing at the offending
/// rule's line. The whole-program notes stay file-level (`source_loc: None`).
#[test]
fn lint_source_locates_the_unsafe_rule() {
    // line 6 is the unsafe rule: `Y` under `not` is not bound by a positive atom.
    let src = "sort T.\n\
               pred p(T).\n\
               pred q(T).\n\
               pred bad(T).\n\
               p(a).\n\
               bad(X) :- p(X), not q(Y).\n";
    let ds = adsmt_ir_asp::lint_source(src);
    let d = ds.iter().find(|d| d.rule == "asp-unsafe").expect("asp-unsafe found");
    let loc = d.source_loc.expect("a precise source location is attached");
    assert_eq!(loc.line, 6, "points at the unsafe rule's line; got {loc:?}");
    // a clean program through lint_source raises nothing.
    assert!(adsmt_ir_asp::lint_source("sort T.\npred p(T).\np(a).\n").is_empty());
}

/// The linter never changes a verdict: every finding is `Info`, and a parse /
/// kernel error (not an unsoundness lint) yields no diagnostics.
#[test]
fn non_lint_errors_are_silent() {
    // an unknown predicate is a kernel/elaboration error, not an unsoundness lint.
    let src = r#"
        sort T.
        pred p(T).
        q(a).
    "#;
    assert!(lint(&parse(src).unwrap()).is_empty());
}
