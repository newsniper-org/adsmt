//! Horn-clause rule base for abductive SLD chaining.
//!
//! A [`HornRule`] is the v0.17 surface for a deductive rule
//! `head :- body₁, body₂, …, bodyₙ`. The body atoms must each be
//! resolved (either via further rule firing or by abducing them
//! from the [`AbducibleSet`](crate::abducible::AbducibleSet))
//! for the rule's head to be derivable.
//!
//! Matching is currently propositional — heads and goals match by
//! α-equivalence, with no first-order unification. The
//! `head_matches` hook keeps the door open for a unifying matcher
//! once the lu-kb typed-arg surface lands.
//!
//! Rules are owned by a [`HornRuleBase`] and consumed read-only by
//! the [`crate::SldEngine`]; mutation is restricted to insertion at
//! load time.

use std::collections::HashSet;
use std::sync::Arc;

use adsmt_core::{Term, TermInner, Var};

/// A single Horn clause `head :- body₁ … bodyₙ`.
///
/// `source` carries the origin tag (typically the lu-kb rule
/// block's `<module>::<name>`) so candidates produced via this
/// rule can attribute their provenance correctly.
#[derive(Clone, Debug)]
pub struct HornRule {
    pub head: Term,
    pub body: Vec<Term>,
    pub source: String,
}

impl HornRule {
    /// Construct a Horn rule. An empty body means the head is a
    /// fact — see [`HornRule::fact`] for the more readable
    /// constructor.
    pub fn new(
        head: Term,
        body: Vec<Term>,
        source: impl Into<String>,
    ) -> Self {
        Self { head, body, source: source.into() }
    }

    /// Construct a fact rule (head with empty body).
    pub fn fact(head: Term, source: impl Into<String>) -> Self {
        Self::new(head, Vec::new(), source)
    }

    /// Does this rule's head propositionally match `goal`?
    ///
    /// v0.17 used α-equivalence; v0.19 keeps that as the default
    /// — variables in the head are treated as **atomic** unless
    /// a future `with_schematic` constructor introduces real
    /// first-order schemas. This preserves backward compatibility:
    /// propositional rules like `fact p ⟸ q` match goal `p` only
    /// when the rule head is α-equivalent.
    pub fn head_matches(&self, goal: &Term) -> bool {
        self.head.alpha_eq(goal)
    }
}

/// v0.19 D.3 — Horn rule with explicit schematic (universally
/// quantified) variables in the head + body.
///
/// Distinct from [`HornRule`] in two ways:
/// 1. The `schematic_vars` set lists every head/body variable
///    that should be treated as a substitution candidate.
/// 2. [`Self::head_matches`] does first-order unification rather
///    than α-equivalence: `fact pred(x) ⟸ ...` matches goal
///    `pred(a)` with substitution `[x ↦ a]`.
///
/// The two rule shapes coexist so adsmt-abduce v0.17's
/// propositional pipeline keeps working unchanged while the
/// v0.19+ typed-argument pipeline opts in to the richer
/// unification by constructing this type directly.
#[derive(Clone, Debug)]
pub struct SchematicHornRule {
    pub head: Term,
    pub body: Vec<Term>,
    pub source: String,
    /// Every variable name in `head` / `body` that should be
    /// treated as schematic. Variables not in this list match
    /// only by α-equivalence.
    pub schematic_vars: Vec<String>,
}

impl SchematicHornRule {
    pub fn new(
        head: Term,
        body: Vec<Term>,
        schematic_vars: Vec<String>,
        source: impl Into<String>,
    ) -> Self {
        Self {
            head,
            body,
            schematic_vars,
            source: source.into(),
        }
    }

    /// First-order match: head unifies with goal, only the
    /// schematic vars participate as substitution candidates.
    pub fn head_matches(&self, goal: &Term) -> bool {
        self.head_unify(goal).is_some()
    }

    /// Return the unifying substitution from `head` to `goal`,
    /// or `None` when no such substitution exists. Only the
    /// listed schematic vars are unification candidates; all
    /// other vars must match by α-equivalence.
    pub fn head_unify(&self, goal: &Term) -> Option<Vec<(String, Term)>> {
        let mut subst: Vec<(String, Term)> = Vec::new();
        if Self::unify_inner(&self.head, goal, &self.schematic_vars, &mut subst) {
            Some(subst)
        } else {
            None
        }
    }

    fn unify_inner(
        pattern: &Term,
        goal: &Term,
        schematic: &[String],
        subst: &mut Vec<(String, Term)>,
    ) -> bool {
        // Higher-order (flexible) head: if the pattern's spine head is
        // a schematic variable and it is applied to ≥1 argument, only
        // the Miller pattern fragment (Lλ — **distinct** variable
        // arguments) is solvable. The MGU against a goal `t` is then
        // `F ↦ λb₁ … bₙ. t` (occurs-checked; SLD goals are top-level
        // so no escaping-bound-variable scope check is needed). A
        // flexible head that is *not* a pattern (non-distinct or
        // non-variable arguments) lies outside the decidable fragment
        // and does not match — crucially, it must NOT fall through to
        // the structural descent below, which would spuriously match a
        // partial sub-spine (e.g. read `F(x, x)` as `(F x) x`).
        if let TermInner::Var(h) = spine_head(pattern).kind()
            && schematic.iter().any(|s| s == &h.name)
            && matches!(pattern.kind(), TermInner::App(..))
        {
            return match flex_pattern(pattern, schematic) {
                Some((f, spine)) => {
                    if goal.free_vars().iter().any(|v| v.name == f) {
                        return false; // occurs check
                    }
                    let lambda = build_lambda(&spine, goal);
                    match subst.iter().find(|(name, _)| name == &f) {
                        Some((_, existing)) => existing.alpha_eq(&lambda),
                        None => {
                            subst.push((f, lambda));
                            true
                        }
                    }
                }
                None => false,
            };
        }

        match pattern.kind() {
            TermInner::Var(v) => {
                if schematic.iter().any(|s| s == &v.name) {
                    if let Some((_, existing)) =
                        subst.iter().find(|(name, _)| name == &v.name)
                    {
                        return existing.alpha_eq(goal);
                    }
                    if v.ty != goal.type_of() {
                        return false;
                    }
                    subst.push((v.name.clone(), goal.clone()));
                    true
                } else {
                    // Non-schematic var — α-equivalence only.
                    pattern.alpha_eq(goal)
                }
            }
            TermInner::Const(c) => match goal.kind() {
                TermInner::Const(c2) => c.name == c2.name && c.ty == c2.ty,
                _ => false,
            },
            TermInner::App(f1, x1) => match goal.kind() {
                TermInner::App(f2, x2) => {
                    Self::unify_inner(f1, f2, schematic, subst)
                        && Self::unify_inner(x1, x2, schematic, subst)
                }
                _ => false,
            },
            TermInner::Lam(_, _) => pattern.alpha_eq(goal),
        }
    }
}

/// The head of an applicative spine: peel `App(App(…(h, a₁)…), aₙ)`
/// down to `h`.
fn spine_head(t: &Term) -> &Term {
    let mut cur = t;
    while let TermInner::App(f, _) = cur.kind() {
        cur = f;
    }
    cur
}

/// Recognise a higher-order pattern flexible head: a term
/// `F b₁ … bₙ` (n ≥ 1) whose spine head `F` is a schematic variable
/// and whose arguments `b₁ … bₙ` are **distinct** variables. Returns
/// `(F's name, [b₁ … bₙ])` in application order, or `None` when the
/// term is not such a pattern.
fn flex_pattern(pattern: &Term, schematic: &[String]) -> Option<(String, Vec<Arc<Var>>)> {
    let mut spine: Vec<Arc<Var>> = Vec::new();
    let mut cur = pattern;
    loop {
        match cur.kind() {
            TermInner::App(f, x) => {
                match x.kind() {
                    TermInner::Var(v) => spine.push(v.clone()),
                    _ => return None, // arg is not a variable → not a pattern
                }
                cur = f;
            }
            TermInner::Var(v)
                if !spine.is_empty() && schematic.iter().any(|s| s == &v.name) =>
            {
                spine.reverse();
                let mut seen = HashSet::new();
                for b in &spine {
                    if !seen.insert(b.name.clone()) {
                        return None; // spine variables must be distinct
                    }
                }
                return Some((v.name.clone(), spine));
            }
            _ => return None,
        }
    }
}

/// Build `λb₁ … bₙ. body`.
fn build_lambda(spine: &[Arc<Var>], body: &Term) -> Term {
    let mut t = body.clone();
    for v in spine.iter().rev() {
        t = Term::lam((**v).clone(), t);
    }
    t
}

/// Owned collection of Horn rules. Insertion-only at load time;
/// the SLD engine borrows immutably during candidate generation.
#[derive(Default, Clone, Debug)]
pub struct HornRuleBase {
    rules: Vec<HornRule>,
}

impl HornRuleBase {
    pub fn new() -> Self { Self::default() }

    pub fn insert(&mut self, r: HornRule) { self.rules.push(r); }

    pub fn iter(&self) -> impl Iterator<Item = &HornRule> {
        self.rules.iter()
    }

    pub fn len(&self) -> usize { self.rules.len() }
    pub fn is_empty(&self) -> bool { self.rules.is_empty() }

    /// All rules whose head matches `goal`.
    pub fn rules_matching<'a>(
        &'a self,
        goal: &'a Term,
    ) -> impl Iterator<Item = &'a HornRule> + 'a {
        self.rules.iter().filter(move |r| r.head_matches(goal))
    }
}

/// Owned collection of schematic (first-order) Horn rules — the
/// unifying counterpart to [`HornRuleBase`]. The SLD engine attaches
/// one alongside (or instead of) the propositional base.
#[derive(Default, Clone, Debug)]
pub struct SchematicHornRuleBase {
    rules: Vec<SchematicHornRule>,
}

impl SchematicHornRuleBase {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, r: SchematicHornRule) {
        self.rules.push(r);
    }

    pub fn iter(&self) -> impl Iterator<Item = &SchematicHornRule> {
        self.rules.iter()
    }

    pub fn len(&self) -> usize {
        self.rules.len()
    }
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }

    /// Every rule whose head unifies with `goal`, paired with the
    /// head→goal substitution (so the caller can instantiate the
    /// rule's body before resolving it).
    pub fn rules_matching<'a>(
        &'a self,
        goal: &'a Term,
    ) -> impl Iterator<Item = (&'a SchematicHornRule, Vec<(String, Term)>)> + 'a {
        self.rules.iter().filter_map(move |r| r.head_unify(goal).map(|s| (r, s)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Type;

    #[test]
    fn fact_rule_has_empty_body() {
        let p = Term::var("p", Type::bool_());
        let r = HornRule::fact(p.clone(), "kb::demo");
        assert!(r.body.is_empty());
        assert!(r.head_matches(&p));
    }

    #[test]
    fn head_matches_under_alpha_eq() {
        let p = Term::var("p", Type::bool_());
        let r = HornRule::new(p.clone(), vec![], "kb::demo");
        let q = Term::var("q", Type::bool_());
        assert!(r.head_matches(&p));
        assert!(!r.head_matches(&q));
    }

    #[test]
    fn rules_matching_returns_only_matching_heads() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let mut base = HornRuleBase::new();
        base.insert(HornRule::fact(p.clone(), "src1"));
        base.insert(HornRule::fact(q.clone(), "src2"));
        let matches: Vec<&HornRule> = base.rules_matching(&p).collect();
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].source, "src1");
    }

    // === v0.19 D.3 typed-arg unification (SchematicHornRule) ===

    #[test]
    fn schematic_head_unifies_via_variable_binding() {
        // Rule head: `pred(x)` with x a schematic variable.
        // Goal: `pred(a)`.
        let int_ty = Type::const_("Int", adsmt_core::Kind::Type);
        let pred_ty =
            Type::fun(int_ty.clone(), Type::bool_()).unwrap();
        let pred = Term::const_("pred", pred_ty);
        let x = Term::var("x", int_ty.clone());
        let head = Term::app(pred.clone(), x).unwrap();
        let a = Term::const_("a", int_ty);
        let goal = Term::app(pred, a.clone()).unwrap();

        let rule = SchematicHornRule::new(
            head,
            vec![],
            vec!["x".into()],
            "test",
        );
        assert!(rule.head_matches(&goal));
        let subst = rule.head_unify(&goal).expect("unification succeeds");
        assert_eq!(subst.len(), 1);
        assert_eq!(subst[0].0, "x");
        assert!(subst[0].1.alpha_eq(&a));
    }

    #[test]
    fn schematic_head_unify_type_clash_fails() {
        let int_ty = Type::const_("Int", adsmt_core::Kind::Type);
        let bool_ty = Type::bool_();
        let x = Term::var("x", int_ty);
        let q = Term::var("q", bool_ty);
        let rule = SchematicHornRule::new(
            x,
            vec![],
            vec!["x".into()],
            "test",
        );
        assert!(rule.head_unify(&q).is_none());
    }

    #[test]
    fn schematic_head_unify_consistent_repeated_var() {
        // Pattern f(x, x) vs f(a, a) — single binding x ↦ a.
        let int_ty = Type::const_("Int", adsmt_core::Kind::Type);
        let f_ty = Type::fun(
            int_ty.clone(),
            Type::fun(int_ty.clone(), Type::bool_()).unwrap(),
        )
        .unwrap();
        let f = Term::const_("f", f_ty);
        let x = Term::var("x", int_ty.clone());
        let head =
            Term::app(Term::app(f.clone(), x.clone()).unwrap(), x).unwrap();
        let a = Term::const_("a", int_ty);
        let goal =
            Term::app(Term::app(f, a.clone()).unwrap(), a).unwrap();
        let rule = SchematicHornRule::new(
            head,
            vec![],
            vec!["x".into()],
            "test",
        );
        assert!(rule.head_matches(&goal));
        let subst = rule.head_unify(&goal).expect("consistent unify");
        assert_eq!(subst.len(), 1);
    }

    #[test]
    fn schematic_head_unify_inconsistent_repeated_var_fails() {
        let int_ty = Type::const_("Int", adsmt_core::Kind::Type);
        let f_ty = Type::fun(
            int_ty.clone(),
            Type::fun(int_ty.clone(), Type::bool_()).unwrap(),
        )
        .unwrap();
        let f = Term::const_("f", f_ty);
        let x = Term::var("x", int_ty.clone());
        let head =
            Term::app(Term::app(f.clone(), x.clone()).unwrap(), x).unwrap();
        let a = Term::const_("a", int_ty.clone());
        let b = Term::const_("b", int_ty);
        let goal = Term::app(Term::app(f, a).unwrap(), b).unwrap();
        let rule = SchematicHornRule::new(
            head,
            vec![],
            vec!["x".into()],
            "test",
        );
        assert!(!rule.head_matches(&goal));
        assert!(rule.head_unify(&goal).is_none());
    }

    #[test]
    fn higher_order_pattern_flex_head_binds_lambda() {
        // Pattern `F(x)` (F a schematic predicate var, x a distinct
        // var) unifies with `g(a)` by the Miller MGU `F ↦ λx. g(a)`.
        use adsmt_core::Kind;
        let int_ty = Type::const_("Int", Kind::Type);
        let pred_ty = Type::fun(int_ty.clone(), Type::bool_()).unwrap();
        let big_f = Term::var("F", pred_ty.clone());
        let x = Term::var("x", int_ty.clone());
        let head = Term::app(big_f, x).unwrap(); // F(x)
        let g = Term::const_("g", pred_ty);
        let a = Term::const_("a", int_ty.clone());
        let goal = Term::app(g, a).unwrap(); // g(a)

        let rule = SchematicHornRule::new(head, vec![], vec!["F".into(), "x".into()], "ho");
        let subst = rule.head_unify(&goal).expect("HO pattern unifies");
        let f_bind = subst
            .iter()
            .find(|(n, _)| n == "F")
            .map(|(_, t)| t.clone())
            .expect("F is bound");
        // Applying the binding to any argument β-reduces to g(a).
        let z = Term::const_("z", int_ty);
        let reduced = Term::app(f_bind, z).unwrap().beta_reduce().unwrap();
        assert!(reduced.alpha_eq(&goal));
    }

    #[test]
    fn higher_order_non_pattern_repeated_arg_falls_back() {
        // `F(x, x)` is NOT a higher-order pattern (args not distinct),
        // so it does not take the flex-head path; structural
        // unification applies and the type-clashing goal fails.
        use adsmt_core::Kind;
        let int_ty = Type::const_("Int", Kind::Type);
        let pred2_ty = Type::fun(
            int_ty.clone(),
            Type::fun(int_ty.clone(), Type::bool_()).unwrap(),
        )
        .unwrap();
        let big_f = Term::var("F", pred2_ty.clone());
        let x = Term::var("x", int_ty.clone());
        let head =
            Term::app(Term::app(big_f, x.clone()).unwrap(), x).unwrap(); // F(x, x)
        let g = Term::const_("g", pred2_ty);
        let a = Term::const_("a", int_ty.clone());
        let b = Term::const_("b", int_ty);
        let goal = Term::app(Term::app(g, a).unwrap(), b).unwrap(); // g(a, b), a ≠ b
        let rule =
            SchematicHornRule::new(head, vec![], vec!["F".into(), "x".into()], "ho");
        // Not a pattern → structural; F↦g then x↦a vs x↦b inconsistent.
        assert!(rule.head_unify(&goal).is_none());
    }

    #[test]
    fn schematic_non_listed_var_falls_back_to_alpha() {
        // Var `y` is NOT listed as schematic — α-equivalence
        // applies. `y` and `z` (distinct names) must NOT unify.
        let bool_ty = Type::bool_();
        let y = Term::var("y", bool_ty.clone());
        let z = Term::var("z", bool_ty);
        let rule = SchematicHornRule::new(y, vec![], vec![], "test");
        assert!(!rule.head_matches(&z));
    }
}
