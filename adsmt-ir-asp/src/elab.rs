//! Elaborate a typed-ASP [`Program`](crate::ast::Program) into a checked kernel
//! environment + a validated surface program ready for grounding.
//!
//! Declarations (`sort`/`enum`/`pred`) are admitted through the kernel's
//! **checked admitters**; ground atoms (facts / ground queries) are `infer`'d
//! and checked to be a `Prop`; **definite rules** are sort-inferred,
//! safety-checked, and kernel-checked as the closed `Prop`
//! `∀X⃗. b₁ → … → bₙ → h` (the Π-implication carrier), where the body literals
//! include the L1 **theory interior** — `open` comparisons over a small `Int`
//! prelude, plus **CanEq** typed (dis)equality: a `{ lhs op rhs }` is routed by
//! the inferred operand sort (arithmetic on `Int`, structural `=`/`!=` on any
//! enum/datatype), so a cross-sort `Int = Node` is an elaboration error rather
//! than a silent atom. So a face bug can only ever yield a [`FaceError`], never
//! a trusted ill-typed term. The solving (grounding + the least-fixpoint gate,
//! with the theory atoms evaluated as the gate's `θ`) is [`crate::solve`].

use std::collections::HashMap;

use adsmt_ir::{Ctx, Env, Term, Univ, declare_inductive_indexed, infer, is_def_eq, postulate};

use crate::ast::{Atom, CmpOp, Ctor, Expr, Item, Literal, Program, Rule, Term as AspTerm, Theory};
use crate::error::FaceError;

/// The built-in integer sort.
pub(crate) const INT: &str = "Int";

/// The face-internal `false` proposition (the integrity-constraint conclusion).
const FALSE: &str = "#false";

/// The face-internal **negation-as-failure** wrapper (`#not : Prop → Prop`,
/// `open`). The kernel type-checks `#not (p t)` as a `Prop`; [`crate::solve`]
/// interprets it as "the atom is not in the (lower-stratum) model".
const NOT: &str = "#not";

/// The internal kernel name of a comparison operator (an `open` `Int→Int→Prop`).
pub(crate) fn cmp_sym(op: CmpOp) -> &'static str {
    match op {
        CmpOp::Lt => "#int.lt",
        CmpOp::Le => "#int.le",
        CmpOp::Eq => "#int.eq",
        CmpOp::Ne => "#int.ne",
        CmpOp::Gt => "#int.gt",
        CmpOp::Ge => "#int.ge",
    }
}

const ARITH: [&str; 3] = ["#int.add", "#int.sub", "#int.mul"];
const CMPS: [CmpOp; 6] = [CmpOp::Lt, CmpOp::Le, CmpOp::Eq, CmpOp::Ne, CmpOp::Gt, CmpOp::Ge];

/// The internal kernel name of a non-`Int` sort's structural **equality** symbol
/// (`#eq.S : S → S → Prop`, `open`).
pub(crate) fn eq_sym_name(sort: &str) -> String {
    format!("#eq.{sort}")
}

/// The internal kernel name of a non-`Int` sort's structural **disequality**
/// symbol (`#ne.S : S → S → Prop`, `open`).
pub(crate) fn ne_sym_name(sort: &str) -> String {
    format!("#ne.{sort}")
}

/// A human-readable operator spelling, for error messages.
fn op_str(op: CmpOp) -> &'static str {
    match op {
        CmpOp::Lt => "<",
        CmpOp::Le => "<=",
        CmpOp::Eq => "=",
        CmpOp::Ne => "!=",
        CmpOp::Gt => ">",
        CmpOp::Ge => ">=",
    }
}

/// The **stratification classification** of a program's predicate dependency
/// graph — the L2/L3 router. A program with no negative cycle is `Stratified`
/// (each predicate carries a stratum and the efficient perfect-model path
/// applies); a negative cycle makes it `NonStratified`, routing to the L3
/// stable-model gate ([`crate::solve`]).
///
/// The `want > n` saturation test that produces this is an **exact** classifier,
/// not a mere rejecter: in a negative-cycle-free program the longest
/// `not`-weighted dependency path is simple (a positive cycle adds no `not`
/// edge), so every stratum tops out at `≤ n-1 < n` and the test never fires;
/// a negative cycle pumps a stratum without bound, so it always does. Hence
/// `want > n ⟺ a negative cycle exists`.
#[derive(Debug, Clone)]
pub enum Stratification {
    /// No negative cycle: each predicate's stratum (a `not q` raises the head
    /// strictly above `q`), for the bottom-up perfect-model evaluation.
    Stratified(HashMap<String, usize>),
    /// A predicate depends on its own negation (a negative cycle); the perfect
    /// model is undefined, so solving routes to the L3 stable-model gate. Carries
    /// a human-readable reason (which predicate closed the cycle).
    NonStratified(String),
}

/// The result of elaborating a typed-ASP program.
#[derive(Debug)]
pub struct Elaborated {
    pub env: Env,
    pub facts: Vec<Atom>,
    pub rules: Vec<Rule>,
    pub queries: Vec<Atom>,
    /// Integrity constraint bodies (`:- B`) — kernel-checked, to be checked
    /// against the least model.
    pub constraints: Vec<Vec<Literal>>,
    /// Abductive goals (`?- abduce G`), each a checked ground atom.
    pub abduce_goals: Vec<Atom>,
    /// The names of predicates declared `abducible` (their ground instances are
    /// the hypothesis space).
    pub abducibles: Vec<String>,
    /// Per-sort finite domain: the constants (enum ctors + object constants +
    /// integer literals) plus the ground constructor terms (subterm-closed) that
    /// appear at that sort — the active term universe.
    pub domains: HashMap<String, Vec<String>>,
    pub pred_sorts: HashMap<String, Vec<String>>,
    /// Every constructor → (result sort, argument sorts) — for the grounder's
    /// pattern matching.
    pub ctor_sig: HashMap<String, (String, Vec<String>)>,
    /// Each predicate's **stratum** (L2): a `not q` body literal raises the head
    /// pred strictly above `q`, so the solver can evaluate strata bottom-up with
    /// every negation reading an already-decided lower stratum. Computed once the
    /// whole rule set is known; on a negative cycle this is an empty map and
    /// [`Self::stratify`] is [`Stratification::NonStratified`] (the L3 path is
    /// taken, which never reads `pred_strata`).
    pub pred_strata: HashMap<String, usize>,
    /// The L2/L3 router: `Stratified` ⇒ the perfect-model path uses
    /// [`Self::pred_strata`]; `NonStratified` ⇒ [`crate::solve`] runs the L3
    /// stable-model gate. A negative cycle now *elaborates* (it is no longer a
    /// hard [`FaceError::NonStratified`]) — the classification is the only L0–L2
    /// behavioural change.
    pub stratify: Stratification,
}

/// Elaborate a full typed-ASP program.
pub fn elaborate(program: &Program) -> Result<Elaborated, FaceError> {
    let mut e = Elaborator::new()?;
    for item in &program.items {
        e.item(item)?;
    }
    // classify (once the whole rule set is known): a negative cycle now routes to
    // the L3 stable-model gate rather than being refused.
    let stratify = e.compute_strata();
    let pred_strata = match &stratify {
        Stratification::Stratified(m) => m.clone(),
        Stratification::NonStratified(_) => HashMap::new(),
    };
    Ok(Elaborated {
        env: e.env,
        facts: e.facts,
        rules: e.rules,
        queries: e.queries,
        constraints: e.constraints,
        abduce_goals: e.abduce_goals,
        abducibles: e.abducibles,
        domains: e.domains,
        pred_sorts: e.preds,
        ctor_sig: e.ctor_sig,
        pred_strata,
        stratify,
    })
}

struct Elaborator {
    env: Env,
    preds: HashMap<String, Vec<String>>,
    /// every constructor (enum or datatype) → (result sort, argument sorts).
    ctor_sig: HashMap<String, (String, Vec<String>)>,
    consts: HashMap<String, String>,
    domains: HashMap<String, Vec<String>>,
    facts: Vec<Atom>,
    rules: Vec<Rule>,
    queries: Vec<Atom>,
    constraints: Vec<Vec<Literal>>,
    abduce_goals: Vec<Atom>,
    abducibles: Vec<String>,
}

fn unsupported(m: impl Into<String>) -> FaceError {
    FaceError::Unsupported(m.into())
}

impl Elaborator {
    /// A fresh elaborator with the built-in `Int` prelude installed (`Int`, the
    /// six comparisons, and `+`/`-`/`*` — all `open`). These are FACE-internal
    /// symbols (`#`-prefixed); the kernel treats them as uninterpreted (it
    /// type-checks them); their *arithmetic* meaning is evaluated by
    /// [`crate::solve`] during grounding (the ground theory atom is the `θ`).
    fn new() -> Result<Self, FaceError> {
        let mut env = Env::new();
        postulate(&mut env, INT, Term::type_(0))?;
        let int = || Term::cnst(INT);
        let i_i_prop = || Term::arrow(int(), Term::arrow(int(), Term::prop()));
        let i_i_i = || Term::arrow(int(), Term::arrow(int(), int()));
        for op in CMPS {
            postulate(&mut env, cmp_sym(op), i_i_prop())?;
        }
        for a in ARITH {
            postulate(&mut env, a, i_i_i())?;
        }
        // a `false` for the integrity-constraint carrier `∀X⃗. B → #false`.
        postulate(&mut env, FALSE, Term::prop())?;
        // the negation-as-failure wrapper for `not p` body literals (L2).
        postulate(&mut env, NOT, Term::arrow(Term::prop(), Term::prop()))?;
        Ok(Elaborator {
            env,
            preds: HashMap::new(),
            ctor_sig: HashMap::new(),
            consts: HashMap::new(),
            domains: HashMap::from([(INT.to_string(), Vec::new())]),
            facts: Vec::new(),
            rules: Vec::new(),
            queries: Vec::new(),
            constraints: Vec::new(),
            abduce_goals: Vec::new(),
            abducibles: Vec::new(),
        })
    }

    fn item(&mut self, item: &Item) -> Result<(), FaceError> {
        match item {
            Item::Sort(name) => self.declare_sort(name),
            Item::Enum(e) => self.declare_enum(&e.name, &e.ctors),
            Item::Data(d) => self.declare_data(&d.name, &d.ctors),
            Item::Pred(p) => self.declare_pred(&p.name, &p.arg_sorts),
            Item::Fact(a) => {
                self.check_ground_atom(a)?;
                self.facts.push(a.clone());
                Ok(())
            }
            Item::Query(a) => {
                self.check_query_atom(a)?;
                self.queries.push(a.clone());
                Ok(())
            }
            Item::Rule(r) => {
                self.check_rule(r)?;
                self.rules.push(r.clone());
                Ok(())
            }
            Item::Abducible(p) => {
                // an abducible is a predicate (usable in rule bodies / facts)
                // whose ground atoms are the hypothesis space.
                self.declare_pred(&p.name, &p.arg_sorts)?;
                self.abducibles.push(p.name.clone());
                Ok(())
            }
            Item::Abduce(a) => {
                // an abductive goal may be ground (`?- abduce p(c)`) or carry
                // variables (`?- abduce p(X)`) — sort-check like a query; the
                // solver enumerates the goal variables and abduces per instance.
                self.check_query_atom(a)?;
                self.abduce_goals.push(a.clone());
                Ok(())
            }
            Item::Constraint(body) => {
                self.check_constraint(body)?;
                self.constraints.push(body.clone());
                Ok(())
            }
        }
    }

    fn declare_sort(&mut self, name: &str) -> Result<(), FaceError> {
        if self.env.lookup(name).is_some() {
            return Err(unsupported(format!("`{name}` is already declared")));
        }
        postulate(&mut self.env, name, Term::type_(0))?;
        self.domains.entry(name.to_string()).or_default();
        Ok(())
    }

    fn declare_enum(&mut self, name: &str, ctors: &[String]) -> Result<(), FaceError> {
        if self.env.lookup(name).is_some() {
            return Err(unsupported(format!("`{name}` is already declared")));
        }
        if ctors.is_empty() {
            return Err(unsupported(format!("enum `{name}` has no constructors")));
        }
        let specs: Vec<(String, Vec<Term>, Vec<Term>)> =
            ctors.iter().map(|c| (c.clone(), Vec::new(), Vec::new())).collect();
        declare_inductive_indexed(&mut self.env, name, vec![], vec![], Univ::Type(0), specs)?;
        let domain = self.domains.entry(name.to_string()).or_default();
        for c in ctors {
            self.ctor_sig.insert(c.clone(), (name.to_string(), Vec::new()));
            domain.push(c.clone());
        }
        Ok(())
    }

    /// `data N = c0(S, …) | …` → a kernel inductive with argument-bearing
    /// constructors (the kernel's strict-positivity gate re-checks). Each
    /// constructor field sort must be a previously declared sort/enum/datatype
    /// or `Int`. The domain is *not* seeded — datatype domain elements are the
    /// ground constructor terms that appear (closed under subterm).
    fn declare_data(&mut self, name: &str, ctors: &[Ctor]) -> Result<(), FaceError> {
        if self.env.lookup(name).is_some() {
            return Err(unsupported(format!("`{name}` is already declared")));
        }
        if ctors.is_empty() {
            return Err(unsupported(format!("datatype `{name}` has no constructors")));
        }
        // field sorts may reference `name` itself (recursive) — `cnst(name)`
        // resolves as the type being declared; the kernel checks positivity.
        let mut specs = Vec::with_capacity(ctors.len());
        for c in ctors {
            for s in &c.arg_sorts {
                if s != name && !self.is_sort(s) {
                    return Err(unsupported(format!(
                        "datatype `{name}` constructor `{}` field sort `{s}` is undeclared",
                        c.name
                    )));
                }
            }
            let fields: Vec<Term> = c.arg_sorts.iter().map(|s| Term::cnst(s.clone())).collect();
            specs.push((c.name.clone(), fields, Vec::new()));
        }
        declare_inductive_indexed(&mut self.env, name, vec![], vec![], Univ::Type(0), specs)?;
        self.domains.entry(name.to_string()).or_default();
        for c in ctors {
            self.ctor_sig.insert(c.name.clone(), (name.to_string(), c.arg_sorts.clone()));
        }
        Ok(())
    }

    fn declare_pred(&mut self, name: &str, arg_sorts: &[String]) -> Result<(), FaceError> {
        if self.preds.contains_key(name) || self.env.lookup(name).is_some() {
            return Err(unsupported(format!("`{name}` is already declared")));
        }
        for s in arg_sorts {
            if !self.is_sort(s) {
                return Err(unsupported(format!(
                    "predicate `{name}` argument sort `{s}` is not a declared sort/enum/Int"
                )));
            }
        }
        let mut ty = Term::prop();
        for s in arg_sorts.iter().rev() {
            ty = Term::arrow(Term::cnst(s.clone()), ty);
        }
        postulate(&mut self.env, name, ty)?;
        self.preds.insert(name.to_string(), arg_sorts.to_vec());
        Ok(())
    }

    fn is_sort(&self, name: &str) -> bool {
        matches!(
            self.env.lookup(name).map(|d| d.ty.kind()),
            Some(adsmt_ir::TermKind::Sort(Univ::Type(0)))
        )
    }

    fn arg_sorts_of(&self, atom: &Atom) -> Result<Vec<String>, FaceError> {
        let sorts = self
            .preds
            .get(&atom.pred)
            .ok_or_else(|| unsupported(format!("unknown predicate `{}`", atom.pred)))?;
        if sorts.len() != atom.args.len() {
            return Err(unsupported(format!(
                "predicate `{}` expects {} arguments, got {}",
                atom.pred,
                sorts.len(),
                atom.args.len()
            )));
        }
        Ok(sorts.clone())
    }

    /// A **ground** fact atom: every argument is a constant / integer literal;
    /// auto-declared at its use sort; the atom is `infer`'d + Prop-checked.
    fn check_ground_atom(&mut self, atom: &Atom) -> Result<(), FaceError> {
        let arg_sorts = self.arg_sorts_of(atom)?;
        let mut t = Term::cnst(atom.pred.clone());
        for (arg, sort) in atom.args.iter().zip(&arg_sorts) {
            t = Term::app(t, self.resolve_arg(arg, sort)?);
        }
        self.check_is_prop(&t, &atom.pred)
    }

    /// A query atom: variables (the "find all" outputs) are sort-checked;
    /// constants/literals resolve as usual.
    fn check_query_atom(&mut self, atom: &Atom) -> Result<(), FaceError> {
        let arg_sorts = self.arg_sorts_of(atom)?;
        let mut var_sort: Vec<(String, String)> = Vec::new();
        for (arg, sort) in atom.args.iter().zip(&arg_sorts) {
            match arg {
                AspTerm::Var(v) => bind_var(&mut var_sort, v, sort)?,
                _ => {
                    self.resolve_arg(arg, sort)?;
                }
            }
        }
        Ok(())
    }

    /// A **definite rule** with the L1 theory interior. Infer variable sorts
    /// over head + positive body atoms; check theory-atom variables are
    /// `Int`-sorted and **bound** by a positive atom (range restriction); check
    /// head-variable safety; auto-declare constants/literals; and kernel-check
    /// the closed Prop `∀X⃗. b₁ → … → bₙ → h` (theory atoms included).
    fn check_rule(&mut self, rule: &Rule) -> Result<(), FaceError> {
        // 1. variable sorts (descending into constructor patterns) + ground
        //    subterm auto-declaration, over head + positive atoms.
        let mut vars: Vec<(String, String)> = Vec::new();
        let pos_atoms = || std::iter::once(&rule.head).chain(rule.body.iter().filter_map(as_pos));
        for atom in pos_atoms() {
            let arg_sorts = self.arg_sorts_of(atom)?;
            for (arg, sort) in atom.args.iter().zip(&arg_sorts) {
                self.rule_arg(arg, sort, &mut vars)?;
            }
        }
        // 2. theory/comparison atoms: CanEq routes each `{ lhs op rhs }` by the
        //    (shared) operand sort — arithmetic on Int, term (dis)equality
        //    elsewhere; every variable must be bound by a positive atom.
        for th in rule.body.iter().filter_map(as_theory) {
            self.check_comparison(th, &vars)?;
        }
        // 2b. negation-as-failure atoms (L2): NAF-safe — every variable must be
        //     bound by a positive body atom (a `not p(X)` with `X` free would be
        //     a universal, not a closed-world negation) — and sort-consistent.
        for neg in rule.body.iter().filter_map(as_neg) {
            self.check_neg_atom(neg, &vars)?;
        }
        // 3. head-variable safety: every flat head variable must be
        //    **range-restricted** — bound by a positive body atom, or
        //    constrained by a constructor pattern (head or body) that the
        //    universe filter pins to an appearing term. A truly-unbound flat
        //    head variable is rejected (else grounding silently drops instances).
        for arg in &rule.head.args {
            if let AspTerm::Var(v) = arg {
                let in_body = rule.body.iter().filter_map(as_pos).any(|b| occurs_in(b, v));
                let in_pattern = occurs_in_pattern(&rule.head, v)
                    || rule.body.iter().filter_map(as_pos).any(|b| occurs_in_pattern(b, v));
                if !in_body && !in_pattern {
                    return Err(FaceError::Unsafe(format!(
                        "head variable `{v}` is not range-restricted in rule `{}`",
                        rule.head.pred
                    )));
                }
            }
        }
        // 4. kernel-check the Π-implication carrier.
        let prop = self.rule_prop(rule, &vars);
        let ty = infer(&self.env, &Ctx::new(), &prop)?;
        if !is_def_eq(&self.env, &ty, &Term::prop()) {
            return Err(unsupported(format!("rule `{}` did not check as a Prop", rule.head.pred)));
        }
        Ok(())
    }

    /// Check a **negation-as-failure** atom `not p(t…)`: the predicate must
    /// exist with matching arity, and every argument must be either a variable
    /// already bound by a positive body atom (NAF safety — a free variable under
    /// `not` would be a universal, unsound to ground) or a ground term (resolved
    /// + seeded). It binds *no new* variables.
    fn check_neg_atom(&mut self, atom: &Atom, vars: &[(String, String)]) -> Result<(), FaceError> {
        let arg_sorts = self.arg_sorts_of(atom)?;
        for (arg, sort) in atom.args.iter().zip(&arg_sorts) {
            self.check_neg_arg(arg, sort, vars)?;
        }
        Ok(())
    }

    fn check_neg_arg(
        &mut self,
        arg: &AspTerm,
        sort: &str,
        vars: &[(String, String)],
    ) -> Result<(), FaceError> {
        match arg {
            AspTerm::Var(v) => match vars.iter().find(|(n, _)| n == v) {
                Some((_, s)) if s == sort => Ok(()),
                Some((_, s)) => Err(unsupported(format!(
                    "negative-literal variable `{v}` has sort `{s}`, used where `{sort}` is expected"
                ))),
                None => Err(FaceError::Unsafe(format!(
                    "negative-literal variable `{v}` is not bound by a positive body atom"
                ))),
            },
            AspTerm::Const(_) | AspTerm::Int(_) => self.resolve_arg(arg, sort).map(|_| ()),
            AspTerm::App(ctor, args) if !has_var(arg) => {
                self.resolve_ctor_term(ctor, args, sort).map(|_| ())
            }
            AspTerm::App(ctor, args) => {
                // a pattern carrying variables: check sort/arity + recurse, but
                // bind nothing — its variables must already be positive-bound.
                let (res, fields) = self
                    .ctor_sig
                    .get(ctor)
                    .ok_or_else(|| unsupported(format!("unknown constructor `{ctor}`")))?
                    .clone();
                if res != sort {
                    return Err(unsupported(format!(
                        "constructor `{ctor}` builds `{res}`, used where `{sort}` is expected"
                    )));
                }
                if fields.len() != args.len() {
                    return Err(unsupported(format!(
                        "constructor `{ctor}` takes {} arguments, got {}",
                        fields.len(),
                        args.len()
                    )));
                }
                for (a, fs) in args.iter().zip(&fields) {
                    self.check_neg_arg(a, fs, vars)?;
                }
                Ok(())
            }
        }
    }

    /// **Classify** the program: assign each predicate a **stratum** by
    /// least-fixpoint over the rule set — a positive body atom keeps the head
    /// at-or-above its dependency, a `not q` pushes the head **strictly above**
    /// `q` — and detect a negative cycle. A predicate whose stratum would exceed
    /// the predicate count has a negative cycle, so the program is
    /// [`Stratification::NonStratified`] (routed to the L3 stable-model gate);
    /// otherwise the converged strata are returned as
    /// [`Stratification::Stratified`]. The `want > n` test is exact (see
    /// [`Stratification`]). (Integrity constraints are excluded — they are
    /// evaluated last, against the full model, so they impose no stratum.)
    fn compute_strata(&self) -> Stratification {
        let n = self.preds.len();
        let mut strata: HashMap<String, usize> = self.preds.keys().map(|p| (p.clone(), 0)).collect();
        loop {
            let mut changed = false;
            for rule in &self.rules {
                let mut want = strata.get(&rule.head.pred).copied().unwrap_or(0);
                for lit in &rule.body {
                    match lit {
                        Literal::Pos(a) => {
                            want = want.max(strata.get(&a.pred).copied().unwrap_or(0));
                        }
                        Literal::Neg(a) => {
                            want = want.max(strata.get(&a.pred).copied().unwrap_or(0) + 1);
                        }
                        Literal::Theory(_) => {}
                    }
                }
                if want > n {
                    // a stratum past the predicate count can only come from a
                    // negative cycle (each `not` adds ≥1; a stratified program
                    // tops out below `n`) — route to L3 rather than refuse.
                    return Stratification::NonStratified(format!(
                        "predicate `{}` depends on its own negation (a negative cycle)",
                        rule.head.pred
                    ));
                }
                if want > strata[&rule.head.pred] {
                    strata.insert(rule.head.pred.clone(), want);
                    changed = true;
                }
            }
            if !changed {
                return Stratification::Stratified(strata);
            }
        }
    }

    /// Process a rule argument at expected sort `sort`: bind a variable's sort,
    /// resolve a ground constant/literal, or descend into a constructor —
    /// **binding the variables inside a pattern** (`node(L, R)` binds `L`, `R` at
    /// the field sorts) while auto-declaring the ground parts. A ground
    /// constructor term is recorded whole in the universe; a pattern (with
    /// variables) is matched at grounding.
    fn rule_arg(
        &mut self,
        arg: &AspTerm,
        sort: &str,
        vars: &mut Vec<(String, String)>,
    ) -> Result<(), FaceError> {
        match arg {
            AspTerm::Var(v) => bind_var(vars, v, sort),
            AspTerm::Const(_) | AspTerm::Int(_) => self.resolve_arg(arg, sort).map(|_| ()),
            AspTerm::App(ctor, args) if !has_var(arg) => {
                self.resolve_ctor_term(ctor, args, sort).map(|_| ())
            }
            AspTerm::App(ctor, args) => {
                let (res, fields) = self
                    .ctor_sig
                    .get(ctor)
                    .ok_or_else(|| unsupported(format!("unknown constructor `{ctor}`")))?
                    .clone();
                if res != sort {
                    return Err(unsupported(format!(
                        "constructor `{ctor}` builds `{res}`, used where `{sort}` is expected"
                    )));
                }
                if fields.len() != args.len() {
                    return Err(unsupported(format!(
                        "constructor `{ctor}` takes {} arguments, got {}",
                        fields.len(),
                        args.len()
                    )));
                }
                for (a, fs) in args.iter().zip(&fields) {
                    self.rule_arg(a, fs, vars)?;
                }
                Ok(())
            }
        }
    }

    /// Check a comparison `{ lhs op rhs }` via **CanEq**: infer the sort of each
    /// operand, require they agree (the cross-sort `Int = Node` mistake is
    /// rejected *here*), and check the operator against that shared sort — all
    /// six on `Int`, only `=`/`!=` on any other sort (an enum/datatype carries
    /// equality, not an ordering). For a non-`Int` sort, the structural
    /// (dis)equality symbol is postulated so the rule's Π-carrier type-checks.
    fn check_comparison(&mut self, th: &Theory, vars: &[(String, String)]) -> Result<(), FaceError> {
        let ls = self.check_operand(&th.lhs, vars)?;
        let rs = self.check_operand(&th.rhs, vars)?;
        if ls != rs {
            return Err(unsupported(format!(
                "comparison operands have different sorts `{ls}` and `{rs}` (CanEq requires equal sorts)"
            )));
        }
        if ls == INT {
            return Ok(()); // all six comparisons are defined on Int.
        }
        match th.op {
            CmpOp::Eq | CmpOp::Ne => self.ensure_eq_sym(&ls),
            _ => Err(unsupported(format!(
                "ordering `{}` is not defined on sort `{ls}` (only `=`/`!=`)",
                op_str(th.op)
            ))),
        }
    }

    /// Infer a comparison operand's sort, **declaring/seeding** its ground parts
    /// (int literals into the `Int` domain; nullary ctors and ground ctor terms
    /// into their sort's subterm-closed domain) and enforcing range restriction
    /// (every variable must already be bound by a positive body atom).
    /// Arithmetic (`+`/`-`/`*`) demands `Int` operands.
    fn check_operand(&mut self, e: &Expr, vars: &[(String, String)]) -> Result<String, FaceError> {
        match e {
            Expr::Lit(n) => {
                self.declare_int_lit(*n);
                Ok(INT.to_string())
            }
            Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) => {
                let sa = self.check_operand(a, vars)?;
                let sb = self.check_operand(b, vars)?;
                if sa != INT || sb != INT {
                    return Err(unsupported(format!(
                        "arithmetic `+`/`-`/`*` requires `Int` operands, got `{sa}` and `{sb}`"
                    )));
                }
                Ok(INT.to_string())
            }
            Expr::Var(v) => match vars.iter().find(|(n, _)| n == v) {
                Some((_, s)) => Ok(s.clone()),
                None => Err(FaceError::Unsafe(format!(
                    "comparison variable `{v}` is not bound by a positive body atom"
                ))),
            },
            Expr::Const(c) => {
                if let Some((sort, fields)) = self.ctor_sig.get(c).cloned() {
                    if !fields.is_empty() {
                        return Err(unsupported(format!(
                            "constructor `{c}` takes {} arguments but is used nullary",
                            fields.len()
                        )));
                    }
                    let dom = self.domains.entry(sort.clone()).or_default();
                    if !dom.contains(c) {
                        dom.push(c.clone());
                    }
                    Ok(sort)
                } else if let Some(sort) = self.consts.get(c) {
                    Ok(sort.clone())
                } else {
                    Err(unsupported(format!(
                        "constant `{c}` in a comparison has no known sort (use it in a typed atom first)"
                    )))
                }
            }
            Expr::App(c, args) => {
                let (sort, fields) = self
                    .ctor_sig
                    .get(c)
                    .cloned()
                    .ok_or_else(|| unsupported(format!("unknown constructor `{c}` in a comparison")))?;
                if fields.len() != args.len() {
                    return Err(unsupported(format!(
                        "constructor `{c}` takes {} arguments, got {}",
                        fields.len(),
                        args.len()
                    )));
                }
                for (a, fs) in args.iter().zip(&fields) {
                    // arithmetic inside a constructor-term operand would force the
                    // structural (render-equality) path to evaluate an un-reduced
                    // `1+1`, so it is refused in this slice (write the literal).
                    if matches!(a, Expr::Add(..) | Expr::Sub(..) | Expr::Mul(..)) {
                        return Err(unsupported(format!(
                            "arithmetic is not supported inside a constructor-term comparison operand (`{c}` argument)"
                        )));
                    }
                    let asort = self.check_operand(a, vars)?;
                    if &asort != fs {
                        return Err(unsupported(format!(
                            "constructor `{c}` field expects sort `{fs}`, got `{asort}`"
                        )));
                    }
                }
                // seed a *ground* ctor term (subterm-closed: the field terms are
                // seeded by the recursion above) into its sort's domain.
                if !expr_has_var(e) {
                    let rendered = render_expr(e);
                    let dom = self.domains.entry(sort.clone()).or_default();
                    if !dom.contains(&rendered) {
                        dom.push(rendered);
                    }
                }
                Ok(sort)
            }
        }
    }

    /// Postulate (idempotently) the `open` structural equality / disequality
    /// symbols `#eq.S` / `#ne.S : S → S → Prop` for a non-`Int` sort `S` — the
    /// kernel type-checks them; [`crate::solve`] evaluates them structurally on
    /// ground terms (canonical-rendering equality = EUF on the finite universe).
    fn ensure_eq_sym(&mut self, sort: &str) -> Result<(), FaceError> {
        for sym in [eq_sym_name(sort), ne_sym_name(sort)] {
            if self.env.lookup(&sym).is_none() {
                let ty = Term::arrow(Term::cnst(sort), Term::arrow(Term::cnst(sort), Term::prop()));
                postulate(&mut self.env, &sym, ty)?;
            }
        }
        Ok(())
    }

    /// Build the closed kernel term `∀X⃗. b₁ → … → bₙ → h`, with positive atoms
    /// and theory atoms both as body arrows.
    fn rule_prop(&self, rule: &Rule, vars: &[(String, String)]) -> Term {
        let head = self.atom_term(&rule.head, vars, vars.len());
        self.body_pi(&rule.body, head, vars)
    }

    /// Build `∀X⃗. b₁ → … → bₙ → conclusion` (the body folds under the arrow,
    /// the variables wrap as Π-binders). `conclusion` is already built in the
    /// `k`-binder context.
    fn body_pi(&self, body: &[Literal], conclusion: Term, vars: &[(String, String)]) -> Term {
        let k = vars.len();
        let mut inner = conclusion;
        for lit in body.iter().rev() {
            let l = match lit {
                Literal::Pos(a) => self.atom_term(a, vars, k),
                Literal::Neg(a) => Term::app(Term::cnst(NOT), self.atom_term(a, vars, k)),
                Literal::Theory(t) => self.theory_term(t, vars, k),
            };
            inner = Term::arrow(l, inner);
        }
        for (_, sort) in vars.iter().rev() {
            inner = Term::pi(Term::cnst(sort.clone()), inner);
        }
        inner
    }

    /// An **integrity constraint** `:- B`: validate the body (variable sorts via
    /// patterns, theory-atom binding, constant auto-declaration) and kernel-check
    /// the closed `Prop` `∀X⃗. b₁ → … → bₙ → #false` (the negative carrier).
    fn check_constraint(&mut self, body: &[Literal]) -> Result<(), FaceError> {
        let mut vars: Vec<(String, String)> = Vec::new();
        for atom in body.iter().filter_map(as_pos) {
            let arg_sorts = self.arg_sorts_of(atom)?;
            for (arg, sort) in atom.args.iter().zip(&arg_sorts) {
                self.rule_arg(arg, sort, &mut vars)?;
            }
        }
        for th in body.iter().filter_map(as_theory) {
            self.check_comparison(th, &vars)?;
        }
        for neg in body.iter().filter_map(as_neg) {
            self.check_neg_atom(neg, &vars)?;
        }
        let prop = self.body_pi(body, Term::cnst(FALSE), &vars);
        let ty = infer(&self.env, &Ctx::new(), &prop)?;
        if !is_def_eq(&self.env, &ty, &Term::prop()) {
            return Err(unsupported("integrity constraint did not check as a Prop"));
        }
        Ok(())
    }

    fn atom_term(&self, atom: &Atom, vars: &[(String, String)], k: usize) -> Term {
        let mut t = Term::cnst(atom.pred.clone());
        for arg in &atom.args {
            t = Term::app(t, self.arg_term(arg, vars, k));
        }
        t
    }

    /// The kernel term of a comparison: the operator symbol — an `Int`
    /// comparison `#int.*`, or the operand sort's structural equality
    /// `#eq.S`/`#ne.S` — applied to the two operand terms.
    fn theory_term(&self, th: &Theory, vars: &[(String, String)], k: usize) -> Term {
        let lhs = self.expr_term(&th.lhs, vars, k);
        let rhs = self.expr_term(&th.rhs, vars, k);
        let sort = self.operand_sort(&th.lhs, vars);
        let sym = if sort == INT {
            cmp_sym(th.op).to_string()
        } else if th.op == CmpOp::Ne {
            ne_sym_name(&sort)
        } else {
            eq_sym_name(&sort)
        };
        Term::apps(Term::cnst(sym), [lhs, rhs])
    }

    fn expr_term(&self, e: &Expr, vars: &[(String, String)], k: usize) -> Term {
        match e {
            Expr::Lit(n) => Term::cnst(n.to_string()),
            Expr::Const(c) => Term::cnst(c.clone()),
            Expr::Var(v) => {
                let p = vars.iter().position(|(n, _)| n == v).expect("bound comparison var");
                Term::bound(k - 1 - p)
            }
            Expr::App(c, args) => {
                let mut t = Term::cnst(c.clone());
                for a in args {
                    t = Term::app(t, self.expr_term(a, vars, k));
                }
                t
            }
            Expr::Add(a, b) => self.arith(ARITH[0], a, b, vars, k),
            Expr::Sub(a, b) => self.arith(ARITH[1], a, b, vars, k),
            Expr::Mul(a, b) => self.arith(ARITH[2], a, b, vars, k),
        }
    }

    fn arith(&self, sym: &str, a: &Expr, b: &Expr, vars: &[(String, String)], k: usize) -> Term {
        Term::apps(Term::cnst(sym), [self.expr_term(a, vars, k), self.expr_term(b, vars, k)])
    }

    /// The (already-validated) sort of a comparison operand — a pure lookup
    /// mirroring [`Self::check_operand`], used to pick the operator symbol.
    fn operand_sort(&self, e: &Expr, vars: &[(String, String)]) -> String {
        match e {
            Expr::Lit(_) | Expr::Add(..) | Expr::Sub(..) | Expr::Mul(..) => INT.to_string(),
            Expr::Var(v) => vars
                .iter()
                .find(|(n, _)| n == v)
                .map(|(_, s)| s.clone())
                .unwrap_or_else(|| INT.to_string()),
            Expr::Const(c) | Expr::App(c, _) => self
                .ctor_sig
                .get(c)
                .map(|(s, _)| s.clone())
                .or_else(|| self.consts.get(c).cloned())
                .unwrap_or_else(|| INT.to_string()),
        }
    }

    fn arg_term(&self, arg: &AspTerm, vars: &[(String, String)], k: usize) -> Term {
        match arg {
            AspTerm::Var(v) => {
                let p = vars.iter().position(|(n, _)| n == v).expect("bound var");
                Term::bound(k - 1 - p)
            }
            AspTerm::Const(c) => Term::cnst(c.clone()),
            AspTerm::Int(n) => Term::cnst(n.to_string()),
            AspTerm::App(ctor, args) => {
                let mut t = Term::cnst(ctor.clone());
                for a in args {
                    t = Term::app(t, self.arg_term(a, vars, k));
                }
                t
            }
        }
    }

    /// Resolve a ground argument (constant or integer literal) at expected sort
    /// `sort`, auto-declaring + sort-checking it (and recording it in the
    /// sort's domain). Rejects a variable.
    fn resolve_arg(&mut self, arg: &AspTerm, sort: &str) -> Result<Term, FaceError> {
        match arg {
            AspTerm::Var(v) => Err(FaceError::Unsafe(format!("variable `{v}` in a ground position"))),
            AspTerm::Const(c) => self.resolve_const(c, sort),
            AspTerm::Int(n) => {
                if sort != INT {
                    return Err(unsupported(format!(
                        "integer literal `{n}` used where sort `{sort}` is expected"
                    )));
                }
                self.declare_int_lit(*n);
                Ok(Term::cnst(n.to_string()))
            }
            AspTerm::App(ctor, args) => self.resolve_ctor_term(ctor, args, sort),
        }
    }

    /// Resolve a **ground** constructor term `c(t…)` at expected sort `sort`:
    /// check the constructor's result sort + arity, resolve each argument at its
    /// field sort (closing the domain under subterm), and record the whole term
    /// (rendered canonically) in the sort's domain. Builds the kernel
    /// constructor application.
    fn resolve_ctor_term(&mut self, ctor: &str, args: &[AspTerm], sort: &str) -> Result<Term, FaceError> {
        let (res, fields) = self
            .ctor_sig
            .get(ctor)
            .ok_or_else(|| unsupported(format!("unknown constructor `{ctor}`")))?
            .clone();
        if res != sort {
            return Err(unsupported(format!(
                "constructor `{ctor}` builds `{res}`, used where `{sort}` is expected"
            )));
        }
        if fields.len() != args.len() {
            return Err(unsupported(format!(
                "constructor `{ctor}` takes {} arguments, got {}",
                fields.len(),
                args.len()
            )));
        }
        let mut t = Term::cnst(ctor.to_string());
        for (arg, field_sort) in args.iter().zip(&fields) {
            t = Term::app(t, self.resolve_arg(arg, field_sort)?);
        }
        let rendered = render(&AspTerm::App(ctor.to_string(), args.to_vec()));
        let dom = self.domains.entry(sort.to_string()).or_default();
        if !dom.contains(&rendered) {
            dom.push(rendered);
        }
        Ok(t)
    }

    fn resolve_const(&mut self, name: &str, sort: &str) -> Result<Term, FaceError> {
        if let Some((ctor_sort, arg_sorts)) = self.ctor_sig.get(name) {
            if !arg_sorts.is_empty() {
                return Err(unsupported(format!(
                    "constructor `{name}` takes {} arguments but is used nullary",
                    arg_sorts.len()
                )));
            }
            if ctor_sort != sort {
                return Err(unsupported(format!(
                    "constructor `{name}` has sort `{ctor_sort}`, used where `{sort}` is expected"
                )));
            }
            // a nullary constructor is a domain element of its sort.
            let dom = self.domains.entry(sort.to_string()).or_default();
            if !dom.contains(&name.to_string()) {
                dom.push(name.to_string());
            }
            return Ok(Term::cnst(name.to_string()));
        }
        match self.consts.get(name) {
            Some(prev) if prev != sort => Err(unsupported(format!(
                "constant `{name}` used at sort `{sort}` but already at `{prev}`"
            ))),
            Some(_) => Ok(Term::cnst(name.to_string())),
            None => {
                postulate(&mut self.env, name, Term::cnst(sort.to_string()))?;
                self.consts.insert(name.to_string(), sort.to_string());
                self.domains.entry(sort.to_string()).or_default().push(name.to_string());
                Ok(Term::cnst(name.to_string()))
            }
        }
    }

    /// Auto-declare an integer literal as an `Int` constant (named by its
    /// decimal form) and add it to the `Int` domain (idempotent).
    fn declare_int_lit(&mut self, n: i64) {
        let name = n.to_string();
        if self.env.lookup(&name).is_none() {
            // an `open` Int constant; safe (postulate of a fresh name).
            let _ = postulate(&mut self.env, &name, Term::cnst(INT));
            let dom = self.domains.entry(INT.to_string()).or_default();
            if !dom.contains(&name) {
                dom.push(name);
            }
        }
    }

    fn check_is_prop(&self, t: &Term, what: &str) -> Result<(), FaceError> {
        let ty = infer(&self.env, &Ctx::new(), t)?;
        if !is_def_eq(&self.env, &ty, &Term::prop()) {
            return Err(unsupported(format!("atom `{what}` has sort `{ty}`, expected a Prop")));
        }
        Ok(())
    }
}

fn as_pos(l: &Literal) -> Option<&Atom> {
    match l {
        Literal::Pos(a) => Some(a),
        Literal::Neg(_) | Literal::Theory(_) => None,
    }
}

fn as_theory(l: &Literal) -> Option<&Theory> {
    match l {
        Literal::Theory(t) => Some(t),
        Literal::Pos(_) | Literal::Neg(_) => None,
    }
}

fn as_neg(l: &Literal) -> Option<&Atom> {
    match l {
        Literal::Neg(a) => Some(a),
        Literal::Pos(_) | Literal::Theory(_) => None,
    }
}

fn bind_var(vars: &mut Vec<(String, String)>, v: &str, sort: &str) -> Result<(), FaceError> {
    match vars.iter().find(|(n, _)| n == v) {
        Some((_, prev)) if prev != sort => Err(unsupported(format!(
            "variable `{v}` used at sort `{sort}` but already at `{prev}`"
        ))),
        Some(_) => Ok(()),
        None => {
            vars.push((v.to_string(), sort.to_string()));
            Ok(())
        }
    }
}

/// Whether a term mentions any variable (including inside a constructor).
pub(crate) fn has_var(t: &AspTerm) -> bool {
    match t {
        AspTerm::Var(_) => true,
        AspTerm::App(_, args) => args.iter().any(has_var),
        _ => false,
    }
}

/// Whether a comparison operand mentions any variable.
fn expr_has_var(e: &Expr) -> bool {
    match e {
        Expr::Var(_) => true,
        Expr::Lit(_) | Expr::Const(_) => false,
        Expr::App(_, args) => args.iter().any(expr_has_var),
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) => expr_has_var(a) || expr_has_var(b),
    }
}

/// The canonical rendering of a **ground** comparison operand — the key under
/// which the grounder's domain stores a ctor term (matches [`render`] on the
/// equivalent [`AspTerm`]).
fn render_expr(e: &Expr) -> String {
    match e {
        Expr::Lit(n) => n.to_string(),
        Expr::Const(c) => c.clone(),
        Expr::Var(v) => v.clone(),
        Expr::App(c, args) => {
            let inner: Vec<String> = args.iter().map(render_expr).collect();
            format!("{c}({})", inner.join(","))
        }
        Expr::Add(a, b) => format!("{}+{}", render_expr(a), render_expr(b)),
        Expr::Sub(a, b) => format!("{}-{}", render_expr(a), render_expr(b)),
        Expr::Mul(a, b) => format!("{}*{}", render_expr(a), render_expr(b)),
    }
}

fn occurs_in(a: &Atom, v: &str) -> bool {
    a.args.iter().any(occurs_in_term(v))
}

/// Whether `v` occurs *inside a constructor pattern* of `a` (so the universe
/// filter range-restricts it).
fn occurs_in_pattern(a: &Atom, v: &str) -> bool {
    a.args.iter().any(|arg| matches!(arg, AspTerm::App(..)) && occurs_in_term(v)(arg))
}

fn occurs_in_term(v: &str) -> impl Fn(&AspTerm) -> bool + '_ {
    move |t| match t {
        AspTerm::Var(n) => n == v,
        AspTerm::App(_, args) => args.iter().any(occurs_in_term(v)),
        _ => false,
    }
}

/// The canonical decimal/structural rendering of a **ground** term — the key
/// under which the grounder interns it (and the domain stores it). A nullary
/// constructor / object constant renders to its name, an integer to its decimal
/// form, and `c(t…)` to `c(r(t),…)`.
pub(crate) fn render(t: &AspTerm) -> String {
    match t {
        AspTerm::Var(v) => v.clone(),
        AspTerm::Const(c) => c.clone(),
        AspTerm::Int(n) => n.to_string(),
        AspTerm::App(c, args) => {
            let inner: Vec<String> = args.iter().map(render).collect();
            format!("{c}({})", inner.join(","))
        }
    }
}
