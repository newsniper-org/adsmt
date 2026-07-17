//! Shared delegation stack for a typed HOL sequent `H ⊢ G` (SMT query `H ∧ ¬G`).
//!
//! Lifted out of `lu-smt`'s `Driver` so `adsmt-lukb-driver` (and thus `adsmtc` /
//! `adsmtr`) reaches the SAME delegation both CLIs used to get only in `lu-smt`.
//! Two independent, feature-gated backends:
//!
//! * [`cas::try_discharge`] (feature `cas`) — classify the sequent into an
//!   algebraic obligation, dispatch it to the untrusted CAS backends, and return
//!   the admit-re-checked [`adsmt_cas::CasProof`] iff a witness proves `G` VALID.
//!   Every witness is re-checked with exact `BigRational` / `BigInt`, so a backend
//!   bug only ever yields `None` — never a wrong `Some`.
//! * [`oxiz::try_oxiz`] (feature `oxiz`) — [`render_smtlib`] the obligation to an
//!   SMT-LIB script and feed the vendored in-process OxiZ (z3-parity), returning
//!   its verdict. Trusts OxiZ exactly as `lu-smt`'s delegation does.
//!
//! ## Soundness of the renderer
//!
//! [`render_smtlib`] must be *semantically faithful*: OxiZ decides the rendered
//! script, and the caller trusts that verdict for the original obligation, so a
//! mis-render would be unsound. The expression rendering is the SAME logic
//! `lu-smt` uses for its re-parseable abductive `term` field (Var/Const names pass
//! through unchanged — they are already the SMT-LIB symbols), with the ONE
//! addition that quantifiers render as standard `(forall ((v S)) body)` instead of
//! the abductive path's quantifier-free `(forall (lambda …))`. Anything the
//! renderer cannot faithfully emit (a bare lambda, a polymorphic / higher-order
//! binder sort, datatypes) returns `None` — the sound fallback (no delegation),
//! never a guessed script.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use adsmt_core::{Term, TermInner, Type};
use adsmt_theory::datatypes::DatatypeDecl;

/// One quantifier's `:pattern` annotation for the renderer: the telescope
/// arity the binder re-collection must span, plus the trigger groups (each a
/// multi-pattern over the SAME bound `Var`s as the quantifier body). Produced
/// by `adsmt-ir-lower`'s trigger takeover (`Lowered::triggers`); the driver
/// converts and merges the hyps + goals maps.
#[derive(Debug, Clone)]
pub struct QuantPatterns {
    pub arity: usize,
    pub groups: Vec<Vec<Term>>,
}

/// Outermost lowered HOL `forall` term → its `:pattern` annotation. Advisory:
/// an entry the dead-pattern guard rejects renders plain (same as today).
pub type PatternMap = HashMap<Term, QuantPatterns>;

/// Render the obligation `H ∧ ¬G` to a self-contained SMT-LIB script
/// (`declare-sort` / `declare-datatypes` / `declare-const` / `declare-fun` for
/// the free symbols, then the asserted hypotheses + the negated goal +
/// `(check-sat)`), or `None` if any part cannot be faithfully rendered.
///
/// `datatypes` are the module's engine [`DatatypeDecl`]s, emitted as ONE
/// `(declare-datatypes …)` group (the multi-datatype form, so cross-references
/// work). Constructors/selectors appear in lowered terms as `Const` leaves, so
/// they render by name and are declared exactly once (here); the datatype SORT
/// names are excluded from the `declare-sort` set for the same reason. A
/// PARAMETRIC decl bails sound (`None`) — the lowering never produces one today.
///
/// SOUNDNESS of the datatype emission: the caller trusts only OxiZ's `unsat`
/// ([`oxiz::proves_goal`]). If OxiZ interprets the declared datatype only
/// partially (e.g. constructors as plain uninterpreted functions), it solves an
/// OVER-approximation — a superset of models — so its `unsat` still implies the
/// real `unsat` (dropping datatype axioms can only ADD models). The `sat`
/// direction over such an abstraction is exactly why `sat` is never trusted.
/// z3-differential-gated per the unsat-trust rule.
#[must_use]
pub fn render_smtlib(
    hyps: &[Term],
    goal: &Term,
    datatypes: &[DatatypeDecl],
    patterns: &PatternMap,
) -> Option<String> {
    render_smtlib_shaped(hyps, goal, datatypes, patterns, true)
}

/// [`render_smtlib`] with the quantifier SHAPE under caller control:
/// `recollect = false` renders every quantifier 1:1 CURRIED (one binder per
/// level, the pre-`:pattern` output, byte-identical to the historical
/// renderer) and is only meaningful with an empty/ignored `patterns` map —
/// it is the completeness-floor fallback shape ([`oxiz::proves_goal`]).
#[must_use]
pub(crate) fn render_smtlib_shaped(
    hyps: &[Term],
    goal: &Term,
    datatypes: &[DatatypeDecl],
    patterns: &PatternMap,
    recollect: bool,
) -> Option<String> {
    if datatypes.iter().any(|d| !d.params.is_empty()) {
        return None; // parametric datatypes: no faithful monomorphic render.
    }
    let cx = RenderCx {
        patterns,
        // A/B triage kill-switch (the 209-row gate's control arm): suppress
        // ALL `:pattern` emission without a rebuild. Binder RE-collection is
        // kept, so the script shape matches the annotated run minus the
        // annotations — isolating the patterns' own effect.
        disabled: std::env::var_os("ADSMT_DELEGATE_NO_PATTERNS").is_some(),
        recollect,
        plans: RefCell::new(HashMap::new()),
    };
    let bound = HashSet::new();
    let mut sorts: BTreeSet<String> = BTreeSet::new();
    let mut consts: BTreeMap<String, Type> = BTreeMap::new();
    for h in hyps {
        collect_decls(h, &bound, &mut sorts, &mut consts, &cx)?;
    }
    collect_decls(goal, &bound, &mut sorts, &mut consts, &cx)?;
    // Datatype sorts are declared by `declare-datatypes`, not `declare-sort`.
    let dt_sorts: BTreeSet<&str> = datatypes.iter().map(|d| d.sort_name.as_str()).collect();
    sorts.retain(|s| !dt_sorts.contains(s.as_str()));

    let mut out = String::new();
    // Choose the TIGHTEST sound logic. OxiZ's sound nonlinear dispatch
    // (`dispatch_nl_solver`) only engages when the logic string contains `NIA` /
    // `NRA`; under `ALL` a nonlinear atom falls onto the opaque CDCL(T) path (sound
    // only for `unsat` — a `sat` there is downgraded to `unknown`). So for a
    // quantifier-free nonlinear obligation we emit `QF_NIA` (pure integer) or
    // `QF_NRA` (any real — a real-relaxation `unsat` is a sound `unsat` for the
    // integer restriction too), which lets OxiZ actually PROVE the goal (e.g.
    // `x*x = 3` → `unsat`) instead of abstaining. Everything else (linear,
    // quantified, EUF) stays `ALL` — native already decides the linear/quantified
    // fragment, and a quantifier under a `QF_*` logic would be mis-routed.
    let mut th = TheoryFlags::default();
    for h in hyps {
        analyze(h, &mut th);
    }
    analyze(goal, &mut th);
    // A datatype-bearing obligation stays on `ALL` (the QF_NIA/QF_NRA fast
    // paths have no datatype dispatch; `ALL` routes through the full solver).
    if !datatypes.is_empty() {
        th.quant = true;
    }
    out.push_str(&format!("(set-logic {})\n", th.logic()));
    // Uninterpreted sorts (Int / Real / Bool are built in and never collected).
    for s in &sorts {
        out.push_str(&format!("(declare-sort {s} 0)\n"));
    }
    // All datatypes in ONE `declare-datatypes` group (cross-refs + the OxiZ
    // multi-datatype parse form). Selector names carry `!` — a legal SMT-LIB
    // simple-symbol character, no quoting needed.
    if !datatypes.is_empty() {
        let mut heads = String::new();
        let mut bodies = String::new();
        for d in datatypes {
            heads.push_str(&format!("({} 0) ", d.sort_name));
            bodies.push('(');
            for (j, cname) in d.constructors.iter().enumerate() {
                bodies.push('(');
                bodies.push_str(cname);
                for (i, fsort) in d.field_sorts.get(j)?.iter().enumerate() {
                    let sel = d.selectors.get(j)?.get(i)?;
                    bodies.push_str(&format!(" ({sel} {fsort})"));
                }
                bodies.push_str(") ");
            }
            bodies.push_str(") ");
        }
        out.push_str(&format!("(declare-datatypes ({heads}) ({bodies}))\n"));
    }
    for (name, ty) in &consts {
        let (args, ret) = decompose_fun_type(ty)?;
        if args.is_empty() {
            out.push_str(&format!("(declare-const {name} {ret})\n"));
        } else {
            out.push_str(&format!("(declare-fun {name} ({}) {ret})\n", args.join(" ")));
        }
    }
    for h in hyps {
        out.push_str(&format!("(assert {})\n", render_expr(h, &bound, &cx)?));
    }
    out.push_str(&format!("(assert (not {}))\n", render_expr(goal, &bound, &cx)?));
    out.push_str("(check-sat)\n");
    Some(out)
}

/// `(forall|exists, binder, body)` if `t` is a quantifier application, else `None`.
fn dest_quant(t: &Term) -> Option<(&'static str, adsmt_core::Var, Term)> {
    if let Some((v, body)) = t.dest_forall() {
        return Some(("forall", v, body));
    }
    if let Some((v, body)) = t.dest_exists() {
        return Some(("exists", v, body));
    }
    None
}

/// Per-render context: the caller's [`PatternMap`] plus a memo of the
/// per-quantifier annotation [`Plan`]s (computed once, consulted by both the
/// declaration pass and the expression pass so they can never disagree on
/// whether a quantifier's patterns are emitted).
struct RenderCx<'a> {
    patterns: &'a PatternMap,
    /// `ADSMT_DELEGATE_NO_PATTERNS` kill-switch: treat the map as empty.
    disabled: bool,
    /// `false` = render every quantifier 1:1 curried (the pre-`:pattern`
    /// historical shape — the completeness-floor fallback).
    recollect: bool,
    plans: RefCell<HashMap<Term, Option<Plan>>>,
}

/// A validated annotation for one map-keyed `forall`: exactly `arity` peeled
/// binders, the residual body, and the trigger groups that passed the
/// dead-pattern guard. Existence of a `Plan` == the patterns WILL be emitted.
#[derive(Clone)]
struct Plan {
    vars: Vec<adsmt_core::Var>,
    body: Term,
    groups: Vec<Vec<Term>>,
}

impl RenderCx<'_> {
    /// The annotation plan for `t`, or `None` (no map entry / any guard
    /// failure ⇒ render plain — the all-or-nothing per-quantifier firewall).
    fn plan(&self, t: &Term) -> Option<Plan> {
        if self.disabled || self.patterns.is_empty() {
            return None; // the common path: zero overhead, zero behavior change
        }
        if let Some(cached) = self.plans.borrow().get(t) {
            return cached.clone();
        }
        let plan = self.compute_plan(t);
        self.plans.borrow_mut().insert(t.clone(), plan.clone());
        plan
    }

    fn compute_plan(&self, t: &Term) -> Option<Plan> {
        let qp = self.patterns.get(t)?;
        if qp.arity == 0 || qp.groups.is_empty() {
            return None;
        }
        // peel EXACTLY `arity` forall binders (the annotation's scope).
        let mut vars = Vec::with_capacity(qp.arity);
        let mut body = t.clone();
        for _ in 0..qp.arity {
            let (v, b) = body.dest_forall()?;
            vars.push(v);
            body = b;
        }
        let binder_names: HashSet<&str> = vars.iter().map(|v| v.name.as_str()).collect();
        // the DEAD-PATTERN GUARD (all-or-nothing per quantifier):
        // (c)'s reference set — every Const name + FREE Var name reachable in
        // the body (a pattern whose head the lowering erased would never fire
        // = zero instantiations, strictly worse than trigger inference; this
        // gate is the sole defense). FREE occurrences only: a nested
        // quantifier's `x!N` binder name must never vouch for a pattern head
        // that colludes with lower's fresh scheme (the guard-(c) bypass).
        let body_syms = free_symbols(&body, &mut HashMap::new());
        for group in &qp.groups {
            let mut covered: HashSet<&str> = HashSet::new();
            for p in group {
                // (a) renderable: `render_expr`/`collect_decls` are total on
                // lambda-free terms, so lam-freeness == both passes succeed.
                if !lam_free(p) {
                    return None;
                }
                // (c) the head must be an uninterpreted function (not a
                // builtin, not a bare binder) that occurs in the body.
                let (head_t, n_args) = spine_head(p);
                let (head, head_ty) = match head_t.kind() {
                    TermInner::Var(v) => (v.name.as_str(), &v.ty),
                    TermInner::Const(c) => (c.name.as_str(), &c.ty),
                    TermInner::App(..) | TermInner::Lam(..) => return None,
                };
                if is_interpreted_head(head)
                    || binder_names.contains(head)
                    || !body_syms.contains(head)
                {
                    return None;
                }
                // …and the spine must SATURATE the head's declared arity (the
                // elab face already drops function-sorted patterns; this is
                // the defense-in-depth): an ill-arity `:pattern` parses
                // leniently but can never e-match — a dead trigger that
                // suppresses the solver's own inference.
                let (fun_args, _ret) = decompose_fun_type(head_ty)?;
                if n_args != fun_args.len() {
                    return None;
                }
                for n in pattern_var_names(p) {
                    if let Some(bn) = binder_names.get(n) {
                        covered.insert(*bn);
                    }
                }
            }
            // (b) each group must cover ALL binders (an uncovered variable
            // cannot be instantiated from a match on this group).
            if covered.len() != vars.len() {
                return None;
            }
        }
        Some(Plan { vars, body, groups: qp.groups.clone() })
    }
}

/// `t` contains no `Lam` (hence no quantifier) — the fragment on which both
/// `render_expr` and `collect_decls` are total.
fn lam_free(t: &Term) -> bool {
    match t.kind() {
        TermInner::Var(_) | TermInner::Const(_) => true,
        TermInner::App(f, x) => lam_free(f) && lam_free(x),
        TermInner::Lam(_, _) => false,
    }
}

/// The head of `t`'s application spine plus the spine length (argument count).
fn spine_head(t: &Term) -> (&Term, usize) {
    let mut head = t;
    let mut n = 0;
    while let TermInner::App(f, _) = head.kind() {
        head = f;
        n += 1;
    }
    (head, n)
}

/// SMT-LIB interpreted heads: a `:pattern` headed by one is rejected by
/// solvers (and matches nothing e-matchable).
fn is_interpreted_head(name: &str) -> bool {
    matches!(
        name,
        "=" | "not"
            | "and"
            | "or"
            | "=>"
            | "xor"
            | "ite"
            | "distinct"
            | "true"
            | "false"
            | "forall"
            | "exists"
            | "+"
            | "-"
            | "*"
            | "/"
            | "div"
            | "mod"
            | "abs"
            | "<"
            | "<="
            | ">"
            | ">="
            | "to_real"
            | "to_int"
            | "is_int"
    ) || name.parse::<i128>().is_ok()
        || name.parse::<f64>().is_ok()
}

/// Every `Var` name occurring in a (lambda-free) pattern term.
fn pattern_var_names(t: &Term) -> Vec<&str> {
    let mut out = Vec::new();
    let mut stack = vec![t];
    while let Some(cur) = stack.pop() {
        match cur.kind() {
            TermInner::Var(v) => out.push(v.name.as_str()),
            TermInner::Const(_) => {}
            TermInner::App(f, x) => {
                stack.push(f);
                stack.push(x);
            }
            TermInner::Lam(_, b) => stack.push(b),
        }
    }
    out
}

/// Every `Const` name plus every FREE `Var` name in `t` — the guard (c)
/// reference set. `Lam` binder names and their bound occurrences are EXCLUDED:
/// including them lets a nested quantifier's fresh `x!N` binder vouch for a
/// pattern head that never occurs ground (the guard-(c) bypass). Free-ness is
/// context-independent per subterm, so the bottom-up memo is exact and the
/// walk linear in the hash-consed DAG. Name-shadow conflation (a free `Var`
/// spelled like an enclosing binder) only ever REMOVES names — the guard then
/// fails closed (pattern renders plain), never open.
fn free_symbols(t: &Term, memo: &mut HashMap<Term, HashSet<String>>) -> HashSet<String> {
    if let Some(s) = memo.get(t) {
        return s.clone();
    }
    let out = match t.kind() {
        TermInner::Var(v) => HashSet::from([v.name.clone()]),
        TermInner::Const(c) => HashSet::from([c.name.clone()]),
        TermInner::App(f, x) => {
            let mut s = free_symbols(f, memo);
            s.extend(free_symbols(x, memo));
            s
        }
        TermInner::Lam(v, b) => {
            let mut s = free_symbols(b, memo);
            s.remove(&v.name);
            s
        }
    };
    memo.insert(t.clone(), out.clone());
    out
}

/// The SMT-LIB sort name of a *ground* sort (an uninterpreted sort or a builtin
/// like `Int` / `Real` / `Bool`). `None` for a polymorphic / applied / function
/// type — those are not first-order SMT-LIB sorts and must bail.
fn sort_name(ty: &Type) -> Option<String> {
    match ty {
        Type::Const(c) => Some(c.name.clone()),
        _ => None,
    }
}

/// Split `S1 -> S2 -> … -> R` into `([S1, S2, …], R)` (empty args ⇒ a constant of
/// sort `R`). `None` if any component is not a ground sort.
fn decompose_fun_type(ty: &Type) -> Option<(Vec<String>, String)> {
    let mut args = Vec::new();
    let mut cur = ty.clone();
    while let Some((dom, cod)) = cur.dest_fun() {
        args.push(sort_name(&dom)?);
        cur = cod;
    }
    Some((args, sort_name(&cur)?))
}

/// Add every uninterpreted sort constant reachable in `ty` to `sorts` (skips the
/// builtins `Int` / `Real` / `Bool` and the `->` type constructor).
fn collect_sorts_from_type(ty: &Type, sorts: &mut BTreeSet<String>) {
    match ty {
        Type::Const(c) => {
            if !matches!(c.name.as_str(), "Int" | "Real" | "Bool" | "->") {
                sorts.insert(c.name.clone());
            }
        }
        Type::App(f, a) => {
            collect_sorts_from_type(f, sorts);
            collect_sorts_from_type(a, sorts);
        }
        Type::Var(_) => {}
    }
}

/// Collect the free symbols to declare: each free `Var` leaf (declared symbols are
/// `Var`; literals / constructors are `Const`) with its type, plus the
/// uninterpreted sorts they reference. Bound variables (quantifier binders) are
/// NOT declared. Returns `None` on a construct that cannot be rendered.
fn collect_decls(
    t: &Term,
    bound: &HashSet<String>,
    sorts: &mut BTreeSet<String>,
    consts: &mut BTreeMap<String, Type>,
    cx: &RenderCx,
) -> Option<()> {
    if let Some((_kw, v, body)) = dest_quant(t) {
        // dead-pattern guard (d): the patterns this quantifier WILL emit are
        // declared too — one undeclared pattern-only symbol would kill
        // parsing of the whole script. Scoped under ALL the plan's binders.
        if let Some(plan) = cx.plan(t) {
            let mut inner = bound.clone();
            for pv in &plan.vars {
                inner.insert(pv.name.clone());
            }
            for g in &plan.groups {
                for p in g {
                    collect_decls(p, &inner, sorts, consts, cx)?;
                }
            }
        }
        collect_sorts_from_type(&v.ty, sorts);
        let mut inner = bound.clone();
        inner.insert(v.name.clone());
        return collect_decls(&body, &inner, sorts, consts, cx);
    }
    match t.kind() {
        TermInner::Var(v) => {
            if !bound.contains(&v.name) {
                consts.insert(v.name.clone(), v.ty.clone());
                collect_sorts_from_type(&v.ty, sorts);
            }
            Some(())
        }
        TermInner::Const(_) => Some(()),
        TermInner::App(f, x) => {
            collect_decls(f, bound, sorts, consts, cx)?;
            collect_decls(x, bound, sorts, consts, cx)
        }
        // A bare lambda outside a quantifier is not first-order SMT-LIB.
        TermInner::Lam(_, _) => None,
    }
}

/// Render a term as an SMT-LIB expression, or `None` if it cannot be faithfully
/// rendered. Mirrors `lu-smt`'s abductive `term_to_smtlib` for the quantifier-free
/// fragment. A quantifier RE-COLLECTS its curried same-kind binder chain into one
/// multi-binder form `(forall ((v1 S1) (v2 S2)) body)` — mandatory for pattern
/// emission (OxiZ attaches patterns per quantifier level, so annotating only the
/// innermost curried level would leave the outer variables unguided) and it helps
/// OxiZ's own trigger inference on trigger-free quantifiers. An annotated forall
/// (a [`Plan`]) collects EXACTLY its arity and emits `(! body :pattern …)`; the
/// plain collection stops BEFORE a nested annotated quantifier so each level
/// keeps its own annotation. With `RenderCx::recollect == false` (the
/// completeness-floor fallback shape) no chain is merged: every quantifier
/// prints 1:1 curried, byte-identical to the historical renderer.
fn render_expr(t: &Term, bound: &HashSet<String>, cx: &RenderCx) -> Option<String> {
    if let Some((kw, v, body)) = dest_quant(t) {
        if let Some(plan) = cx.plan(t) {
            let mut inner = bound.clone();
            let mut binders = Vec::with_capacity(plan.vars.len());
            for pv in &plan.vars {
                binders.push(format!("({} {})", pv.name, sort_name(&pv.ty)?));
                inner.insert(pv.name.clone());
            }
            let body_s = render_expr(&plan.body, &inner, cx)?;
            let mut pats = String::new();
            for g in &plan.groups {
                let rendered: Option<Vec<String>> =
                    g.iter().map(|p| render_expr(p, &inner, cx)).collect();
                pats.push_str(&format!(" :pattern ({})", rendered?.join(" ")));
            }
            return Some(format!("(forall ({}) (! {body_s}{pats}))", binders.join(" ")));
        }
        let mut vars = vec![v];
        let mut body = body;
        while cx.recollect && let Some((kw2, v2, b2)) = dest_quant(&body) {
            if kw2 != kw || cx.plan(&body).is_some() {
                break;
            }
            vars.push(v2);
            body = b2;
        }
        let mut inner = bound.clone();
        let mut binders = Vec::with_capacity(vars.len());
        for pv in &vars {
            binders.push(format!("({} {})", pv.name, sort_name(&pv.ty)?));
            inner.insert(pv.name.clone());
        }
        return Some(format!("({kw} ({}) {})", binders.join(" "), render_expr(&body, &inner, cx)?));
    }
    match t.kind() {
        TermInner::Var(v) => Some(v.name.clone()),
        TermInner::Const(c) => Some(c.name.clone()),
        TermInner::App(_, _) => {
            // Collect the application spine, left through `App` heads.
            let mut args: Vec<&Term> = Vec::new();
            let mut head = t;
            while let TermInner::App(f, x) = head.kind() {
                args.push(x);
                head = f;
            }
            args.reverse();
            let rendered: Option<Vec<String>> =
                args.iter().map(|a| render_expr(a, bound, cx)).collect();
            Some(format!("({} {})", render_expr(head, bound, cx)?, rendered?.join(" ")))
        }
        // A bare lambda (function value) has no SMT-LIB expression form.
        TermInner::Lam(_, _) => None,
    }
}

/// Which theories the obligation touches — drives the `(set-logic …)` choice.
#[derive(Default)]
struct TheoryFlags {
    /// A product of two non-numeral terms (`(* a b)` with a var on both sides).
    nonlinear: bool,
    /// Any `Real`-sorted symbol.
    real: bool,
    /// Any `forall` / `exists`.
    quant: bool,
}

impl TheoryFlags {
    /// The tightest sound SMT-LIB logic. Only route to `QF_NIA` / `QF_NRA` for a
    /// quantifier-free nonlinear obligation (so OxiZ's sound nonlinear dispatch
    /// engages); everything else stays `ALL`.
    fn logic(&self) -> &'static str {
        if self.nonlinear && !self.quant {
            if self.real { "QF_NRA" } else { "QF_NIA" }
        } else {
            "ALL"
        }
    }
}

/// Walk `t`, setting the [`TheoryFlags`] it touches.
fn analyze(t: &Term, f: &mut TheoryFlags) {
    if let Some((_kw, v, body)) = dest_quant(t) {
        f.quant = true;
        analyze_type(&v.ty, f);
        analyze(&body, f);
        return;
    }
    match t.kind() {
        TermInner::Var(v) => analyze_type(&v.ty, f),
        TermInner::Const(_) => {}
        TermInner::App(_, _) => {
            if let Some((a, b)) = dest_mul(t)
                && !is_numeral(&a)
                && !is_numeral(&b)
            {
                f.nonlinear = true;
            }
            let mut head = t;
            while let TermInner::App(g, x) = head.kind() {
                analyze(x, f);
                head = g;
            }
            analyze(head, f);
        }
        TermInner::Lam(v, body) => {
            analyze_type(&v.ty, f);
            analyze(body, f);
        }
    }
}

fn analyze_type(ty: &Type, f: &mut TheoryFlags) {
    if let Type::Const(c) = ty
        && c.name == "Real"
    {
        f.real = true;
    }
}

/// `(* a b)` = `App(App(Const("*"), a), b)` destructured to `(a, b)`.
fn dest_mul(t: &Term) -> Option<(Term, Term)> {
    if let TermInner::App(f, b) = t.kind()
        && let TermInner::App(g, a) = f.kind()
        && let TermInner::Const(c) = g.kind()
        && c.name == "*"
    {
        return Some((a.clone(), b.clone()));
    }
    None
}

/// A numeric literal (`Const` whose name parses as an integer or decimal).
fn is_numeral(t: &Term) -> bool {
    matches!(t.kind(), TermInner::Const(c) if c.name.parse::<i128>().is_ok() || c.name.parse::<f64>().is_ok())
}

#[cfg(feature = "cas")]
pub mod cas;

#[cfg(feature = "oxiz")]
pub mod oxiz;

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Term;

    fn int_ty() -> Type {
        Type::const_("Int", adsmt_core::Kind::Type)
    }
    fn int_var(n: &str) -> Term {
        Term::var(n, int_ty())
    }
    fn int_const_op(n: &str) -> Term {
        // an SMT-LIB op / literal renders by name
        Term::const_(n, int_ty())
    }

    #[test]
    fn renders_ground_arith_query() {
        // hyp: (> x 0)   goal: (> x 5)   ⇒ script asserts (> x 0) and (not (> x 5))
        // `>` : Int -> Int -> Bool so the kind-checked `Term::app` accepts it.
        let gt_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let gt = |a: Term, b: Term| {
            let g = Term::const_(">", gt_ty.clone());
            Term::app(Term::app(g, a).unwrap(), b).unwrap()
        };
        let hyp = gt(int_var("x"), int_const_op("0"));
        let goal = gt(int_var("x"), int_const_op("5"));
        let s = render_smtlib(&[hyp], &goal, &[], &PatternMap::new()).expect("renders");
        assert!(s.contains("(declare-const x Int)"), "got:\n{s}");
        assert!(s.contains("(assert (> x 0))"), "got:\n{s}");
        assert!(s.contains("(assert (not (> x 5)))"), "got:\n{s}");
        assert!(s.trim_end().ends_with("(check-sat)"), "got:\n{s}");
    }

    #[test]
    fn datatypes_render_as_one_group() {
        // a Nat-like decl renders as one `(declare-datatypes …)` group; its sort
        // never gets a conflicting `declare-sort`; a PARAMETRIC decl bails sound.
        let n = adsmt_theory::datatypes::DatatypeDecl {
            sort_name: "N".into(),
            constructors: vec!["zero".into(), "succ".into()],
            is_finite: false,
            arities: vec![0, 1],
            selectors: vec![vec![], vec!["succ!sel0".into()]],
            params: vec![],
            field_sorts: vec![vec![], vec!["N".into()]],
        };
        let x = Term::var("x", Type::const_("N", adsmt_core::Kind::Type));
        let eq_ty = Type::fun(
            Type::const_("N", adsmt_core::Kind::Type),
            Type::fun(Type::const_("N", adsmt_core::Kind::Type), Type::bool_()).unwrap(),
        )
        .unwrap();
        let goal =
            Term::app(Term::app(Term::const_("=", eq_ty), x.clone()).unwrap(), x).unwrap();
        let s = render_smtlib(&[], &goal, std::slice::from_ref(&n), &PatternMap::new()).expect("renders");
        assert!(
            s.contains("(declare-datatypes ((N 0) ) (((zero) (succ (succ!sel0 N)) ) ))"),
            "got:\n{s}"
        );
        assert!(!s.contains("(declare-sort N"), "datatype sort must not be re-declared:\n{s}");
        let mut p = n;
        p.params = vec!["T".into()];
        assert!(render_smtlib(&[], &Term::var("y", int_ty()), &[p], &PatternMap::new()).is_none());
    }

    #[test]
    fn bare_lambda_bails_sound() {
        let lam = Term::lam(
            adsmt_core::Var { name: "y".into(), ty: Type::const_("Int", adsmt_core::Kind::Type) },
            int_var("y"),
        );
        assert!(render_smtlib(&[], &lam, &[], &PatternMap::new()).is_none());
    }

    /// The OxiZ path end-to-end: a trivially-VALID goal `x = x` renders to
    /// `(assert (not (= x x)))`, which OxiZ decides `unsat` — so `proves_goal`
    /// returns `true`. Confirms the render → OxiZ → verdict wiring produces the
    /// verifying `unsat` the caller trusts (the completeness half; the soundness
    /// half — that a spurious OxiZ `sat` is NOT trusted — is exercised in
    /// `adsmt-lukb-driver`).
    #[cfg(feature = "oxiz")]
    #[test]
    fn oxiz_proves_a_trivially_valid_goal() {
        let eq_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let eq = Term::const_("=", eq_ty);
        let x = int_var("x");
        let goal = Term::app(Term::app(eq, x.clone()).unwrap(), x).unwrap(); // (= x x)
        assert!(crate::oxiz::proves_goal(&[], &goal, &[], &PatternMap::new()), "OxiZ should verify x = x");
    }

    // ── `:pattern` emission + the dead-pattern guard ────────────────────────

    /// `f : Int -> Int -> Int` as a free (declared) symbol — a `Var`, exactly
    /// as the lowering produces declared functions.
    fn f_var(name: &str) -> Term {
        let ty =
            Type::fun(int_ty(), Type::fun(int_ty(), int_ty()).unwrap()).unwrap();
        Term::var(name, ty)
    }
    fn app2(f: &Term, a: Term, b: Term) -> Term {
        Term::app(Term::app(f.clone(), a).unwrap(), b).unwrap()
    }
    /// `(>= (f x y) 0)` under `∀x:Int. ∀y:Int.` — the 2-binder test telescope.
    fn telescope_2(patterns: Vec<Vec<Term>>) -> (Term, PatternMap) {
        let f = f_var("f");
        let x = int_var("x");
        let y = int_var("y");
        let ge_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let body = app2(&Term::const_(">=", ge_ty), app2(&f, x, y), int_const_op("0"));
        let vy = adsmt_core::Var { name: "y".into(), ty: int_ty() };
        let vx = adsmt_core::Var { name: "x".into(), ty: int_ty() };
        let q = Term::mk_forall(vx, Term::mk_forall(vy, body).unwrap()).unwrap();
        let mut map = PatternMap::new();
        map.insert(q.clone(), QuantPatterns { arity: 2, groups: patterns });
        (q, map)
    }

    /// (i) multi-binder re-collection + two pattern groups render the exact
    /// `(forall (…) (! body :pattern … :pattern …))` shape.
    #[test]
    fn patterns_render_the_annotated_multibinder_shape() {
        let f = f_var("f");
        let (q, map) = telescope_2(vec![
            vec![app2(&f, int_var("x"), int_var("y"))],
            vec![app2(&f, int_var("y"), int_var("x"))],
        ]);
        let s = render_smtlib(&[q], &int_var("p"), &[], &map).expect("renders");
        assert!(
            s.contains(
                "(assert (forall ((x Int) (y Int)) \
                 (! (>= (f x y) 0) :pattern ((f x y)) :pattern ((f y x)))))"
            ),
            "got:\n{s}"
        );
    }

    /// (ii) guard (b): a group that misses a binder (`y` uncovered) cannot
    /// instantiate it — the WHOLE quantifier falls back to the plain
    /// (re-collected, un-annotated) form.
    #[test]
    fn uncovered_binder_falls_back_to_plain() {
        let f = f_var("f");
        let (q, map) = telescope_2(vec![vec![app2(&f, int_var("x"), int_var("x"))]]);
        let s = render_smtlib(&[q], &int_var("p"), &[], &map).expect("renders");
        assert!(
            s.contains("(assert (forall ((x Int) (y Int)) (>= (f x y) 0)))"),
            "got:\n{s}"
        );
        assert!(!s.contains(":pattern"), "no annotation may survive:\n{s}");
    }

    /// (iii) guard (c): a pattern whose head does not occur in the rendered
    /// body would NEVER fire (zero instantiations — worse than inference):
    /// plain fallback.
    #[test]
    fn erased_head_falls_back_to_plain() {
        let g = f_var("g"); // `g` occurs nowhere in the body `(>= (f x y) 0)`
        let (q, map) = telescope_2(vec![vec![app2(&g, int_var("x"), int_var("y"))]]);
        let s = render_smtlib(&[q], &int_var("p"), &[], &map).expect("renders");
        assert!(
            s.contains("(assert (forall ((x Int) (y Int)) (>= (f x y) 0)))"),
            "got:\n{s}"
        );
        assert!(!s.contains(":pattern"), "no annotation may survive:\n{s}");
    }

    /// (iv) a trigger-free OUTER forall whose INNER forall is a map key:
    /// re-collection stops before the key, so the inner level keeps its own
    /// annotation (annotating a merged binder list would mis-scope it).
    #[test]
    fn recollection_stops_before_an_annotated_inner_quantifier() {
        let f = f_var("f");
        let x = int_var("x");
        let y = int_var("y");
        let ge_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let body = app2(&Term::const_(">=", ge_ty), app2(&f, x, y), int_const_op("0"));
        let vy = adsmt_core::Var { name: "y".into(), ty: int_ty() };
        let vx = adsmt_core::Var { name: "x".into(), ty: int_ty() };
        let inner = Term::mk_forall(vy, body).unwrap();
        let outer = Term::mk_forall(vx, inner.clone()).unwrap();
        let mut map = PatternMap::new();
        map.insert(
            inner,
            QuantPatterns { arity: 1, groups: vec![vec![app2(&f, int_var("x"), int_var("y"))]] },
        );
        let s = render_smtlib(&[outer], &int_var("p"), &[], &map).expect("renders");
        assert!(
            s.contains(
                "(assert (forall ((x Int)) \
                 (forall ((y Int)) (! (>= (f x y) 0) :pattern ((f x y))))))"
            ),
            "got:\n{s}"
        );
    }

    /// (v) guard (d): a PATTERN-ONLY symbol (`k` appears in no assert body)
    /// still gets its `declare-fun` — one undeclared symbol would kill the
    /// whole script's parse.
    #[test]
    fn pattern_only_symbols_are_declared() {
        let f = f_var("f");
        let k = Term::var("k", Type::fun(int_ty(), int_ty()).unwrap());
        let kx = Term::app(k, int_var("x")).unwrap();
        let (q, map) = telescope_2(vec![vec![app2(&f, kx, int_var("y"))]]);
        let s = render_smtlib(&[q], &int_var("p"), &[], &map).expect("renders");
        assert!(s.contains("(declare-fun k (Int) Int)"), "got:\n{s}");
        assert!(s.contains(":pattern ((f (k x) y))"), "got:\n{s}");
    }

    /// (vi) an UNDER-APPLIED pattern (`(f x)` for 2-ary `f`) is an ill-arity
    /// `:pattern` the solver parses leniently but can never e-match — a dead
    /// trigger. The saturation guard rejects it (defense-in-depth behind the
    /// elab-face drop): plain fallback.
    #[test]
    fn partially_applied_pattern_falls_back_to_plain() {
        let f = f_var("f");
        // `{ (f x), (f y) }` covers both binders (guard (b) passes) and the
        // head `f` occurs in the body (guard (c) passes) — only the arity
        // saturation check can reject this group.
        let fx = Term::app(f.clone(), int_var("x")).unwrap();
        let fy = Term::app(f.clone(), int_var("y")).unwrap();
        let (q, map) = telescope_2(vec![vec![fx, fy]]);
        let s = render_smtlib(&[q], &int_var("p"), &[], &map).expect("renders");
        assert!(
            s.contains("(assert (forall ((x Int) (y Int)) (>= (f x y) 0)))"),
            "got:\n{s}"
        );
        assert!(!s.contains(":pattern"), "no annotation may survive:\n{s}");
    }

    /// (vii) guard (c) counts only FREE symbols: a NESTED binder's name (`h`
    /// below — the class of lower's fresh `x!N` names) must not vouch for a
    /// pattern head that never occurs ground in the body.
    #[test]
    fn nested_binder_name_does_not_vouch_for_a_pattern_head() {
        let f = f_var("f");
        let ge_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let body =
            app2(&Term::const_(">=", ge_ty), app2(&f, int_var("x"), int_var("h")), int_const_op("0"));
        let vh = adsmt_core::Var { name: "h".into(), ty: int_ty() };
        let vx = adsmt_core::Var { name: "x".into(), ty: int_ty() };
        let inner = Term::mk_forall(vh, body).unwrap();
        let outer = Term::mk_forall(vx, inner).unwrap();
        // the pattern head is a FUNCTION named exactly like the inner binder.
        let hfun = Term::var("h", Type::fun(int_ty(), int_ty()).unwrap());
        let mut map = PatternMap::new();
        map.insert(
            outer.clone(),
            QuantPatterns {
                arity: 1,
                groups: vec![vec![Term::app(hfun, int_var("x")).unwrap()]],
            },
        );
        let s = render_smtlib(&[outer], &int_var("p"), &[], &map).expect("renders");
        assert!(!s.contains(":pattern"), "no annotation may survive:\n{s}");
    }

    /// (viii) the `ADSMT_DELEGATE_NO_PATTERNS` kill-switch mechanism: a
    /// disabled context plans nothing (the env-var plumbing itself is a
    /// one-line read in `render_smtlib`, e2e-covered by the corpus A/B runs).
    #[test]
    fn kill_switch_disables_annotation_plans() {
        let f = f_var("f");
        let (q, map) = telescope_2(vec![vec![app2(&f, int_var("x"), int_var("y"))]]);
        let cx = RenderCx {
            patterns: &map,
            disabled: false,
            recollect: true,
            plans: RefCell::new(HashMap::new()),
        };
        assert!(cx.plan(&q).is_some(), "sanity: the annotation plans when enabled");
        let cx = RenderCx {
            patterns: &map,
            disabled: true,
            recollect: true,
            plans: RefCell::new(HashMap::new()),
        };
        assert!(cx.plan(&q).is_none(), "a disabled context must plan nothing");
    }

    /// (ix) the COMPLETENESS-FLOOR fallback (the seq-vstd ob08/ob09 class):
    /// a guard-passing pattern that never e-matches the ground terms makes
    /// the annotated script LOSE the proof OxiZ's own trigger inference
    /// finds; [`crate::oxiz::proves_goal`] must retry pattern-free and still
    /// verify the goal.
    #[cfg(feature = "oxiz")]
    #[test]
    fn defeating_pattern_falls_back_to_pattern_free() {
        let int1 = Type::fun(int_ty(), int_ty()).unwrap();
        let f = Term::var("f", int1.clone());
        let g = Term::var("g", int1);
        let app1 = |h: &Term, a: Term| Term::app(h.clone(), a).unwrap();
        let eq_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let plus_ty = Type::fun(int_ty(), Type::fun(int_ty(), int_ty()).unwrap()).unwrap();
        let eq = Term::const_("=", eq_ty);
        let plus = Term::const_("+", plus_ty);
        // hyp: ∀x:Int. f(g(x)) = f(x) + 1
        let x = int_var("x");
        let hyp_body = app2(
            &eq,
            app1(&f, app1(&g, x.clone())),
            app2(&plus, app1(&f, x.clone()), int_const_op("1")),
        );
        let vx = adsmt_core::Var { name: "x".into(), ty: int_ty() };
        let hyp = Term::mk_forall(vx, hyp_body).unwrap();
        // goal: f(g(g(a))) = f(a) + 2 — two axiom applications close it.
        let a = int_var("a");
        let goal = app2(
            &eq,
            app1(&f, app1(&g, app1(&g, a.clone()))),
            app2(&plus, app1(&f, a), int_const_op("2")),
        );
        // pattern `(g (g x))`: head `g` occurs in the body, covers `x`,
        // saturated — every static guard passes — but no ground `g(g(g(a)))`
        // exists, so e-matching yields only ONE of the two needed
        // instantiations: the annotated script does NOT prove the goal
        // (probe-verified against the OxiZ CLI).
        let pat = app1(&g, app1(&g, x));
        let mut map = PatternMap::new();
        map.insert(hyp.clone(), QuantPatterns { arity: 1, groups: vec![vec![pat]] });
        assert!(
            crate::oxiz::proves_goal(&[hyp], &goal, &[], &map),
            "the pattern-free fallback must recover the proof"
        );
    }
}
