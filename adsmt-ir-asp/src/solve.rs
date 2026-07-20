//! Solve an L0+L1 typed-ASP program: **finite grounding** + the forward Horn
//! **least-fixpoint** ([`crate::program`]) + query answering, with the L1
//! **theory interior** evaluated during grounding.
//!
//! The elaborator ([`crate::elab`]) has already type-checked the program. The
//! grounder instantiates each rule over the finite Herbrand universe (the
//! constants that appear, per sort — there are no function symbols, so this is
//! finite and complete). Each rule's **positive** body atoms become ground atom
//! ids; its **theory** atoms (range-restricted, hence ground after grounding)
//! are *evaluated arithmetically* — that evaluation is the gate's `θ`, collapsed
//! into the least-fixpoint's per-rule `guard`. The least model of the resulting
//! ground program is the unique answer set; a query is answered by membership.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::ast::{Atom, Expr, Literal, Rule, Term as AspTerm, Theory};
use crate::elab::{Elaborated, Stratification};
use crate::error::FaceError;
use crate::program::{Atom as AtomId, GroundNProgram, GroundNRule, GroundProgram, GroundRule};

/// The **entailment regime** a query answer was computed under. On a stratified
/// (L0–L2) program there is one model, so the regime is degenerate (`Cautious ≡
/// Brave ≡ membership`) and every answer is `Cautious`. On a non-stratified (L3)
/// program with multiple stable models the default is `Cautious` (true in *every*
/// model — the sound generalisation); `Brave` (true in *some*) is a later slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Entailment {
    /// True in **all** (constraint-consistent) stable models — the default, and
    /// the only regime in this slice.
    Cautious,
    /// True in **some** stable model. Reserved for a later slice.
    Brave,
}

/// The answer to one query: the satisfying assignments to its variables. For a
/// ground query, `vars` is empty and `tuples` is `[[]]` iff it holds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QueryAnswer {
    pub query: Atom,
    pub vars: Vec<String>,
    pub tuples: Vec<Vec<String>>,
    /// The entailment regime: always `Cautious` in this slice (see
    /// [`Entailment`]). On a stratified program it is the degenerate single-model
    /// membership; on an L3 program it is the `∩`-over-stable-models reading.
    pub mode: Entailment,
}

impl QueryAnswer {
    pub fn holds(&self) -> bool {
        !self.tuples.is_empty()
    }
}

/// The **stable models** of a non-stratified (L3) program, in surface form. Each
/// model is the set of atoms true in one answer set (sorted; constructor terms
/// rendered). `None` on the [`Solution`] of every stratified (L0–L2) program;
/// `Some` with an empty `models` vector means the program has **no answer set**
/// (e.g. `p :- not p.`) — distinct from a single empty answer set `[[]]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StableModels {
    pub models: Vec<Vec<Atom>>,
}

/// The **3-valued well-founded model** of a non-stratified program — the AFT
/// approximation pair `(L*, U*)` rendered to surface form (van Gelder's
/// alternating fixpoint, [`well_founded_model`]). It is sound and polynomial:
///
/// * `true_atoms` (`= L*`) hold in **every** stable model,
/// * `false_atoms` (`= B \ U*`, the greatest unfounded set) hold in **none**,
/// * `undefined_atoms` (`= U* \ L*`) are the residual a full guess-and-check
///   would still have to decide.
///
/// Exposed so a caller gets a sound PARTIAL verdict (cautious-true `true_atoms`,
/// cautious-false `false_atoms`) even on the large programs whose stable-model
/// enumeration is over budget — where the z3-compatible path abstains, the `Full`
/// output mode returns this instead.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ThreeValued {
    pub true_atoms: Vec<Atom>,
    pub false_atoms: Vec<Atom>,
    pub undefined_atoms: Vec<Atom>,
}

/// The answer to one abductive query `?- abduce G`: the ⊆-minimal sets of
/// abducible atoms that, assumed, make `G` hold. An empty set among the
/// explanations means `G` is already entailed deductively (the
/// "deduction = empty-abducible abduction" identity).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbduceAnswer {
    pub goal: Atom,
    /// Each explanation is a set of ground abducible atoms (surface form).
    pub explanations: Vec<Vec<Atom>>,
    /// `true` iff the backward relevance search hit a DoS budget and the
    /// explanation list may be **incomplete** (a sound under-report). Lets a
    /// caller tell "search clamped" apart from a genuine "no explanation".
    pub truncated: bool,
}

impl AbduceAnswer {
    /// Whether the goal holds **deductively** (some explanation is empty).
    pub fn entailed(&self) -> bool {
        self.explanations.iter().any(Vec::is_empty)
    }
    /// Whether any explanation (incl. the empty one) was found within budget.
    pub fn explained(&self) -> bool {
        !self.explanations.is_empty()
    }
}

/// The solution to a program: one answer per (deductive) query, one per
/// abductive query, whether the program is consistent, and — on a non-stratified
/// (L3) program — its stable models.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Solution {
    pub answers: Vec<QueryAnswer>,
    pub abductions: Vec<AbduceAnswer>,
    /// Whether the program has an answer set. The meaning generalises across the
    /// two model regimes (the field is the natural union of both):
    /// - **L0–L2 (stratified)**: `false` iff some integrity constraint `:- B` is
    ///   violated by the perfect model (the program then has no answer set).
    /// - **L3 (non-stratified)**: `false` iff *no* constraint-consistent stable
    ///   model exists (an odd negative loop like `p :- not p.`, or every stable
    ///   model discarded by a constraint). Equivalently, `!stable.models.is_empty()`.
    pub consistent: bool,
    /// The stable models (L3). `None` on every stratified program; on a
    /// non-stratified program `Some` — possibly with an empty `models` (no answer
    /// set). In the `Full` output mode this may be `None` even for a
    /// non-stratified program whose enumeration was over budget — the sound
    /// partial answer then lives in [`well_founded`](Solution::well_founded).
    /// See [`StableModels`].
    pub stable: Option<StableModels>,
    /// The 3-valued well-founded model (L3 only). Always `Some` on a
    /// non-stratified program (it is cheap to compute and brackets every stable
    /// model); `None` on a stratified program. The sound partial verdict the
    /// `Full` output mode surfaces when stable-model enumeration is over budget.
    /// See [`ThreeValued`].
    pub well_founded: Option<ThreeValued>,
}

/// Materialising the full hypothesis space costs memory; beyond this many ground
/// abducibles the face abstains (a loud, sound `FaceError`). This is now a
/// **grounding-memory** guard, not a search bound — the backward relevance
/// search (below) explores only the abducibles reachable from the goal, so it no
/// longer pays the old `2^k` subset enumeration and there is no per-explanation
/// cardinality cap.
const MAX_GROUND_ABDUCIBLES: usize = 4096;
/// The recursion-depth (stack-safety) bound on the backward relevance search.
/// The `visiting` cycle guard already guarantees *termination* over the finite
/// ground universe; this only caps native stack frames, set well above any
/// realistic ground derivation height (a deeper derivation is a sound truncation,
/// surfaced via `AbduceAnswer::truncated`).
const MAX_BACKWARD_DEPTH: u32 = 500;
/// The total number of candidate hypothesis-sets the backward search may
/// materialise — the **cartesian-product blow-up** guard (abduction is inherently
/// exponential: `g :- d₁…dₙ` with each `dᵢ` two-way abducible has `2ⁿ` minimal
/// explanations). On overrun the search returns its bounded partial family and
/// marks the answer `truncated` (a sound under-report, never a hang/OOM).
const MAX_BACKWARD_CANDIDATES: usize = 4096;

/// The cap on the cartesian-product cardinality the grounder may enumerate for a
/// single rule / constraint / query — `∏ |domain(sort)|` over the variables.
/// Checked *before* materialising the assignment vector ([`assignments`]), so a
/// wide-arity rule over a large domain abstains in milliseconds instead of
/// eagerly allocating the whole product. Bounds *every* grounding path (L0–L3).
const MAX_GROUNDING_ASSIGNMENTS: u128 = 2_000_000;

/// The number of ground rules the L3 grounder may materialise before abstaining
/// — a **grounding-memory** guard checked *during* the pass (a wide-arity rule
/// over a large domain can blow up the cartesian instantiation before the search
/// base is ever computed). A loud, sound [`FaceError::Unsupported`], never a
/// silent truncation (a dropped ground rule would change the least model).
const MAX_GROUND_N_RULES: usize = 262_144;
/// The cap on the number of **free** atoms `U \ L` the stable-model sweep
/// brackets — the structural guard that keeps the `1u64 << free` shift in range
/// and names the `2ⁿ`-candidate frontier in the abstain message. The real time
/// bound is [`MAX_STABLE_WORK`]; this is the sharp secondary cap.
const MAX_STABLE_FREE: usize = 24;
/// The **work** budget of the stable-model sweep: `2^|FREE| · |rules|`, the
/// dominant cost (each of the `2^|FREE|` candidates runs one reduct + one
/// `least_model` over the whole ground program, so a count-only bound on `|FREE|`
/// would still soft-hang on a large rule set). Over budget ⇒ a loud, sound
/// [`FaceError::Unsupported`] naming the loop-formula deferral — never a hang.
/// Empirically calibratable (the per-candidate cost is ~0.1 µs per ground rule).
const MAX_STABLE_WORK: u128 = 12_000_000;
/// The cap on the **materialised stable-model count** when a program decomposes
/// into independent components (the cartesian product of the components' answer
/// sets can be exponential in the number of components). The cap applies ONLY on
/// the decomposition path, which is reached only when the monolithic sweep is
/// already infeasible — so it never regresses a monolithic-decidable program; it
/// only bounds how many of the *previously-abstained* programs the cartesian
/// combine will enumerate. A SEARCH-bound program (few answer sets) stays well
/// under it; a COUNT-bound one (`2^k` answer sets) abstains soundly past it.
const MAX_STABLE_MODELS: usize = 1 << 14;

/// Solve the elaborated program: route on its [`Stratification`] —
/// `Stratified` ⇒ the L0–L2 perfect-model path (unchanged); `NonStratified` ⇒
/// the L3 stable-model gate.
pub fn solve(elab: &Elaborated) -> Result<Solution, FaceError> {
    solve_with_mode(elab, AspOutputMode::Z3Compatible)
}

/// How the ASP face renders an L3 (non-stratified) verdict at the output
/// boundary — the analogue of the SMT face's `OutputMode`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AspOutputMode {
    /// **z3-compatible** (default): enumerate the stable models, or — when that
    /// is over budget — abstain LOUDLY with an `Err` (the historical behaviour).
    /// The internal 3-valued well-founded model is still attached to the
    /// `Solution`, but a budget overrun is an error, not a partial answer.
    #[default]
    Z3Compatible,
    /// **Full**: never collapse a budget overrun to a total abstain — return the
    /// sound 3-valued well-founded model as a PARTIAL verdict instead (the
    /// successful enumeration path is unchanged).
    Full,
}

/// Solve `elab`, rendering an L3 verdict per `mode` (the in-process control for
/// the output mode; [`solve`] is the z3-compatible default).
pub fn solve_with_mode(elab: &Elaborated, mode: AspOutputMode) -> Result<Solution, FaceError> {
    match &elab.stratify {
        Stratification::Stratified(_) => solve_stratified(elab),
        Stratification::NonStratified(_) => solve_stable(elab, mode),
    }
}

/// The L0–L2 path: ground the program (evaluating the theory interior), compute
/// the **perfect model** stratum-by-stratum, and answer every query by
/// membership. Byte-identical to the pre-L3 behaviour (the `stable` field is
/// `None`, every query answer is `Cautious` — the degenerate single-model regime).
fn solve_stratified(elab: &Elaborated) -> Result<Solution, FaceError> {
    let mut intern = Interner::default();
    let has_neg = program_has_negation(elab);

    // The **perfect model**, computed stratum-by-stratum (L2): every `not q`
    // reads an already-decided lower stratum (the elaborator's stratification
    // guarantees `q` is strictly lower). A negation-free program is one stratum,
    // i.e. the least model — the unchanged L0/L1 behaviour.
    let model = stratified_model(elab, &mut intern)?;

    // integrity constraints: the program is inconsistent iff some `:- B` has a
    // ground instance that holds in the (full) perfect model.
    let consistent = !violates_constraints(elab, &model, &intern)?;

    // deductive queries.
    let mut answers = Vec::with_capacity(elab.queries.len());
    for q in &elab.queries {
        let mut vars = Vec::new();
        collect_vars(q, &elab.pred_sorts, &elab.ctor_sig, &mut vars);
        let mut tuples = Vec::new();
        for assign in assignments(&vars, &elab.domains)? {
            if !atom_in_universe(q, &vars, &assign, &elab.pred_sorts, &elab.domains) {
                continue;
            }
            let key = instantiate(q, &vars, &assign);
            if let Some(id) = intern.get(&q.pred, &key)
                && model.contains(&id)
            {
                tuples.push(assign);
            }
        }
        answers.push(QueryAnswer {
            query: q.clone(),
            vars: vars.into_iter().map(|(n, _)| n).collect(),
            tuples,
            mode: Entailment::Cautious,
        });
    }

    // abductive queries (the merge: abducible = a completion-less atom; the
    // forward lfp is reused inside the hypothesis-subset search). Abduction is
    // monotone — sound only over the definite/L1 fragment; a program mixing
    // abduction with `not` is a later (non-monotone) slice, so we abstain.
    let abductions = if elab.abduce_goals.is_empty() {
        Vec::new()
    } else if has_neg {
        return Err(FaceError::Unsupported(
            "abduction over a program with negation (`not`) is a later slice".into(),
        ));
    } else {
        let prog = flat_program(elab, &mut intern)?;
        let ground = ground_abducibles(elab, &mut intern)?;
        let mut out = Vec::with_capacity(elab.abduce_goals.len());
        for g in &elab.abduce_goals {
            let mut gvars = Vec::new();
            collect_vars(g, &elab.pred_sorts, &elab.ctor_sig, &mut gvars);
            if gvars.is_empty() {
                // a ground goal — exactly one answer (kept even when unexplained).
                out.push(abduce(&prog, &ground, g, &mut intern)?);
            } else {
                // a non-ground goal `?- abduce p(X)`: enumerate the goal variables
                // over the finite domains and abduce per ground instance, keeping
                // the bindings that have at least one explanation.
                for assign in assignments(&gvars, &elab.domains)? {
                    if !atom_in_universe(g, &gvars, &assign, &elab.pred_sorts, &elab.domains) {
                        continue;
                    }
                    let gi = instantiate_goal_atom(g, &gvars, &assign);
                    let ans = abduce(&prog, &ground, &gi, &mut intern)?;
                    if ans.explained() {
                        out.push(ans);
                    }
                }
            }
        }
        out
    };

    Ok(Solution { answers, abductions, consistent, stable: None, well_founded: None })
}

/// Whether any rule / constraint body carries a `not` literal.
fn program_has_negation(elab: &Elaborated) -> bool {
    let body_has_neg = |b: &[Literal]| b.iter().any(|l| matches!(l, Literal::Neg(_)));
    elab.rules.iter().any(|r| body_has_neg(&r.body))
        || elab.constraints.iter().any(|b| body_has_neg(b))
}

/// Whether any integrity constraint `:- B` has a ground instance that **holds**
/// in `model` — every positive body atom present, every theory guard satisfied,
/// every `not q` absent. Shared by the L2 perfect-model path (one model) and the
/// L3 path (each candidate stable model is discarded if it violates a
/// constraint). A theory-guard evaluation error propagates as a `FaceError`.
fn violates_constraints(
    elab: &Elaborated,
    model: &BTreeSet<AtomId>,
    intern: &Interner,
) -> Result<bool, FaceError> {
    for body in &elab.constraints {
        let mut vars = Vec::new();
        for a in body.iter().filter_map(as_pos) {
            collect_vars(a, &elab.pred_sorts, &elab.ctor_sig, &mut vars);
        }
        'assign: for assign in assignments(&vars, &elab.domains)? {
            // every constructor pattern must match the universe.
            if !body
                .iter()
                .filter_map(as_pos)
                .all(|a| atom_in_universe(a, &vars, &assign, &elab.pred_sorts, &elab.domains))
            {
                continue;
            }
            // theory guards + negative literals must hold.
            let ints = int_bindings(&vars, &assign)?;
            for lit in body {
                match lit {
                    Literal::Theory(t) if !eval_compare(t, &vars, &assign, &ints)? => continue 'assign,
                    Literal::Neg(a) => {
                        // `not a` holds iff `a` is not in the model.
                        let in_model = intern
                            .get(&a.pred, &instantiate(a, &vars, &assign))
                            .is_some_and(|id| model.contains(&id));
                        if in_model {
                            continue 'assign;
                        }
                    }
                    _ => {}
                }
            }
            // all positive body atoms in the model ⇒ the constraint is violated.
            let all_in = body.iter().filter_map(as_pos).all(|a| {
                intern
                    .get(&a.pred, &instantiate(a, &vars, &assign))
                    .is_some_and(|id| model.contains(&id))
            });
            if all_in {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

/// The **L3 path**: solve a non-stratified program by the bounded stable-model
/// gate. Ground it retaining the negative bodies ([`ground_n_program`]),
/// enumerate the bracketed candidate space and certify each through the trusted
/// GL reduct + lfp ([`stable_models`]), discard constraint-violating answer sets,
/// and answer queries **cautiously** (`∩` over the surviving stable models).
fn solve_stable(elab: &Elaborated, mode: AspOutputMode) -> Result<Solution, FaceError> {
    // abduction over a non-stratified program is a later (non-monotone) slice —
    // abstain LOUDLY rather than silently dropping the goal (the L2 `has_neg`
    // guard lives on the stratified arm and is never reached here).
    if !elab.abduce_goals.is_empty() {
        return Err(FaceError::Unsupported(
            "abduction over a non-stratified (stable-model) program is a later slice".into(),
        ));
    }

    let mut intern = Interner::default();
    let p = ground_n_program(elab, &mut intern)?;

    // The 3-valued well-founded model — cheap (polynomial), brackets every stable
    // model, and is attached to the Solution below (the AFT approximation pair).
    let (l_star, u_star) = well_founded_model(&p);

    // enumerate + gate, then keep only the constraint-consistent answer sets. On a
    // budget overrun the z3-compatible mode propagates the abstain (`Err`); the
    // `Full` mode instead returns the sound 3-valued well-founded model as a
    // PARTIAL verdict — the new capability (cautious-true `L*`, cautious-false
    // `B \ U*`), decided on programs the guess-and-check cannot reach.
    let stable_sets = match stable_models(&p) {
        Ok(sets) => sets,
        Err(e) => {
            if mode == AspOutputMode::Full {
                let wfm = three_valued(&l_star, &u_star, &intern);
                // `L*` violating an integrity constraint ⇒ it is violated in EVERY
                // stable model (`L* ⊆ M`) ⇒ definitely no answer set (sound). The
                // `true` direction is only "not DEFINITELY inconsistent" (a stable
                // model might still be killed via an undefined atom).
                let consistent = !violates_constraints(elab, &l_star, &intern)?;
                let answers = cautious_queries(elab, &intern, |id| l_star.contains(&id))?;
                return Ok(Solution {
                    answers,
                    abductions: Vec::new(),
                    consistent,
                    stable: None,
                    well_founded: Some(wfm),
                });
            }
            return Err(e);
        }
    };
    let mut models: Vec<BTreeSet<AtomId>> = Vec::new();
    for m in stable_sets {
        if !violates_constraints(elab, &m, &intern)? {
            models.push(m);
        }
    }
    let consistent = !models.is_empty();

    // render answer sets to surface form (atoms sorted within a model, models
    // sorted between — fully deterministic).
    let rev = intern.reverse();
    let mut surface: Vec<Vec<Atom>> = models
        .iter()
        .map(|m| {
            let mut atoms: Vec<Atom> = m.iter().filter_map(|id| rev.get(id).cloned()).collect();
            atoms.sort_by_cached_key(render_atom);
            atoms
        })
        .collect();
    surface.sort_by(|x, y| {
        let kx: Vec<String> = x.iter().map(render_atom).collect();
        let ky: Vec<String> = y.iter().map(render_atom).collect();
        kx.cmp(&ky)
    });

    // cautious queries: a binding holds iff its ground atom is in EVERY stable
    // model (`∩`). With no answer set, no binding is entailed (empty tuples; the
    // `consistent`/`stable.models.is_empty()` pair already signals "no model").
    let answers = cautious_queries(elab, &intern, |id| {
        !models.is_empty() && models.iter().all(|m| m.contains(&id))
    })?;

    Ok(Solution {
        answers,
        abductions: Vec::new(),
        consistent,
        stable: Some(StableModels { models: surface }),
        well_founded: Some(three_valued(&l_star, &u_star, &intern)),
    })
}

// ---------------------------------------------------------------------------
// L5 first slice — weak constraints (`:~ B. [weight@level]`).
//
// A weak constraint's body is checked (elab.rs) and grounded (below) exactly
// like an integrity constraint's, but a ground instance whose body HOLDS never
// kills an answer set — it costs its declared `weight` instead (ASP-Core-2's
// "violated" terminology, dual to a strong constraint: "violated" = "body
// holds"; verified against clingo 5.8.0: `a. :~ a. [1@0]` ⇒ optimal cost `1`).
// The optimal answer set(s) minimize the summed cost.
//
// **Counting rule** (the soundness-critical half of this design, beyond plain
// polarity): ASP-Core-2 identifies a ground weak-constraint instance by the
// tuple `(weight, level, terms)`; this surface has no `terms` clause, so
// `terms` is always empty — and instances that end up sharing an identical
// `(weight, level)` pair are **counted once**, not summed per instance, and
// this dedup is GLOBAL across every weak constraint in the program, not
// scoped to one declaration. Empirically re-verified three independent ways
// against clingo 5.8.0 (not assumed from the task's own "one soft clause per
// grounding" paraphrase, which is the naive-and-wrong reading):
//   - `p(1..3). :~ p(X). [5@0].`                       ⇒ cost `5`  (not `15`)
//   - `a. b. :~ a. [5@0]. :~ b. [5@0].`                 ⇒ cost `5`  (not `10`)
//   - `p(1..3). :~ p(X). [X@0].`                        ⇒ cost `6`  (distinct
//     per-instance weights ⇒ no collision ⇒ sums normally)
// A caller wanting each ground instance counted independently must give it a
// distinct weight — not a bug, the standard's own semantics for a `terms`-free
// weak constraint (clingo's `[weight@level, t1, …]` extra-terms disambiguator
// is out of scope this slice; see `ast::Item::WeakConstraint`'s doc comment).
//
// **Search scope**: finding the weight-optimal answer set in general needs a
// weight-aware stable-model search (weight-aware unfounded-set propagation) —
// out of scope for this slice. Instead: reuse the SAME trusted, GL-reduct-
// gated enumeration `solve`/`solve_with_mode` already run (stratified ⇒ the
// one perfect model; non-stratified ⇒ every constraint-consistent stable
// model) to get the finite, already-verified candidate set, then pick the
// cost-minimal one(s) by plain evaluation (`weak_cost`) — an argmin, not a new
// search procedure. This is intentionally NOT a MaxSAT *search*: by the time a
// candidate model is in hand its atoms are already fully decided by the
// trusted gate, so there is nothing left to search for, only to evaluate.
// `adsmt-delegate::asp` mirrors this cost using `oxiz-opt`'s own `Weight` type
// for the trusted result's arithmetic, without re-invoking a solver.

/// One ground instance of a weak constraint: the AtomIds of its positive body
/// atoms and its `not`-negated atoms — theory guards are evaluated once, up
/// front (model-independent, exactly `ground_n_program`'s `guard &&`), and an
/// atom that is never interned by the rest of the program's grounding can
/// never be in ANY candidate model, so (mirroring `violates_constraints`'s own
/// `intern.get(..).is_some_and(..)` reading, but computed once since the
/// interner — unlike the candidate model — does not vary per candidate): a
/// positive reference to one prunes the whole instance (it can never hold),
/// a negative reference to one is dropped (CWA: `not` trivially holds).
struct GroundWeak {
    pos: Vec<AtomId>,
    neg: Vec<AtomId>,
    weight: i64,
}

/// Ground every [`Elaborated::weak_constraints`] instance over the finite
/// Herbrand universe — [`violates_constraints`]'s grounding shape, but
/// recording the (pos, neg) AtomId sets instead of testing them against one
/// fixed model (a weak-constraint instance is re-tested against EVERY
/// candidate answer set — see [`solve_weak_optimal`]). `level` is not carried
/// per-instance: the caller has already rejected a multi-level program via
/// [`check_single_level`], so every instance here shares the program's one
/// level.
fn ground_weak_constraints(
    elab: &Elaborated,
    intern: &Interner,
) -> Result<Vec<GroundWeak>, FaceError> {
    let mut out = Vec::new();
    for wc in &elab.weak_constraints {
        let body = &wc.body;
        let mut vars = Vec::new();
        for a in body.iter().filter_map(as_pos) {
            collect_vars(a, &elab.pred_sorts, &elab.ctor_sig, &mut vars);
        }
        'assign: for assign in assignments(&vars, &elab.domains)? {
            if !body
                .iter()
                .filter_map(as_pos)
                .all(|a| atom_in_universe(a, &vars, &assign, &elab.pred_sorts, &elab.domains))
            {
                continue;
            }
            let ints = int_bindings(&vars, &assign)?;
            let mut pos = Vec::new();
            let mut neg = Vec::new();
            for lit in body {
                match lit {
                    Literal::Theory(t) => {
                        if !eval_compare(t, &vars, &assign, &ints)? {
                            continue 'assign;
                        }
                    }
                    Literal::Pos(a) => match intern.get(&a.pred, &instantiate(a, &vars, &assign)) {
                        Some(id) => pos.push(id),
                        // never derivable anywhere in the program ⇒ this ground
                        // instance's body can never hold in any candidate model.
                        None => continue 'assign,
                    },
                    Literal::Neg(a) => {
                        if let Some(id) = intern.get(&a.pred, &instantiate(a, &vars, &assign)) {
                            neg.push(id);
                        }
                        // else: never derivable ⇒ `not a` trivially holds (CWA) —
                        // no restriction to record.
                    }
                }
            }
            out.push(GroundWeak { pos, neg, weight: wc.weight });
        }
    }
    Ok(out)
}

/// Whether one ground weak-constraint instance's body **holds** in `model`
/// (every positive atom present, every `not`-atom absent) — see the module
/// section comment above for the verified polarity.
fn weak_holds(gw: &GroundWeak, model: &BTreeSet<AtomId>) -> bool {
    gw.pos.iter().all(|id| model.contains(id)) && gw.neg.iter().all(|id| !model.contains(id))
}

/// The ASP-Core-2 weak-constraint cost of `model` under `instances` — grouped
/// by weight (single-level, so `(weight, level)` collapses to just `weight`),
/// each group counted **once** if any instance in it holds. See the module
/// section comment above for the (clingo-verified) counting rule.
///
/// Sums in `i128` (a program can have arbitrarily many distinct weights, and
/// `i64::MAX`-adjacent declared weights are legal individually), then checks
/// the total still fits `i64` — the public [`WeakOptimum::cost`] type — before
/// returning it. An out-of-range total is a loud [`FaceError::Unsupported`]
/// abstain, never a silently wrapped (and possibly sign-flipped) wrong
/// optimum: same "abstain, never approximate" discipline as a stable-model
/// enumeration budget overrun elsewhere in this module.
fn weak_cost(instances: &[GroundWeak], model: &BTreeSet<AtomId>) -> Result<i64, FaceError> {
    let satisfied_weights: BTreeSet<i64> =
        instances.iter().filter(|gw| weak_holds(gw, model)).map(|gw| gw.weight).collect();
    let sum: i128 = satisfied_weights.iter().map(|&w| i128::from(w)).sum();
    i64::try_from(sum).map_err(|_| {
        FaceError::Unsupported(format!(
            "weak-constraint cost overflowed i64: {} distinct satisfied weight(s) sum to \
             {sum}, outside i64::MIN..=i64::MAX — refusing to report a wrapped optimum",
            satisfied_weights.len()
        ))
    })
}

/// Reject a program whose weak constraints span more than one distinct
/// `level` — **single-level only** this slice (see
/// [`crate::ast::Item::WeakConstraint`]'s doc comment); full lexicographic
/// multi-level stratification is a deferred follow-up, refused loudly rather
/// than silently approximated.
fn check_single_level(elab: &Elaborated) -> Result<(), FaceError> {
    let levels: BTreeSet<i64> = elab.weak_constraints.iter().map(|w| w.level).collect();
    if levels.len() > 1 {
        let list: Vec<String> = levels.iter().map(i64::to_string).collect();
        return Err(FaceError::Unsupported(format!(
            "weak constraints span {} distinct optimization levels ({}) — this slice \
             supports a single level only; full lexicographic multi-level \
             stratification is a deferred follow-up",
            levels.len(),
            list.join(", ")
        )));
    }
    Ok(())
}

/// The result of [`solve_weak_optimal`]: the weak-constraint-optimal answer
/// set(s) of a program (L5 first slice) and their shared minimal cost.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WeakOptimum {
    /// Whether the program has an answer set at all (same meaning as
    /// [`Solution::consistent`]) — `false` iff no (hard-)constraint-consistent
    /// answer set exists, in which case `cost` is `None` and `models` is empty.
    pub consistent: bool,
    /// The minimal weak-constraint cost among the program's constraint-
    /// consistent answer set(s). `None` iff `!consistent`.
    pub cost: Option<i64>,
    /// EVERY cost-minimal answer set (surface form, sorted — mirrors
    /// [`StableModels::models`]); more than one iff several answer sets tie
    /// for the minimal cost.
    pub models: Vec<Vec<Atom>>,
}

/// Solve a program's weak constraints (L5 first slice): among its
/// (hard-)constraint-consistent answer set(s) — the SAME set [`solve`] would
/// report (stratified ⇒ the one perfect model; non-stratified ⇒ every
/// constraint-consistent stable model, via the SAME trusted GL-reduct-gated
/// enumeration, never re-decided) — pick the one(s) minimizing the summed
/// weight of its satisfied weak-constraint ground instances (see the module
/// section comment above for the exact, clingo-verified counting rule).
///
/// **Single-level only**: a program whose weak constraints span more than one
/// `level` is refused ([`FaceError::Unsupported`]) rather than silently
/// approximated. A budget overrun in the underlying stable-model enumeration
/// propagates as the SAME [`FaceError`] `solve` would return for that program
/// (never silently narrowed to a partial/possibly-wrong optimum).
pub fn solve_weak_optimal(elab: &Elaborated) -> Result<WeakOptimum, FaceError> {
    check_single_level(elab)?;
    let mut intern = Interner::default();

    let candidates: Vec<BTreeSet<AtomId>> = match &elab.stratify {
        Stratification::Stratified(_) => {
            let m = stratified_model(elab, &mut intern)?;
            if violates_constraints(elab, &m, &intern)? { Vec::new() } else { vec![m] }
        }
        Stratification::NonStratified(_) => {
            let p = ground_n_program(elab, &mut intern)?;
            let sets = stable_models(&p)?;
            let mut kept = Vec::with_capacity(sets.len());
            for m in sets {
                if !violates_constraints(elab, &m, &intern)? {
                    kept.push(m);
                }
            }
            kept
        }
    };

    if candidates.is_empty() {
        return Ok(WeakOptimum { consistent: false, cost: None, models: Vec::new() });
    }

    let weak = ground_weak_constraints(elab, &intern)?;
    let costs: Vec<i64> =
        candidates.iter().map(|m| weak_cost(&weak, m)).collect::<Result<Vec<i64>, FaceError>>()?;
    let min_cost = *costs.iter().min().expect("candidates is non-empty (checked above)");

    let rev = intern.reverse();
    let mut surface: Vec<Vec<Atom>> = candidates
        .into_iter()
        .zip(costs)
        .filter(|(_, c)| *c == min_cost)
        .map(|(m, _)| {
            let mut atoms: Vec<Atom> = m.iter().filter_map(|id| rev.get(id).cloned()).collect();
            atoms.sort_by_cached_key(render_atom);
            atoms
        })
        .collect();
    surface.sort_by(|x, y| {
        let kx: Vec<String> = x.iter().map(render_atom).collect();
        let ky: Vec<String> = y.iter().map(render_atom).collect();
        kx.cmp(&ky)
    });

    Ok(WeakOptimum { consistent: true, cost: Some(min_cost), models: surface })
}

/// Cautious query answers: a binding holds iff `in_every` accepts its ground atom
/// id (membership in EVERY stable model). Shared by the enumerated path
/// (`id ∈ ⋂ models`) and the well-founded partial path (`id ∈ L*`, a subset of
/// every stable model — sound, possibly incomplete).
fn cautious_queries(
    elab: &Elaborated,
    intern: &Interner,
    in_every: impl Fn(AtomId) -> bool,
) -> Result<Vec<QueryAnswer>, FaceError> {
    let mut answers = Vec::with_capacity(elab.queries.len());
    for q in &elab.queries {
        let mut vars = Vec::new();
        collect_vars(q, &elab.pred_sorts, &elab.ctor_sig, &mut vars);
        let mut tuples = Vec::new();
        for assign in assignments(&vars, &elab.domains)? {
            if !atom_in_universe(q, &vars, &assign, &elab.pred_sorts, &elab.domains) {
                continue;
            }
            let key = instantiate(q, &vars, &assign);
            // an un-interned atom is in no model ⇒ not cautious-entailed.
            if let Some(id) = intern.get(&q.pred, &key)
                && in_every(id)
            {
                tuples.push(assign);
            }
        }
        answers.push(QueryAnswer {
            query: q.clone(),
            vars: vars.into_iter().map(|(n, _)| n).collect(),
            tuples,
            mode: Entailment::Cautious,
        });
    }
    Ok(answers)
}

/// Render the well-founded `(L*, U*)` AtomId pair to the surface [`ThreeValued`]
/// model: true = `L*`, undefined = `U* \ L*`, false = `B \ U*` (`B` = every
/// interned atom). Each set is sorted deterministically by surface form.
fn three_valued(
    l_star: &BTreeSet<AtomId>,
    u_star: &BTreeSet<AtomId>,
    intern: &Interner,
) -> ThreeValued {
    let rev = intern.reverse();
    let render = |ids: &mut dyn Iterator<Item = AtomId>| -> Vec<Atom> {
        let mut v: Vec<Atom> = ids.filter_map(|id| rev.get(&id).cloned()).collect();
        v.sort_by_cached_key(render_atom);
        v
    };
    let true_atoms = render(&mut l_star.iter().copied());
    let undefined_atoms = render(&mut u_star.difference(l_star).copied());
    let false_atoms = render(&mut rev.keys().copied().filter(|id| !u_star.contains(id)));
    ThreeValued { true_atoms, false_atoms, undefined_atoms }
}

/// Ground a non-stratified program **retaining its negative bodies** — one pass
/// over all facts + rules, no stratum filter, theory guards evaluated as `θ`.
/// Unlike [`stratified_model`] (which folds each `not q` into the scalar guard
/// against a frozen lower stratum, destroying the negative body), each `not p`
/// is interned into the rule's `neg` so the GL reduct can be built.
///
/// A guard-FALSE instance is **dropped** (mirroring `least_model`'s `r.guard &&`),
/// so the reduct never sees a θ-false rule; a guard that **errors** propagates as
/// a `FaceError` (the `?`). Bounded *during* the pass by [`MAX_GROUND_N_RULES`]
/// (a loud, sound abstain, never a silent truncation).
fn ground_n_program(elab: &Elaborated, intern: &mut Interner) -> Result<GroundNProgram, FaceError> {
    let mut prog = GroundNProgram::new();
    for fact in &elab.facts {
        let id = intern.atom(&fact.pred, &ground_args(fact)?);
        prog.push(GroundNRule::fact(id));
        if prog.rules.len() > MAX_GROUND_N_RULES {
            return Err(grounding_overrun());
        }
    }
    for rule in &elab.rules {
        let vars = rule_vars(rule, &elab.pred_sorts, &elab.ctor_sig);
        for assign in assignments(&vars, &elab.domains)? {
            if !rule_grounds_in_universe(rule, &vars, &assign, elab)? {
                continue;
            }
            let ints = int_bindings(&vars, &assign)?;
            // θ guard: the AND of the comparison atoms. An error propagates; a
            // false guard DROPS this instance (the reduct never sees it).
            let mut guard = true;
            for t in rule.body.iter().filter_map(as_theory) {
                guard &= eval_compare(t, &vars, &assign, &ints)?;
                if !guard {
                    break;
                }
            }
            if !guard {
                continue;
            }
            let head = intern.atom(&rule.head.pred, &instantiate(&rule.head, &vars, &assign));
            let pos: Vec<AtomId> = rule
                .body
                .iter()
                .filter_map(as_pos)
                .map(|b| intern.atom(&b.pred, &instantiate(b, &vars, &assign)))
                .collect();
            let neg: Vec<AtomId> = rule
                .body
                .iter()
                .filter_map(as_neg)
                .map(|a| intern.atom(&a.pred, &instantiate(a, &vars, &assign)))
                .collect();
            prog.push(GroundNRule::rule(head, pos, neg));
            if prog.rules.len() > MAX_GROUND_N_RULES {
                return Err(grounding_overrun());
            }
        }
    }
    Ok(prog)
}

/// The **well-founded bracket** `[L*, U*]` of a ground normal program — van
/// Gelder's *alternating fixpoint* of the antitone reduct least-model operator
/// `Φ(S) = reduct(S).least_model()`. Iterating `K_{i+1} = Φ(Φ(K_i))` from `∅`
/// (monotone in a finite base, so it converges) yields the **well-founded TRUE**
/// atoms `L*`; `U* = Φ(L*)` is the upper bound, and `B \ U*` are the well-founded
/// FALSE atoms — the **greatest unfounded set** (the unfounded-set propagator,
/// computed as a fixpoint rather than incrementally). By the Van
/// Gelder–Ross–Schlipf theorem the well-founded model brackets every stable model
/// (`L* ⊆ M ⊆ U*` for every GL-stable `M`), so this only ever *shrinks* the free
/// set the guess-and-check enumerates — never skips a stable model.
///
/// Public so a caller can read the sound 3-valued well-founded model directly
/// (true = `L*`, undefined = `U* \ L*`, false = `B \ U*`); the surface-rendered
/// form is [`ThreeValued`], attached to every L3 [`Solution`].
pub fn well_founded_model(p: &GroundNProgram) -> (BTreeSet<AtomId>, BTreeSet<AtomId>) {
    let phi = |s: &BTreeSet<AtomId>| p.reduct(s).least_model();
    let mut k = BTreeSet::new();
    loop {
        let upper = phi(&k); // over-approx of the true atoms (= B \ false-so-far)
        let k_next = phi(&upper); // Φ²(k) — a tighter under-approx (k_next ⊇ k)
        if k_next == k {
            return (k, upper); // (L*, U*) = (K*, Φ(K*)) at the fixpoint
        }
        k = k_next;
    }
}

/// Enumerate the stable models of a ground normal program by **bounded
/// guess-and-check** over the [`well_founded_model`] `L* ⊆ M ⊆ U*`. The
/// well-founded model forces the maximal set of atoms in (`L*`) / out (`B \ U*`)
/// in polynomial time, so only the *undefined* atoms `U* \ L*` remain to guess —
/// strictly tighter than the old one-step reduct bracket
/// (`Φ(B) ⊆ M ⊆ Φ(∅)`, which is just the first alternating-fixpoint iteration),
/// so it decides more programs within the work budget. Each subset of the free
/// atoms is gated by the trusted [`GroundNProgram::is_stable`].
///
/// `Ok(vec)` is the complete (within-budget) set of stable models — an empty vec
/// is the **sound "no answer set"** verdict. Over the work budget it is instead a
/// loud `Err(Unsupported)` (the loop-formula learning solver is a later slice), so
/// a caller can never confuse an abstain (`Err`) with "no answer set" (`Ok([])`).
///
/// **Decomposition (the splitting-theorem base case).** The program is first split
/// into the connected components of its atom-co-occurrence graph
/// ([`connected_components`]) — independent subprograms over DISJOINT atom sets.
/// The answer sets of a disjoint union are exactly the cartesian product of the
/// components' answer sets, so each component runs the well-founded bracket +
/// guess at its OWN (smaller) `|FREE|`. A program of `k` independent small loops
/// — whose GLOBAL `|FREE|` blows the monolithic `MAX_STABLE_FREE` budget — is now
/// decided component-by-component. Pure improvement: a single-component program
/// takes the unchanged monolithic path, and the per-component `|FREE|` never
/// exceeds the global one, so decomposition never abstains where the monolithic
/// sweep would have succeeded (the cartesian product is bounded by the same
/// `2^{global free}` ceiling the monolithic sweep already materialises).
fn stable_models(p: &GroundNProgram) -> Result<Vec<BTreeSet<AtomId>>, FaceError> {
    let components = connected_components(p);
    if components.len() <= 1 {
        return stable_models_component(p); // monolithic path (unchanged)
    }
    // Multi-component. If the MONOLITHIC sweep over the whole program is itself
    // within budget, run it — same models, no model-count cap — so decomposition
    // **never abstains where the monolithic path would have succeeded**. Only when
    // the global free set / work blows the monolithic budget do we decompose; the
    // cartesian model-count cap then applies, but only to programs the monolithic
    // sweep already abstained on (improvement-only). A program of `k` independent
    // SEARCH-bound loops (large global `|FREE|`, FEW answer sets each) is now
    // decided; a COUNT-bound program (`k` independent binary choices ⇒ `2^k`
    // answer sets) is inherently un-enumerable and abstains past the cap.
    let (lower, upper) = well_founded_model(p);
    let gfree = upper.difference(&lower).count();
    if gfree <= MAX_STABLE_FREE
        && (1u128 << gfree).saturating_mul(p.rules.len().max(1) as u128) <= MAX_STABLE_WORK
    {
        return stable_models_component(p);
    }
    // Solve each independent subprogram, then cartesian-combine. A component with
    // NO stable model makes the whole disjoint union inconsistent (cartesian with
    // ∅ = ∅) — a sound "no answer set".
    let mut combos: Vec<BTreeSet<AtomId>> = vec![BTreeSet::new()];
    for comp in &components {
        let comp_models = stable_models_component(comp)?;
        if comp_models.is_empty() {
            return Ok(Vec::new());
        }
        // guard the materialised model count (the cartesian product can be
        // exponential in the number of components — a sound abstain, never a hang).
        if combos.len().saturating_mul(comp_models.len()) > MAX_STABLE_MODELS {
            return Err(stable_models_overrun(components.len()));
        }
        let mut next: Vec<BTreeSet<AtomId>> = Vec::with_capacity(combos.len() * comp_models.len());
        for acc in &combos {
            for m in &comp_models {
                let mut u = acc.clone();
                u.extend(m.iter().copied());
                next.push(u);
            }
        }
        combos = next;
    }
    Ok(combos)
}

/// The monolithic stable-model sweep over one (connected) program: bounded
/// guess-and-check over the [`well_founded_model`] `L* ⊆ M ⊆ U*`, each subset of
/// the free atoms `U* \ L*` gated by the trusted [`GroundNProgram::is_stable`].
fn stable_models_component(p: &GroundNProgram) -> Result<Vec<BTreeSet<AtomId>>, FaceError> {
    let (lower, upper) = well_founded_model(p);
    let free: Vec<AtomId> = upper.difference(&lower).copied().collect();

    // the exponential guards: a sharp structural cap on |FREE| (shift safety +
    // the abstain message) and the work-aware time bound (the real gate).
    if free.len() > MAX_STABLE_FREE {
        return Err(stable_overrun(free.len(), p.rules.len()));
    }
    let candidates = 1u128 << free.len();
    if candidates.saturating_mul(p.rules.len().max(1) as u128) > MAX_STABLE_WORK {
        return Err(stable_overrun(free.len(), p.rules.len()));
    }

    // sweep every subset M = L ∪ S, S ⊆ FREE; keep the GL-certified ones.
    let mut models = Vec::new();
    for mask in 0u128..candidates {
        let mut m = lower.clone();
        for (i, &a) in free.iter().enumerate() {
            if (mask >> i) & 1 == 1 {
                m.insert(a);
            }
        }
        if p.is_stable(&m) {
            models.push(m);
        }
    }
    Ok(models)
}

/// Split a ground normal program into the **connected components** of its
/// atom-co-occurrence graph: two atoms are adjacent iff they share a rule (head,
/// positive, or negative body), and each rule is assigned to the component of its
/// atoms. Components are over DISJOINT atom sets, so they are independent
/// subprograms — the answer sets of the whole program are the cartesian product
/// of the components' (the disjoint-union base case of the splitting theorem).
/// Returns one [`GroundNProgram`] per component (the partition of `p.rules`); an
/// empty program yields no components (the caller's `len() <= 1` short-circuit
/// then takes the unchanged monolithic path).
fn connected_components(p: &GroundNProgram) -> Vec<GroundNProgram> {
    if p.rules.is_empty() {
        return Vec::new();
    }
    let rule_atoms = |r: &GroundNRule| -> Vec<AtomId> {
        std::iter::once(r.head)
            .chain(r.pos.iter().copied())
            .chain(r.neg.iter().copied())
            .collect()
    };
    // index every atom, then union the atoms within each rule (union–find).
    let atoms: BTreeSet<AtomId> = p.rules.iter().flat_map(rule_atoms).collect();
    let idx: HashMap<AtomId, usize> = atoms.iter().enumerate().map(|(i, &a)| (a, i)).collect();
    let mut parent: Vec<usize> = (0..atoms.len()).collect();
    for r in &p.rules {
        let ra = rule_atoms(r);
        let first = idx[&ra[0]];
        for a in &ra[1..] {
            let (x, y) = (uf_find(&mut parent, first), uf_find(&mut parent, idx[a]));
            if x != y {
                parent[x] = y;
            }
        }
    }
    // group rules by their head atom's component root.
    let mut groups: HashMap<usize, GroundNProgram> = HashMap::new();
    for r in &p.rules {
        let root = uf_find(&mut parent, idx[&r.head]);
        groups.entry(root).or_default().push(r.clone());
    }
    groups.into_values().collect()
}

/// Union–find `find` with path halving.
fn uf_find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

fn stable_models_overrun(components: usize) -> FaceError {
    FaceError::Unsupported(format!(
        "the L3 answer-set count exceeds {MAX_STABLE_MODELS} (the cartesian product over \
         {components} independent components — a model-enumeration limit; the loop-formula \
         learning solver is a later slice)"
    ))
}

fn grounding_overrun() -> FaceError {
    FaceError::Unsupported(format!(
        "the L3 grounding exceeds {MAX_GROUND_N_RULES} ground rules (a grounding-memory limit)"
    ))
}

fn stable_overrun(free: usize, rules: usize) -> FaceError {
    FaceError::Unsupported(format!(
        "the relevant Herbrand base has {free} free atoms over {rules} ground rules; \
         stable-model enumeration would exceed the work budget (2^{free} candidates) — \
         abstaining (the unfounded-set propagator + loop-formula certificate are a later slice)"
    ))
}

/// The canonical surface rendering of a ground atom (`pred` or `pred(a,b,…)`) —
/// the deterministic sort key for stable-model output.
fn render_atom(a: &Atom) -> String {
    if a.args.is_empty() {
        a.pred.clone()
    } else {
        let inner: Vec<String> = a.args.iter().map(crate::elab::render).collect();
        format!("{}({})", a.pred, inner.join(","))
    }
}

#[cfg(test)]
mod weak_constraint_tests {
    use super::*;
    use crate::elab::elaborate;
    use crate::parser::parse;

    /// Parse + elaborate + `solve_weak_optimal` in one call — the shape every
    /// test below uses.
    fn opt(src: &str) -> Result<WeakOptimum, FaceError> {
        let prog = parse(src).expect("test program should parse");
        let elab = elaborate(&prog).expect("test program should elaborate");
        solve_weak_optimal(&elab)
    }

    #[test]
    fn no_weak_constraints_is_cost_zero() {
        // degenerate sanity: an L0 program with no weak constraints at all has
        // exactly one (trivially optimal, cost-0) answer set.
        let w = opt("pred p(Int). p(1). p(2).").unwrap();
        assert!(w.consistent);
        assert_eq!(w.cost, Some(0));
        assert_eq!(w.models.len(), 1);
    }

    #[test]
    fn single_weak_constraint_pays_its_weight_when_body_holds() {
        // `a.` is a fact ⇒ always true ⇒ `:~ a. [7@0]` always costs 7 — verified
        // against clingo 5.8.0 as the ground truth for this exact polarity.
        let w = opt("pred a. a. :~ a. [7@0]").unwrap();
        assert_eq!(w.cost, Some(7));
    }

    #[test]
    fn body_never_satisfiable_costs_zero() {
        // `q` never derived by any rule/fact ⇒ `:~ q. […]` never holds in any
        // answer set ⇒ cost is always 0, not an error (an undeclared-but-typed
        // predicate with zero facts is a legal, if vacuous, program).
        let w = opt("pred q. :~ q. [100@0]").unwrap();
        assert_eq!(w.cost, Some(0));
    }

    #[test]
    fn conflicting_weak_constraints_pick_the_cheaper_side() {
        // choose(a) / choose(b) via the even-loop non-stratified idiom
        // (`p :- not q. q :- not p.`) gives two stable models: {a} and {b}.
        // Weak constraints make violating `a` cost 10, violating `b` cost 1 —
        // the optimum must be the {b} model, cost 1, not {a} (cost 10).
        let w = opt(
            "pred a. pred b.
             a :- not b.
             b :- not a.
             :~ a. [10@0]
             :~ b. [1@0]",
        )
        .unwrap();
        assert_eq!(w.cost, Some(1));
        assert_eq!(w.models.len(), 1);
        assert_eq!(w.models[0].len(), 1);
        assert_eq!(w.models[0][0].pred, "b");
    }

    #[test]
    fn tied_optimal_models_are_all_reported() {
        // same shape as above but EQUAL weights ⇒ both {a} and {b} are optimal.
        let w = opt(
            "pred a. pred b.
             a :- not b.
             b :- not a.
             :~ a. [5@0]
             :~ b. [5@0]",
        )
        .unwrap();
        assert_eq!(w.cost, Some(5));
        assert_eq!(w.models.len(), 2);
    }

    #[test]
    fn no_answer_set_is_inconsistent_not_a_cost() {
        // `p :- not p.` (odd loop) has NO stable model — weak constraints don't
        // change that; `consistent` must be false and `cost` must be `None`.
        let w = opt("pred p. p :- not p. :~ p. [1@0]").unwrap();
        assert!(!w.consistent);
        assert_eq!(w.cost, None);
        assert!(w.models.is_empty());
    }

    #[test]
    fn single_level_only_rejects_two_distinct_levels() {
        let err = opt("pred a. pred b. a. b. :~ a. [1@0] :~ b. [1@1]").unwrap_err();
        assert!(matches!(err, FaceError::Unsupported(_)));
    }

    #[test]
    fn single_level_only_accepts_repeated_same_level() {
        // several weak constraints at the SAME level is fine — only >1 DISTINCT
        // level value is rejected.
        assert!(opt("pred a. pred b. a. b. :~ a. [1@0] :~ b. [2@0]").is_ok());
    }

    // --- the dedup / counting rule (the soundness-critical crux of this
    // slice) — each program below was independently run against clingo 5.8.0
    // to establish the expected cost; see the module-level comment above
    // `GroundWeak` for the exact clingo invocations. ---

    #[test]
    fn dedup_same_weight_same_declaration_counts_once() {
        // clingo: `p(1..3). :~ p(X). [5@0].` ⇒ cost 5 (NOT 15).
        let w = opt("pred p(Int). p(1). p(2). p(3). :~ p(X). [5@0]").unwrap();
        assert_eq!(w.cost, Some(5));
    }

    #[test]
    fn dedup_same_weight_different_declarations_counts_once() {
        // clingo: `a. b. :~ a. [5@0]. :~ b. [5@0].` ⇒ cost 5 (NOT 10) — the
        // dedup key is GLOBAL across declarations, not scoped to one `:~`.
        let w = opt("pred a. pred b. a. b. :~ a. [5@0] :~ b. [5@0]").unwrap();
        assert_eq!(w.cost, Some(5));
    }

    #[test]
    fn distinct_weights_sum_normally() {
        // clingo: `p(1..3). :~ p(X). [X@0].` ⇒ cost 6 (1+2+3) — distinct
        // per-instance weights never collide, so no dedup applies and the sum
        // is the naive one. This surface has no variable-weight syntax
        // (`WeightLit` is a literal), so we get the same effect with three
        // separately-weighted declarations instead.
        let w = opt(
            "pred p(Int). p(1). p(2). p(3).
             :~ p(1). [1@0]
             :~ p(2). [2@0]
             :~ p(3). [3@0]",
        )
        .unwrap();
        assert_eq!(w.cost, Some(6));
    }

    // --- grounder hand-verification (the private `ground_weak_constraints` /
    // `weak_cost` — a small program, hand-counted). ---

    #[test]
    fn grounder_produces_one_instance_per_ground_body() {
        let prog = parse("pred p(Int). p(1). p(2). p(3). :~ p(X). [5@0]").unwrap();
        let elab = elaborate(&prog).unwrap();
        let mut intern = Interner::default();
        let model = stratified_model(&elab, &mut intern).unwrap();
        let gw = ground_weak_constraints(&elab, &intern).unwrap();
        // three ground instances (p(1), p(2), p(3)), each weight 5.
        assert_eq!(gw.len(), 3);
        assert!(gw.iter().all(|g| g.weight == 5));
        // all three hold in the (only) model ⇒ weak_cost dedups to 5, not 15.
        assert_eq!(weak_cost(&gw, &model).unwrap(), 5);
    }

    #[test]
    fn grounder_drops_instance_whose_positive_atom_is_never_derivable() {
        // `q` is declared but never a fact/rule head ⇒ never interned ⇒ the
        // ground instance is pruned entirely at grounding time (never even
        // reaches `weak_cost`'s evaluation).
        let prog = parse("pred p. pred q. p. :~ p, q. [1@0]").unwrap();
        let elab = elaborate(&prog).unwrap();
        let mut intern = Interner::default();
        let _ = stratified_model(&elab, &mut intern).unwrap();
        let gw = ground_weak_constraints(&elab, &intern).unwrap();
        assert!(gw.is_empty(), "an instance referencing a never-derivable atom must be pruned");
    }

    #[test]
    fn grounder_neg_atom_never_derivable_holds_by_cwa() {
        // `not q` with `q` never derivable holds trivially (CWA) — so the
        // instance survives grounding with an EMPTY `neg` list (nothing left
        // to falsify it), and its cost is paid whenever the positive part
        // holds.
        let prog = parse("pred p. pred q. p. :~ p, not q. [9@0]").unwrap();
        let elab = elaborate(&prog).unwrap();
        let mut intern = Interner::default();
        let model = stratified_model(&elab, &mut intern).unwrap();
        let gw = ground_weak_constraints(&elab, &intern).unwrap();
        assert_eq!(gw.len(), 1);
        assert!(gw[0].neg.is_empty());
        assert_eq!(weak_cost(&gw, &model).unwrap(), 9);
    }

    #[test]
    fn weak_cost_overflow_abstains_loudly_instead_of_wrapping() {
        // Regression for a confirmed P0: three distinct large declared weights
        // (each individually a legal i64) whose i64 SUM wraps — the exact
        // repro from the finding. Before the fix, `cargo build --release`
        // (this workspace's actual release profile: `lto = "thin"`, no
        // `overflow-checks`) silently produced a wrong, sign-flipped cost;
        // debug instead hard-panicked. Neither is acceptable: this must be a
        // loud `FaceError`, never a wrapped/approximated optimum.
        let err = opt(
            "pred a. pred b. pred c.\n\
             a. b. c.\n\
             :~ a. [4611686018427387903@0]\n\
             :~ b. [4611686018427387904@0]\n\
             :~ c. [4611686018427387905@0]",
        )
        .expect_err("i64-overflowing weight sum must be refused, not wrapped");
        assert!(
            matches!(err, FaceError::Unsupported(_)),
            "overflow must surface as Unsupported (abstain), got {err:?}"
        );
    }

    #[test]
    fn weak_cost_exact_i64_max_boundary_overflow_abstains() {
        // Two DISTINCT declarations (weight is a fixed per-declaration integer
        // literal this slice — never a body variable — so a single `:~` can
        // never itself produce colliding-but-distinct per-instance weights;
        // overflow can only arise across declarations, as here): `i64::MAX`
        // and `1`, both always holding, sum to exactly `i64::MAX + 1` — the
        // textbook wrap-to-`i64::MIN` boundary. Confirms the checked-sum path
        // catches a boundary overflow, not just the deeply-negative one from
        // the P0 repro above.
        let err = opt(&format!("pred a. pred b. a. b. :~ a. [{}@0]\n:~ b. [1@0]", i64::MAX))
            .expect_err("i64::MAX + 1 must be refused, not wrapped to i64::MIN");
        assert!(matches!(err, FaceError::Unsupported(_)));
    }
}

#[cfg(test)]
mod l3_tests {
    use super::*;

    #[test]
    fn well_founded_model_three_way_split() {
        // c.          → c is well-founded TRUE
        // a :- not c. → a is well-founded FALSE (c is true)
        // p :- not q. ┐ even loop → p, q are UNDEFINED
        // q :- not p. ┘
        let (c, a, p, q) = (1u32, 2u32, 3u32, 4u32);
        let mut prog = GroundNProgram::new();
        prog.push(GroundNRule::fact(c));
        prog.push(GroundNRule::rule(a, vec![], vec![c]));
        prog.push(GroundNRule::rule(p, vec![], vec![q]));
        prog.push(GroundNRule::rule(q, vec![], vec![p]));

        let (lo, hi) = well_founded_model(&prog); // (L*, U*)
        assert!(lo.contains(&c), "c is well-founded TRUE (in L*)");
        assert!(!hi.contains(&a), "a is well-founded FALSE (not in U*)");
        for x in [p, q] {
            assert!(!lo.contains(&x) && hi.contains(&x), "{x} is UNDEFINED (U* \\ L*)");
        }
    }
    use crate::program::{GroundNProgram, GroundNRule};

    /// A tiny deterministic PRNG (so the differential is reproducible — no `rand`
    /// dependency, no wall-clock seed).
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            self.0
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// **Empirical soundness + completeness gate** (the keystone, executed against
    /// the *production* `stable_models`, not a model of it): for many random
    /// ground normal programs, the bracketed `L ⊆ M ⊆ U` enumeration must agree
    /// *exactly* with a brute-force `is_stable` sweep over the **entire** Herbrand
    /// base. A bracketing bug that dropped a stable model, or a gate bug that
    /// admitted a non-stable one, fails here.
    #[test]
    fn stable_models_match_brute_force_differential() {
        let mut rng = Lcg(0x1234_5678_9abc_def0);
        for _ in 0..50_000 {
            let n_atoms = 2 + rng.below(4) as u32; // 2..=5 atoms
            let n_rules = 1 + rng.below(8) as usize; // 1..=8 rules
            let mut p = GroundNProgram::new();
            for _ in 0..n_rules {
                let head = rng.below(n_atoms as u64) as AtomId;
                let (mut pos, mut neg) = (Vec::new(), Vec::new());
                for a in 0..n_atoms {
                    match rng.below(5) {
                        0 => pos.push(a),
                        1 => neg.push(a),
                        _ => {} // most atoms absent from any given body
                    }
                }
                p.push(GroundNRule::rule(head, pos, neg));
            }

            // the production bracketed enumeration (small ⇒ never hits the bound).
            let got: BTreeSet<BTreeSet<AtomId>> = stable_models(&p).unwrap().into_iter().collect();

            // the exhaustive oracle over the whole base 2^n_atoms.
            let mut brute = BTreeSet::new();
            for mask in 0u32..(1u32 << n_atoms) {
                let m: BTreeSet<AtomId> = (0..n_atoms).filter(|a| (mask >> a) & 1 == 1).collect();
                if p.is_stable(&m) {
                    brute.insert(m);
                }
            }

            assert_eq!(got, brute, "bracket ≠ brute force for rules {:?}", p.rules);
        }
    }

    /// **Completeness gain of the well-founded bracket.** A program whose
    /// negation resolves only on the *second* alternating-fixpoint iteration:
    /// `c.`; `a_i :- not c.` (each `a_i` is unfounded ⇒ false, since `c` is true);
    /// `b_i :- c, not a_i.` (each `b_i` ⇒ true). The well-founded model decides
    /// EVERY atom (free set empty ⇒ one candidate), but the old one-step reduct
    /// bracket leaves all `2N` of the `a_i`/`b_i` free — exceeding `MAX_STABLE_FREE`
    /// for `N ≥ 13`, i.e. the old path would have abstained. Here `N = 20`
    /// (one-step free = 40) yet the WFM path returns the unique answer set.
    #[test]
    fn well_founded_model_decides_what_one_step_abstains_on() {
        const N: u32 = 20;
        let c = 0u32;
        let a = |i: u32| 1 + i; // a_0..a_{N-1}
        let b = |i: u32| 1 + N + i; // b_0..b_{N-1}
        let mut p = GroundNProgram::new();
        p.push(GroundNRule::fact(c));
        for i in 0..N {
            p.push(GroundNRule::rule(a(i), vec![], vec![c])); // a_i :- not c
            p.push(GroundNRule::rule(b(i), vec![c], vec![a(i)])); // b_i :- c, not a_i
        }

        // the OLD one-step bracket would leave 2N atoms free (→ abstain at N≥13).
        let one_step_lo = p.reduct(&p.heads()).least_model();
        let one_step_hi = p.reduct(&BTreeSet::new()).least_model();
        let one_step_free = one_step_hi.difference(&one_step_lo).count();
        assert_eq!(one_step_free, 2 * N as usize, "one-step bracket leaves 2N free");
        assert!(one_step_free > MAX_STABLE_FREE, "old path would abstain");

        // the WFM bracket decides every atom (free set empty) → the unique model.
        let (wfm_lo, wfm_hi) = well_founded_model(&p);
        assert_eq!(wfm_lo, wfm_hi, "well-founded model is total here (no undefined atoms)");

        let models = stable_models(&p).expect("WFM bracket decides within budget");
        let expected: BTreeSet<AtomId> = std::iter::once(c).chain((0..N).map(b)).collect();
        assert_eq!(models, vec![expected], "the unique answer set {{c, b_0..b_N-1}}");
    }

    /// The bracket is sound on every accepted model: each model the production
    /// path returns satisfies `L ⊆ M ⊆ U` and the GL gate.
    #[test]
    fn returned_models_are_within_bracket_and_stable() {
        let mut rng = Lcg(0xfeed_face_cafe_babe);
        for _ in 0..20_000 {
            let n_atoms = 2 + rng.below(4) as u32;
            let n_rules = 1 + rng.below(7) as usize;
            let mut p = GroundNProgram::new();
            for _ in 0..n_rules {
                let head = rng.below(n_atoms as u64) as AtomId;
                let (mut pos, mut neg) = (Vec::new(), Vec::new());
                for a in 0..n_atoms {
                    match rng.below(5) {
                        0 => pos.push(a),
                        1 => neg.push(a),
                        _ => {}
                    }
                }
                p.push(GroundNRule::rule(head, pos, neg));
            }
            let base = p.heads();
            let lower = p.reduct(&base).least_model();
            let upper = p.reduct(&BTreeSet::new()).least_model();
            for m in stable_models(&p).unwrap() {
                assert!(lower.is_subset(&m) && m.is_subset(&upper), "L ⊆ M ⊆ U violated");
                assert!(p.is_stable(&m), "returned a non-stable model");
            }
        }
    }

    /// **Completeness gain of connected-component decomposition.** `N` independent
    /// even-loops `a_i :- not b_i. b_i :- not a_i.` — global `|FREE| = 2N`. For
    /// `N = 13` the global free set is 26, over `MAX_STABLE_FREE = 24`, so the
    /// monolithic sweep abstains; decomposition solves each 2-atom loop and
    /// cartesian-combines into the `2^13 = 8192` answer sets (under the model cap).
    #[test]
    fn decomposition_decides_what_monolithic_abstains() {
        const N: u32 = 13;
        let mut p = GroundNProgram::new();
        for i in 0..N {
            let (a, b) = (2 * i, 2 * i + 1);
            p.push(GroundNRule::rule(a, vec![], vec![b])); // a_i :- not b_i
            p.push(GroundNRule::rule(b, vec![], vec![a])); // b_i :- not a_i
        }
        // monolithic would abstain (global free = 26 > 24)…
        assert!(well_founded_model(&p).1.len() >= MAX_STABLE_FREE + 1);
        // …but the decomposition decides all 2^N answer sets, each picking one of
        // {a_i, b_i} per loop.
        let models = stable_models(&p).expect("decomposition decides the independent loops");
        assert_eq!(models.len(), 1usize << N, "2^N answer sets (one per loop choice)");
        for m in &models {
            assert!(p.is_stable(m), "every combined model is GL-stable");
            assert_eq!(m.len() as u32, N, "exactly one of each loop pair");
        }
    }

    /// **The decomposition differential** (the keystone for THIS slice). The base
    /// `stable_models_match_brute_force_differential` rarely builds a multi-component
    /// program (its 2–5 atoms usually connect), so it under-exercises the cartesian
    /// path. Here we deliberately generate `k` subprograms over DISJOINT atom
    /// ranges, concatenate them (forcing `k` connected components), and assert the
    /// production decomposition still matches an exhaustive `is_stable` sweep over
    /// the WHOLE base — a partition bug (mixing components), a cartesian bug, or a
    /// monolithic-feasibility-routing bug all fail here.
    #[test]
    fn decomposition_matches_brute_force_differential() {
        let mut rng = Lcg(0x0bad_c0de_dead_beef);
        for _ in 0..15_000 {
            let k = 2 + rng.below(2) as u32; // 2..=3 components
            let per = 2 + rng.below(2) as u32; // 2..=3 atoms each
            let n_atoms = k * per; // ≤ 9 ⇒ brute force ≤ 2^9 (keeps the sweep fast)
            let mut p = GroundNProgram::new();
            for c in 0..k {
                let base = c * per; // this component's disjoint atom range
                let n_rules = 1 + rng.below(4) as usize;
                for _ in 0..n_rules {
                    let head = base + rng.below(per as u64) as AtomId;
                    let (mut pos, mut neg) = (Vec::new(), Vec::new());
                    for off in 0..per {
                        match rng.below(5) {
                            0 => pos.push(base + off),
                            1 => neg.push(base + off),
                            _ => {}
                        }
                    }
                    p.push(GroundNRule::rule(head, pos, neg));
                }
            }

            let got: BTreeSet<BTreeSet<AtomId>> = stable_models(&p).unwrap().into_iter().collect();
            let mut brute = BTreeSet::new();
            for mask in 0u32..(1u32 << n_atoms) {
                let m: BTreeSet<AtomId> = (0..n_atoms).filter(|a| (mask >> a) & 1 == 1).collect();
                if p.is_stable(&m) {
                    brute.insert(m);
                }
            }
            assert_eq!(got, brute, "decomposition ≠ brute force for {:?}", p.rules);
        }
    }

    /// Decomposition must AGREE with the monolithic enumeration on a program small
    /// enough that the monolithic path also runs: three independent loops give
    /// `2^3` models via either route (the cartesian product is the true set).
    #[test]
    fn decomposition_matches_monolithic_on_small_independent_loops() {
        let mut p = GroundNProgram::new();
        for i in 0..3u32 {
            let (a, b) = (2 * i, 2 * i + 1);
            p.push(GroundNRule::rule(a, vec![], vec![b]));
            p.push(GroundNRule::rule(b, vec![], vec![a]));
        }
        let got: BTreeSet<BTreeSet<AtomId>> = stable_models(&p).unwrap().into_iter().collect();
        // brute force over the whole 6-atom base.
        let mut brute = BTreeSet::new();
        for mask in 0u32..(1u32 << 6) {
            let m: BTreeSet<AtomId> = (0..6).filter(|a| (mask >> a) & 1 == 1).collect();
            if p.is_stable(&m) {
                brute.insert(m);
            }
        }
        assert_eq!(got, brute, "decomposition's cartesian == brute force");
        assert_eq!(got.len(), 8);
    }
}

/// The **perfect model** by stratified bottom-up evaluation. Each stratum is
/// solved by the [`GroundProgram`] least-fixpoint, seeded with the frozen lower
/// strata; a `not q` literal becomes a guard against that frozen model (sound
/// because stratification puts `q` strictly lower, so it is fully decided). The
/// shared `intern` is populated for the query / constraint lookups.
fn stratified_model(elab: &Elaborated, intern: &mut Interner) -> Result<BTreeSet<AtomId>, FaceError> {
    let strata = &elab.pred_strata;
    let stratum_of = |p: &str| strata.get(p).copied().unwrap_or(0);
    let max_level = strata.values().copied().max().unwrap_or(0);

    let mut model: BTreeSet<AtomId> = BTreeSet::new();
    for level in 0..=max_level {
        let mut prog = GroundProgram::new();
        // freeze every lower stratum (already in `model`) as a fact.
        for &a in &model {
            prog.push(GroundRule::fact(a));
        }
        // facts whose predicate sits at this stratum.
        for fact in &elab.facts {
            if stratum_of(&fact.pred) == level {
                let id = intern.atom(&fact.pred, &ground_args(fact)?);
                prog.push(GroundRule::fact(id));
            }
        }
        // rules whose head predicate sits at this stratum.
        for rule in &elab.rules {
            if stratum_of(&rule.head.pred) != level {
                continue;
            }
            let vars = rule_vars(rule, &elab.pred_sorts, &elab.ctor_sig);
            for assign in assignments(&vars, &elab.domains)? {
                if !rule_grounds_in_universe(rule, &vars, &assign, elab)? {
                    continue;
                }
                let ints = int_bindings(&vars, &assign)?;
                let mut guard = true;
                for lit in &rule.body {
                    match lit {
                        Literal::Theory(t) => guard &= eval_compare(t, &vars, &assign, &ints)?,
                        Literal::Neg(a) => {
                            // `a`'s predicate is strictly lower ⇒ already decided
                            // in `model`; un-interned ⇒ never derived ⇒ `not a`
                            // holds.
                            let key = instantiate(a, &vars, &assign);
                            if let Some(id) = intern.get(&a.pred, &key) {
                                guard &= !model.contains(&id);
                            }
                        }
                        Literal::Pos(_) => {}
                    }
                    if !guard {
                        break;
                    }
                }
                let head = intern.atom(&rule.head.pred, &instantiate(&rule.head, &vars, &assign));
                let body: Vec<AtomId> = rule
                    .body
                    .iter()
                    .filter_map(as_pos)
                    .map(|b| intern.atom(&b.pred, &instantiate(b, &vars, &assign)))
                    .collect();
                prog.push(GroundRule::rule(head, body, guard));
            }
        }
        model = prog.least_model();
    }
    Ok(model)
}

/// The flat ground program (all facts + all rules, theory guards evaluated) —
/// the base for the **abductive** search, valid only for a negation-free program
/// (where the flat least model equals the perfect model).
fn flat_program(elab: &Elaborated, intern: &mut Interner) -> Result<GroundProgram, FaceError> {
    let mut prog = GroundProgram::new();
    for fact in &elab.facts {
        let id = intern.atom(&fact.pred, &ground_args(fact)?);
        prog.push(GroundRule::fact(id));
    }
    for rule in &elab.rules {
        let vars = rule_vars(rule, &elab.pred_sorts, &elab.ctor_sig);
        for assign in assignments(&vars, &elab.domains)? {
            if !rule_grounds_in_universe(rule, &vars, &assign, elab)? {
                continue;
            }
            let ints = int_bindings(&vars, &assign)?;
            let mut guard = true;
            for lit in &rule.body {
                if let Literal::Theory(t) = lit {
                    guard &= eval_compare(t, &vars, &assign, &ints)?;
                }
            }
            let head = intern.atom(&rule.head.pred, &instantiate(&rule.head, &vars, &assign));
            let body: Vec<AtomId> = rule
                .body
                .iter()
                .filter_map(as_pos)
                .map(|b| intern.atom(&b.pred, &instantiate(b, &vars, &assign)))
                .collect();
            prog.push(GroundRule::rule(head, body, guard));
        }
    }
    Ok(prog)
}

/// The full hypothesis space: every ground instance of every abducible
/// predicate, interned (so it shares ids with the base program), paired with its
/// surface atom.
fn ground_abducibles(
    elab: &Elaborated,
    intern: &mut Interner,
) -> Result<Vec<(AtomId, Atom)>, FaceError> {
    let mut out = Vec::new();
    for pred in &elab.abducibles {
        let sorts = elab.pred_sorts.get(pred).cloned().unwrap_or_default();
        // treat each argument position as a fresh variable of its sort.
        let slots: Vec<(String, String)> =
            sorts.iter().enumerate().map(|(i, s)| (format!("_{i}"), s.clone())).collect();
        for assign in assignments(&slots, &elab.domains)? {
            let id = intern.atom(pred, &assign);
            let args = assign.into_iter().map(AspTerm::Const).collect();
            out.push((id, Atom { pred: pred.clone(), args }));
        }
        if out.len() > MAX_GROUND_ABDUCIBLES {
            return Err(FaceError::Unsupported(format!(
                "the hypothesis space exceeds {MAX_GROUND_ABDUCIBLES} ground abducibles (a grounding-memory limit)"
            )));
        }
    }
    Ok(out)
}

/// A set of ground abducible atom ids — one candidate hypothesis.
type HypSet = BTreeSet<AtomId>;

/// The DoS budget threaded through the backward relevance search. `depth` caps
/// recursion (stack safety); `cands` caps the total hypothesis-sets materialised
/// (the cartesian-product blow-up guard). `truncated` records whether either
/// fired — a sound under-report, surfaced on the answer.
struct Budget {
    depth: u32,
    cands: usize,
    truncated: bool,
}

/// Abduce the ⊆-minimal explanations of a ground goal by **native backward-SLD
/// relevance grounding + forward re-verification** (the AD1 SLD engine's
/// algorithm, ported onto u32 ground atom ids — no `adsmt-core` dependency).
///
/// The backward search ([`backward`]) is an UNTRUSTED candidate *generator*: it
/// chains backward from the goal through the (already-grounded, guard-true) rules
/// to the abducibles reachable from it, proposing hypothesis-sets directly
/// (lifting the old `2^k` subset enumeration's size / count caps). Every proposed
/// set — **including the empty set** — is then RE-VERIFIED by the trusted forward
/// gate (recompute `least_model(base ∪ H)`, check the goal is in it), exactly as
/// the old exhaustive search did. So a relevance-grounder bug can only
/// under-report or be rejected by the gate, never manufacture a false
/// explanation (the soundness firewall is unchanged). The survivors are then
/// ⊆-minimised.
fn abduce(
    base: &GroundProgram,
    ground: &[(AtomId, Atom)],
    g: &Atom,
    intern: &mut Interner,
) -> Result<AbduceAnswer, FaceError> {
    let goal_id = intern.atom(&g.pred, &ground_args(g)?);

    // native indices over the existing ids (no new interning in the search).
    let abducibles: HypSet = ground.iter().map(|(id, _)| *id).collect();
    let mut heads: HashMap<AtomId, Vec<usize>> = HashMap::new();
    for (ri, r) in base.rules.iter().enumerate() {
        if r.guard {
            // guard-FALSE rules never fire (mirror least_model's `guard &&`), so
            // they are excluded from the backward chain too.
            heads.entry(r.head).or_default().push(ri);
        }
    }

    // GENERATE (untrusted, budgeted).
    let mut ctx = Budget { depth: MAX_BACKWARD_DEPTH, cands: MAX_BACKWARD_CANDIDATES, truncated: false };
    let mut visiting: HypSet = BTreeSet::new();
    let raw = backward(goal_id, &mut visiting, &mut ctx, &abducibles, &heads, base);

    // VERIFY through the trusted forward gate (the firewall — the SOLE arbiter;
    // the empty set goes through it too, so `entailed()` is computed, not assumed).
    let mut verified: Vec<HypSet> = Vec::new();
    for h in raw {
        let mut prog = base.clone();
        for &a in &h {
            prog.push(GroundRule::fact(a));
        }
        if prog.least_model().contains(&goal_id) {
            verified.push(h);
        }
    }

    // ⊆-MINIMISE (order-robust antichain) + render ids → surface form.
    let minimal = drop_supersets(verified);
    let id_to_surface: HashMap<AtomId, &Atom> = ground.iter().map(|(id, a)| (*id, a)).collect();
    let mut explanations: Vec<Vec<Atom>> = minimal
        .into_iter()
        .map(|h| h.iter().map(|id| id_to_surface[id].clone()).collect())
        .collect();
    explanations.sort_by_key(Vec::len); // stable smallest-first
    Ok(AbduceAnswer { goal: g.clone(), explanations, truncated: ctx.truncated })
}

/// Backward AND/OR search for the hypothesis-sets that derive `goal`. OR over the
/// ways to reach `goal`: it is itself an abducible (`{goal}`), or the head of a
/// guard-true rule (a fact = empty-body rule ⇒ the empty set; otherwise the
/// resolved body). The `visiting` cycle guard stops re-entering an active goal
/// (termination over the finite ground universe); the budget bounds depth + the
/// total sets materialised.
fn backward(
    goal: AtomId,
    visiting: &mut HypSet,
    ctx: &mut Budget,
    abducibles: &HypSet,
    heads: &HashMap<AtomId, Vec<usize>>,
    base: &GroundProgram,
) -> Vec<HypSet> {
    let mut out: Vec<HypSet> = Vec::new();
    // OR-branch: the goal is directly abducible (tried before the cycle guard).
    if abducibles.contains(&goal) {
        out.push(BTreeSet::from([goal]));
        ctx.cands = ctx.cands.saturating_sub(1);
    }
    if ctx.cands == 0 || ctx.depth == 0 {
        ctx.truncated = true;
        return dedup(out);
    }
    if !visiting.insert(goal) {
        return dedup(out); // cycle: do not re-expand an active goal
    }
    // (depth is decremented in `resolve_body`, once per rule-chain level.)
    for &ri in heads.get(&goal).into_iter().flatten() {
        let body = &base.rules[ri].body;
        if body.is_empty() {
            out.push(BTreeSet::new()); // a fact ⇒ the empty hypothesis set
            ctx.cands = ctx.cands.saturating_sub(1);
        } else if let Some(joint) = resolve_body(body, visiting, ctx, abducibles, heads, base) {
            out.extend(joint);
        }
        if ctx.cands == 0 {
            ctx.truncated = true;
            break;
        }
    }
    visiting.remove(&goal);
    dedup(out)
}

/// Resolve a rule body to its joint hypothesis-sets: the cartesian product over
/// the body atoms' hypothesis-sets, unioned. One unresolvable atom kills the rule
/// (returns `None`). The product is bounded *as it is built* by the candidate
/// budget — the cartesian blow-up guard (a wide all-abducible body is `2ⁿ`).
fn resolve_body(
    body: &[AtomId],
    visiting: &mut HypSet,
    ctx: &mut Budget,
    abducibles: &HypSet,
    heads: &HashMap<AtomId, Vec<usize>>,
    base: &GroundProgram,
) -> Option<Vec<HypSet>> {
    let saved = ctx.depth;
    ctx.depth -= 1;
    let mut joint: Vec<HypSet> = vec![BTreeSet::new()];
    for &b in body {
        let sub = backward(b, visiting, ctx, abducibles, heads, base);
        if sub.is_empty() {
            ctx.depth = saved;
            return None; // an unresolvable body atom ⇒ this rule cannot fire
        }
        let mut next: Vec<HypSet> = Vec::new();
        'product: for j in &joint {
            for s in &sub {
                if ctx.cands == 0 {
                    ctx.truncated = true;
                    break 'product;
                }
                let mut m = j.clone();
                m.extend(s.iter().copied());
                next.push(m);
                ctx.cands -= 1;
            }
        }
        joint = dedup(next);
        if ctx.cands == 0 {
            ctx.truncated = true;
            break;
        }
    }
    ctx.depth = saved;
    Some(joint)
}

/// First-wins collapse of equal hypothesis-sets (`BTreeSet` gives order-free
/// structural equality natively).
fn dedup(v: Vec<HypSet>) -> Vec<HypSet> {
    let mut seen: HashSet<HypSet> = HashSet::new();
    let mut out = Vec::new();
    for s in v {
        if seen.insert(s.clone()) {
            out.push(s);
        }
    }
    out
}

/// Reduce to the ⊆-minimal antichain (drop every set that is a superset of
/// another). **Order-robust** (mirrors adsmt-abduce's `drop_subsumed`): unlike the
/// old generation-order pruning, the backward generator can hand us a minimal set
/// and its superset in any order, so adding `c` both skips it when subsumed by a
/// kept set AND retro-removes kept sets that `c` subsumes. (A verified empty set
/// subsumes everything ⇒ deduction collapses all explanations.)
fn drop_supersets(cands: Vec<HypSet>) -> Vec<HypSet> {
    let mut kept: Vec<HypSet> = Vec::new();
    for c in dedup(cands) {
        if kept.iter().any(|s| s.is_subset(&c)) {
            continue; // c is subsumed by a kept set
        }
        kept.retain(|s| !c.is_subset(s)); // c subsumes these — drop them
        kept.push(c);
    }
    kept
}

#[derive(Default)]
struct Interner {
    map: HashMap<(String, Vec<String>), AtomId>,
    next: AtomId,
}

impl Interner {
    fn atom(&mut self, pred: &str, args: &[String]) -> AtomId {
        let key = (pred.to_string(), args.to_vec());
        if let Some(&id) = self.map.get(&key) {
            return id;
        }
        let id = self.next;
        self.next += 1;
        self.map.insert(key, id);
        id
    }

    fn get(&self, pred: &str, args: &[String]) -> Option<AtomId> {
        self.map.get(&(pred.to_string(), args.to_vec())).copied()
    }

    /// The reverse map id → surface atom (arguments as opaque `Const`s) — for
    /// rendering stable models. A model contains only head atoms, all interned,
    /// so every id it holds is present here.
    fn reverse(&self) -> HashMap<AtomId, Atom> {
        self.map
            .iter()
            .map(|((pred, args), id)| {
                let args = args.iter().cloned().map(AspTerm::Const).collect();
                (*id, Atom { pred: pred.clone(), args })
            })
            .collect()
    }
}

fn as_pos(l: &Literal) -> Option<&Atom> {
    match l {
        Literal::Pos(a) => Some(a),
        Literal::Neg(_) | Literal::Theory(_) => None,
    }
}

fn as_neg(l: &Literal) -> Option<&Atom> {
    match l {
        Literal::Neg(a) => Some(a),
        Literal::Pos(_) | Literal::Theory(_) => None,
    }
}

fn as_theory(l: &Literal) -> Option<&Theory> {
    match l {
        Literal::Theory(t) => Some(t),
        Literal::Pos(_) | Literal::Neg(_) => None,
    }
}

/// The canonical strings of a ground atom's arguments (a fact). Errors on a
/// stray variable (including inside a constructor term).
fn ground_args(atom: &Atom) -> Result<Vec<String>, FaceError> {
    atom.args
        .iter()
        .map(|a| {
            if has_var(a) {
                Err(FaceError::Unsafe("variable in a ground atom".into()))
            } else {
                Ok(crate::elab::render(a))
            }
        })
        .collect()
}

/// Whether a term mentions any variable (including inside a constructor).
fn has_var(t: &AspTerm) -> bool {
    match t {
        AspTerm::Var(_) => true,
        AspTerm::App(_, args) => args.iter().any(has_var),
        _ => false,
    }
}

type CtorSig = HashMap<String, (String, Vec<String>)>;

/// The variables of a rule (head ∪ positive body atoms) in first-occurrence
/// order, with sorts — **descending into constructor patterns** (a variable
/// inside `node(L, R)` is bound at the field sort). Theory atoms reference only
/// already-bound variables.
fn rule_vars(rule: &Rule, pred_sorts: &HashMap<String, Vec<String>>, ctors: &CtorSig) -> Vec<(String, String)> {
    let mut vars: Vec<(String, String)> = Vec::new();
    collect_vars(&rule.head, pred_sorts, ctors, &mut vars);
    for atom in rule.body.iter().filter_map(as_pos) {
        collect_vars(atom, pred_sorts, ctors, &mut vars);
    }
    vars
}

fn collect_vars(
    atom: &Atom,
    pred_sorts: &HashMap<String, Vec<String>>,
    ctors: &CtorSig,
    out: &mut Vec<(String, String)>,
) {
    let Some(sorts) = pred_sorts.get(&atom.pred) else { return };
    for (arg, sort) in atom.args.iter().zip(sorts) {
        collect_term_vars(arg, sort, ctors, out);
    }
}

/// Collect a term's variables (descending into constructor patterns), each at
/// its sort (a pattern variable's sort is the constructor's field sort).
fn collect_term_vars(t: &AspTerm, sort: &str, ctors: &CtorSig, out: &mut Vec<(String, String)>) {
    match t {
        AspTerm::Var(v) => {
            if !out.iter().any(|(n, _)| n == v) {
                out.push((v.clone(), sort.to_string()));
            }
        }
        AspTerm::App(c, args) => {
            if let Some((_, fields)) = ctors.get(c) {
                for (a, fs) in args.iter().zip(fields) {
                    collect_term_vars(a, fs, ctors, out);
                }
            }
        }
        _ => {}
    }
}

/// The matching filter: every constructor-pattern argument of `atom`,
/// instantiated under the assignment, must be an appearing universe term of the
/// argument's sort. (A whole-term variable / constant / literal is always a
/// universe element.)
fn atom_in_universe(
    atom: &Atom,
    vars: &[(String, String)],
    assign: &[String],
    pred_sorts: &HashMap<String, Vec<String>>,
    domains: &HashMap<String, Vec<String>>,
) -> bool {
    let Some(sorts) = pred_sorts.get(&atom.pred) else { return true };
    for (arg, sort) in atom.args.iter().zip(sorts) {
        if matches!(arg, AspTerm::App(..)) {
            let s = instantiate_term(arg, vars, assign);
            if !domains.get(sort).is_some_and(|d| d.contains(&s)) {
                return false;
            }
        }
    }
    true
}

/// Whether a rule **head** constructs a ground constructor term outside the
/// finite (appearing-terms) universe. A head constructor-app argument all of
/// whose variables are bound by a *positive body* atom is a **construction** (its
/// value is determined by the body, not a universe-ranging pattern); if that
/// ground term is absent from the sort's domain, the appearing-terms grounder
/// would silently drop a *derived* atom — soundness-fatal — so the caller
/// abstains loudly. A universe-ranging **pattern** head (a head-only / mixed
/// ctor variable, as in `member(X, cons(X, T))`) is *not* a construction: it
/// stays correctly range-restricted to appearing terms (a sound drop).
fn head_constructs_escaping_term(
    rule: &Rule,
    vars: &[(String, String)],
    assign: &[String],
    elab: &Elaborated,
) -> bool {
    // the variables determined by the positive body.
    let mut body_vars: Vec<(String, String)> = Vec::new();
    for a in rule.body.iter().filter_map(as_pos) {
        collect_vars(a, &elab.pred_sorts, &elab.ctor_sig, &mut body_vars);
    }
    let Some(sorts) = elab.pred_sorts.get(&rule.head.pred) else { return false };
    for (arg, sort) in rule.head.args.iter().zip(sorts) {
        if !matches!(arg, AspTerm::App(..)) {
            continue;
        }
        let mut tvars: Vec<(String, String)> = Vec::new();
        collect_term_vars(arg, sort, &elab.ctor_sig, &mut tvars);
        // a construction: every variable of the ctor term is positive-body-bound
        // (a fully ground head ctor term is seeded at elaboration, so it is
        // already in the universe and never reaches this branch).
        let constructed =
            !tvars.is_empty() && tvars.iter().all(|(n, _)| body_vars.iter().any(|(b, _)| b == n));
        if constructed {
            let ground = instantiate_term(arg, vars, assign);
            if !elab.domains.get(sort).is_some_and(|d| d.contains(&ground)) {
                return true;
            }
        }
    }
    false
}

/// The universe filter for one ground rule instance, split by soundness
/// direction. A positive **body** atom outside the universe ⇒ this instance
/// cannot fire (`Ok(false)`, a sound drop — the pattern matches nothing). A
/// **head** outside the universe is a range-restricted pattern (`Ok(false)`,
/// also sound) UNLESS it *constructs* a term escaping the finite universe — that
/// would silently drop a derived atom (soundness-fatal), so abstain (`Err`).
/// Otherwise the instance grounds (`Ok(true)`).
fn rule_grounds_in_universe(
    rule: &Rule,
    vars: &[(String, String)],
    assign: &[String],
    elab: &Elaborated,
) -> Result<bool, FaceError> {
    if !rule
        .body
        .iter()
        .filter_map(as_pos)
        .all(|a| atom_in_universe(a, vars, assign, &elab.pred_sorts, &elab.domains))
    {
        return Ok(false);
    }
    if !atom_in_universe(&rule.head, vars, assign, &elab.pred_sorts, &elab.domains) {
        if head_constructs_escaping_term(rule, vars, assign, elab) {
            return Err(FaceError::Unsupported(
                "a rule head constructs a datatype term outside the finite term universe \
                 (seed it via a fact, or term construction is a later slice)"
                    .into(),
            ));
        }
        return Ok(false);
    }
    Ok(true)
}

/// All variable assignments over the finite domains, as const-tuples aligned
/// with `vars`. An empty domain for any variable yields no assignments.
///
/// The cartesian product `∏ |domain(sort)|` is **pre-checked against
/// [`MAX_GROUNDING_ASSIGNMENTS`] before materialising** — a wide-arity rule over
/// a large domain would otherwise eagerly allocate gigabytes of `Vec<String>`
/// before any output-count guard could fire (the bound must measure the *input*
/// product, not the output rules). Over budget ⇒ a loud, sound abstain.
fn assignments(
    vars: &[(String, String)],
    domains: &HashMap<String, Vec<String>>,
) -> Result<Vec<Vec<String>>, FaceError> {
    let mut card: u128 = 1;
    for (_, sort) in vars {
        let n = domains.get(sort).map(Vec::len).unwrap_or(0) as u128;
        card = card.saturating_mul(n);
    }
    if card > MAX_GROUNDING_ASSIGNMENTS {
        return Err(FaceError::Unsupported(format!(
            "grounding would enumerate {card} variable assignments (over {MAX_GROUNDING_ASSIGNMENTS}); \
             a grounding-memory limit — reduce the rule arity or the domain size"
        )));
    }
    let mut acc: Vec<Vec<String>> = vec![Vec::new()];
    for (_, sort) in vars {
        let domain = domains.get(sort).map(Vec::as_slice).unwrap_or(&[]);
        let mut next = Vec::new();
        for partial in &acc {
            for c in domain {
                let mut p = partial.clone();
                p.push(c.clone());
                next.push(p);
            }
        }
        acc = next;
    }
    Ok(acc)
}

/// Instantiate an atom's arguments under a variable assignment → ground
/// constants.
fn instantiate(atom: &Atom, vars: &[(String, String)], assign: &[String]) -> Vec<String> {
    atom.args.iter().map(|a| instantiate_term(a, vars, assign)).collect()
}

/// Render a term under a variable assignment to its canonical ground string
/// (substituting whole-term variables; recursing through constructors).
fn instantiate_term(t: &AspTerm, vars: &[(String, String)], assign: &[String]) -> String {
    match t {
        AspTerm::Const(c) => c.clone(),
        AspTerm::Int(n) => n.to_string(),
        AspTerm::Var(v) => {
            let p = vars.iter().position(|(n, _)| n == v).expect("var bound");
            assign[p].clone()
        }
        AspTerm::App(c, args) => {
            let inner: Vec<String> = args.iter().map(|a| instantiate_term(a, vars, assign)).collect();
            format!("{c}({})", inner.join(","))
        }
    }
}

/// Instantiate a (possibly non-ground) abductive goal atom under a variable
/// assignment → a ground atom whose arguments are the canonical rendered values
/// (each an opaque `Const`, so [`abduce`]'s `ground_args` re-renders them to the
/// same interning keys the hypothesis space uses).
fn instantiate_goal_atom(g: &Atom, vars: &[(String, String)], assign: &[String]) -> Atom {
    Atom {
        pred: g.pred.clone(),
        args: g.args.iter().map(|a| AspTerm::Const(instantiate_term(a, vars, assign))).collect(),
    }
}

/// The integer values of the `Int`-sorted variables under an assignment (for
/// the theory evaluation). The elaborator guarantees `Int` domain values are
/// integer literals, so the parse cannot fail in a well-formed program.
fn int_bindings(vars: &[(String, String)], assign: &[String]) -> Result<HashMap<String, i64>, FaceError> {
    let mut m = HashMap::new();
    for ((name, sort), val) in vars.iter().zip(assign) {
        if sort == crate::elab::INT {
            let n = val
                .parse::<i64>()
                .map_err(|_| FaceError::Unsupported(format!("non-integer `Int` value `{val}`")))?;
            m.insert(name.clone(), n);
        }
    }
    Ok(m)
}

/// Evaluate a ground comparison guard, routed by **CanEq** sort (the elaborator
/// validated it): an `Int` comparison is evaluated arithmetically; a non-`Int`
/// `=`/`!=` is evaluated as **structural (dis)equality** of the operands'
/// canonical renderings (= EUF on the finite ground universe).
fn eval_compare(
    t: &Theory,
    vars: &[(String, String)],
    assign: &[String],
    ints: &HashMap<String, i64>,
) -> Result<bool, FaceError> {
    use crate::ast::CmpOp::*;
    if operand_is_int(&t.lhs, vars) && operand_is_int(&t.rhs, vars) {
        let l = eval_int(&t.lhs, ints)?;
        let r = eval_int(&t.rhs, ints)?;
        return Ok(match t.op {
            Lt => l < r,
            Le => l <= r,
            Eq => l == r,
            Ne => l != r,
            Gt => l > r,
            Ge => l >= r,
        });
    }
    // structural equality at a non-Int sort; the elaborator guarantees `=`/`!=`.
    let l = instantiate_expr(&t.lhs, vars, assign);
    let r = instantiate_expr(&t.rhs, vars, assign);
    match t.op {
        Eq => Ok(l == r),
        Ne => Ok(l != r),
        _ => Err(FaceError::Unsupported("ordering on a non-Int sort".into())),
    }
}

/// Whether a comparison operand is `Int`-sorted (so the comparison is
/// arithmetic): a literal / `+`/`-`/`*` always is; a constant / ctor app never
/// is; a variable is iff it was bound at sort `Int`.
fn operand_is_int(e: &Expr, vars: &[(String, String)]) -> bool {
    match e {
        Expr::Lit(_) | Expr::Add(..) | Expr::Sub(..) | Expr::Mul(..) => true,
        Expr::Const(_) | Expr::App(..) => false,
        Expr::Var(v) => vars.iter().any(|(n, s)| n == v && s == crate::elab::INT),
    }
}

/// Render a ground comparison operand to its canonical string under the
/// assignment (the structural-equality key). Arithmetic cannot appear in a
/// non-`Int` comparison (CanEq guarantees it), so those arms are unreachable.
fn instantiate_expr(e: &Expr, vars: &[(String, String)], assign: &[String]) -> String {
    match e {
        Expr::Lit(n) => n.to_string(),
        Expr::Const(c) => c.clone(),
        Expr::Var(v) => {
            let p = vars.iter().position(|(n, _)| n == v).expect("comparison var bound");
            assign[p].clone()
        }
        Expr::App(c, args) => {
            let inner: Vec<String> = args.iter().map(|a| instantiate_expr(a, vars, assign)).collect();
            format!("{c}({})", inner.join(","))
        }
        Expr::Add(..) | Expr::Sub(..) | Expr::Mul(..) => {
            unreachable!("arithmetic operand in a non-Int comparison")
        }
    }
}

/// Evaluate a ground integer expression, with **checked** arithmetic — an
/// overflow is reported (a sound abstain), never a wrapped wrong value.
/// A constant / ctor operand cannot reach here (CanEq keeps arithmetic `Int`).
fn eval_int(e: &Expr, ints: &HashMap<String, i64>) -> Result<i64, FaceError> {
    let overflow = || FaceError::Unsupported("integer overflow in a theory atom".into());
    match e {
        Expr::Lit(n) => Ok(*n),
        Expr::Var(v) => ints
            .get(v)
            .copied()
            .ok_or_else(|| FaceError::Unsafe(format!("unbound theory variable `{v}`"))),
        Expr::Add(a, b) => eval_int(a, ints)?.checked_add(eval_int(b, ints)?).ok_or_else(overflow),
        Expr::Sub(a, b) => eval_int(a, ints)?.checked_sub(eval_int(b, ints)?).ok_or_else(overflow),
        Expr::Mul(a, b) => eval_int(a, ints)?.checked_mul(eval_int(b, ints)?).ok_or_else(overflow),
        Expr::Const(c) => Err(FaceError::Unsupported(format!("constant `{c}` in an arithmetic operand"))),
        Expr::App(c, _) => {
            Err(FaceError::Unsupported(format!("constructor `{c}` in an arithmetic operand")))
        }
    }
}
