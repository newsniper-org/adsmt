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
    /// set). See [`StableModels`].
    pub stable: Option<StableModels>,
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

/// Solve the elaborated program: route on its [`Stratification`] —
/// `Stratified` ⇒ the L0–L2 perfect-model path (unchanged); `NonStratified` ⇒
/// the L3 stable-model gate.
pub fn solve(elab: &Elaborated) -> Result<Solution, FaceError> {
    match &elab.stratify {
        Stratification::Stratified(_) => solve_stratified(elab),
        Stratification::NonStratified(_) => solve_stable(elab),
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

    Ok(Solution { answers, abductions, consistent, stable: None })
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
fn solve_stable(elab: &Elaborated) -> Result<Solution, FaceError> {
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

    // enumerate + gate, then keep only the constraint-consistent answer sets.
    let mut models: Vec<BTreeSet<AtomId>> = Vec::new();
    for m in stable_models(&p)? {
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
    let mut answers = Vec::with_capacity(elab.queries.len());
    for q in &elab.queries {
        let mut vars = Vec::new();
        collect_vars(q, &elab.pred_sorts, &elab.ctor_sig, &mut vars);
        let mut tuples = Vec::new();
        if !models.is_empty() {
            for assign in assignments(&vars, &elab.domains)? {
                if !atom_in_universe(q, &vars, &assign, &elab.pred_sorts, &elab.domains) {
                    continue;
                }
                let key = instantiate(q, &vars, &assign);
                // an un-interned atom is in no model ⇒ not cautious-entailed.
                if let Some(id) = intern.get(&q.pred, &key)
                    && models.iter().all(|m| m.contains(&id))
                {
                    tuples.push(assign);
                }
            }
        }
        answers.push(QueryAnswer {
            query: q.clone(),
            vars: vars.into_iter().map(|(n, _)| n).collect(),
            tuples,
            mode: Entailment::Cautious,
        });
    }

    Ok(Solution {
        answers,
        abductions: Vec::new(),
        consistent,
        stable: Some(StableModels { models: surface }),
    })
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

/// Enumerate the stable models of a ground normal program by **bounded
/// guess-and-check**. Two sound (completeness-preserving) prunings bracket the
/// search: the heads-only base `B` (every stable `M ⊆ B`, since `least_model`
/// only inserts heads) and the monotone bracket `L ⊆ M ⊆ U` —
/// `L = least_model(reduct(B))` (every negation-guarded rule dropped, the
/// forced-in atoms) and `U = least_model(reduct(∅))` (the classical upper bound).
/// Both follow from the rule-set monotonicity of the reduct + the lfp, so no
/// stable model is skipped. Each subset of the free atoms `U \ L` is gated by the
/// trusted [`GroundNProgram::is_stable`].
///
/// `Ok(vec)` is the complete (within-budget) set of stable models — an empty vec
/// is the **sound "no answer set"** verdict. Over the work budget it is instead a
/// loud `Err(Unsupported)` (the clasp/loop-formula solver is a later slice), so a
/// caller can never confuse an abstain (`Err`) with "no answer set" (`Ok([])`).
fn stable_models(p: &GroundNProgram) -> Result<Vec<BTreeSet<AtomId>>, FaceError> {
    let base = p.heads();
    // monotone bracket (both via the trusted lfp): L forced-in, U the upper bound.
    let lower = p.reduct(&base).least_model();
    let upper = p.reduct(&BTreeSet::new()).least_model();
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
mod l3_tests {
    use super::*;
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
