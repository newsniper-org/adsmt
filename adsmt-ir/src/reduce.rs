//! Reduction (WHNF) and definitional equality (convertibility).
//!
//! The kernel's notion of "equal types" is **convertibility**: two terms
//! are interchangeable iff they reduce to a common form under β (apply a
//! λ), ζ (unfold a `let`), and δ (unfold a `def` constant — *never* an
//! `open` one). η is intentionally omitted in this first cut: omitting it
//! is *sound* (it only makes the checker reject a few more terms, which
//! the prime directive prefers over accepting a wrong one). See
//! `DESIGN.md`.

use crate::env::{Decl, Env, Modality};
use crate::term::{Term, TermKind, as_const_app, collect_spine, peel_all_pis, shift, subst_top};
use crate::theory;

/// The folded result, unless writing that name back into the head-reduction
/// loop would restart it.
///
/// A fold emits a CONSTANT and continues; the δ arm unfolds any `Def` constant
/// and continues. If the emitted name is a `Def`, those two form a cycle and
/// `whnf` — which has no fuel and no visited set — never returns. `define`
/// refuses numeral-spelled names precisely so this cannot be set up through a
/// checked admitter, but `Env::declare` is `pub` and documented as unchecked,
/// so the loop guards itself rather than trusting how its env was built.
fn fold_to(env: &Env, name: impl AsRef<str>) -> Option<Term> {
    let name = name.as_ref();
    match env.lookup(name) {
        Some(Decl { modality: Modality::Def(_), .. }) => None,
        _ => Some(Term::cnst(name)),
    }
}

/// Is `name` bound in this environment as an OPAQUE constant?
///
/// The folds are gated on this. `ite`, `true`, `false` and `=` are names the
/// KERNEL never declares — a face installs them — so folding on the spelling
/// alone gave δ-content to symbols the kernel has no claim over: a caller with
/// its own 4-ary `ite`, or its own constant named `true`, would have had its
/// applications rewritten. (Postulating them in the kernel prelude was tried
/// and refused: it breaks both faces on a duplicate declaration and destroyed
/// 112 of 246 corpus verdicts.) Requiring the name to be a declared opaque
/// constant is the narrow version: a face that installs the prelude gets the
/// folds, and one that does not, or that binds the name to something else,
/// stays stuck instead.
/// Is `t` a well-formed TYPE in the empty context? Used to check `ite`'s first
/// argument really is the type argument the prelude's `Π(T:Type0)` promises.
fn infer_univ_ok(env: &Env, t: &Term) -> bool {
    crate::check::infer_univ(env, &crate::check::Ctx::new(), t).is_ok()
}

fn is_open_const(env: &Env, name: &str) -> bool {
    matches!(env.lookup(name), Some(Decl { modality: Modality::Open, .. }))
}

fn as_int_literal(t: &Term) -> Option<i128> {
    match t.kind() {
        TermKind::Const(s) => s.parse::<i128>().ok(),
        _ => None,
    }
}

/// Weak-head normal form: reduce the **head** under β, ζ, δ, ι (`Elim` /
/// `Match` on a constructor), and μ (a guarded `Fix` applied with its
/// recursive argument in constructor form) until it is a sort, a variable,
/// an `open`/inductive/ctor constant, a λ/Π, a bare `Fix`, or a stuck
/// application/eliminator. Arguments are left unreduced (that is what
/// "weak" means); [`is_def_eq`] recurses into them congruently.
///
/// Termination is enforced, not assumed. The old argument — "`def` bodies are
/// non-recursive (head-δ cannot loop) and every admitted `Fix` passed
/// `guard::guard_ok`" — is true of every environment built through the checked
/// admitters, and `Env::declare` is `pub` and documented as unchecked, so it is
/// not true of every environment. It was measurably false in this workspace:
/// the lu-kb face admitted a mutual `fn` group through the raw `declare`, and
/// `f x = g x`, `g x = f x` made this function spin forever (a flat δ/β cycle,
/// no stack growth) while `f x = g x + 1` blew the stack at ~3850 frames.
///
/// So the loop refuses a δ step that cannot make progress: see
/// [`ReductionPath`]. A term that reappears on the path is returned STUCK,
/// which is the honest answer — `f c` above has no weak head normal form, and
/// no reduction strategy can invent one. Callers see an un-reduced term, which
/// costs completeness (a conversion may answer "not equal" where a terminating
/// reduction would have said equal) and never soundness. A depth cap backstops
/// the stack for a term that is deep without being cyclic.
///
/// **Memoized** (the §8 conversion cache): `whnf` is a pure function of the
/// env-*state* and `t`, so the result is cached on `env` keyed by the
/// hash-consed handle `t` (the env clears its memo on every state mutation, so
/// a hit is always valid for the current state). The inner recursion calls the
/// *memoized* `whnf`, so repeated sub-terms (ubiquitous prelude lemmas) are
/// normalized once.
pub fn whnf(env: &Env, t: &Term) -> Term {
    if let Some(cached) = env.memo_whnf_get(t) {
        return cached;
    }
    let depth = ReductionPath::depth();
    if depth >= MAX_WHNF_DEPTH {
        // Not a cycle, just deeper than the stack can carry. Same honest
        // answer, same refusal to cache it.
        ReductionPath::note_cut();
        return t.clone();
    }
    let cuts_before = ReductionPath::cuts();
    ReductionPath::set_depth(depth + 1);
    let result = whnf_uncached(env, t);
    ReductionPath::set_depth(depth);
    // A result computed while some reduction below was cut short is NOT the
    // weak head normal form of `t`; caching it would make the truncation
    // permanent for the rest of the session, and visible to callers that were
    // nowhere near the cut.
    if ReductionPath::cuts() == cuts_before {
        env.memo_whnf_put(t, &result);
    }
    result
}

/// How deep `whnf` may nest before it stops rather than overflow the stack.
///
/// The cycle check below is what actually decides termination; this is the
/// backstop for a term that is *deep* without being cyclic. Measured headroom:
/// the observed overflow sat at ~3850 nested frames on an 8 MiB stack, so 512
/// leaves roughly a 7x margin, and the deepest reduction anywhere in the
/// 246-file corpus is orders of magnitude below it.
const MAX_WHNF_DEPTH: u32 = 512;

thread_local! {
    /// Terms whose head reduction is IN PROGRESS on this thread, across every
    /// nested `whnf` frame. Membership is the cycle test.
    static PATH: std::cell::RefCell<std::collections::HashSet<Term>> =
        std::cell::RefCell::new(std::collections::HashSet::new());
    static PATH_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
    static PATH_CUTS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// The in-progress reduction path, and the RAII handle that keeps it accurate.
///
/// `whnf_uncached` reaches its terminal cases through a dozen early `return`s,
/// so the pops happen in `Drop` rather than at each exit. Terms are hash-consed:
/// `Hash` reads a precomputed `u64` and `PartialEq` is `Arc::ptr_eq`, so both
/// the insert and the lookup are O(1) with no structural traversal.
///
/// Identity is the whole TERM, not the constant being unfolded. That
/// distinction matters: `f (f 1)` legitimately reduces `f` twice on one path
/// and must not be mistaken for a cycle, while `f c → g c → f c` returns to a
/// term it is already reducing and genuinely cannot terminate.
struct ReductionPath {
    pushed: Vec<Term>,
}

impl ReductionPath {
    fn new() -> Self {
        Self { pushed: Vec::new() }
    }

    /// Register `t` as being reduced on this path. `false` means it already
    /// was — the reduction has returned to itself and cannot make progress.
    fn enter(&mut self, t: &Term) -> bool {
        let fresh = PATH.with(|p| p.borrow_mut().insert(t.clone()));
        if fresh {
            self.pushed.push(t.clone());
        }
        fresh
    }

    fn depth() -> u32 {
        PATH_DEPTH.with(|c| c.get())
    }

    fn set_depth(d: u32) {
        PATH_DEPTH.with(|c| c.set(d));
    }

    fn cuts() -> u64 {
        PATH_CUTS.with(|c| c.get())
    }

    fn note_cut() {
        PATH_CUTS.with(|c| c.set(c.get().wrapping_add(1)));
    }
}

/// How many reductions this thread has CUT SHORT so far — a monotone counter,
/// meaningful only as a before/after comparison.
///
/// A cut leaves a term un-reduced, and a consumer that turns an un-reduced term
/// into an uninterpreted symbol has silently dropped the definition's meaning.
/// Dropping meaning preserves `unsat` and destroys `sat`, so such a consumer
/// must abstain rather than answer. `adsmt-ir-lower` brackets its `whnf` call
/// with this and refuses to lower a term whose reduction was cut.
pub fn reduction_cuts() -> u64 {
    ReductionPath::cuts()
}

impl Drop for ReductionPath {
    fn drop(&mut self) {
        PATH.with(|p| {
            let mut p = p.borrow_mut();
            for t in &self.pushed {
                p.remove(t);
            }
        });
    }
}

/// Can `t` be the point a reduction cycles back to?
///
/// A sort, a de Bruijn index, a λ, a Π and a bare `fix` are already
/// weak-head-normal: the loop returns on them without stepping, so they can
/// never recur. Registering them on the path is pure overhead, and this is the
/// hot case — the corpus reaches a normal form in one or two steps.
fn may_recur(t: &Term) -> bool {
    !matches!(
        t.kind(),
        TermKind::Sort(_)
            | TermKind::Bound(_)
            | TermKind::Lam(_, _)
            | TermKind::Pi(_, _)
            | TermKind::Fix { .. }
    )
}

/// The uncached weak-head reduction loop behind [`whnf`].
fn whnf_uncached(env: &Env, t: &Term) -> Term {
    let mut path = ReductionPath::new();
    let mut cur = t.clone();
    // The FIRST term is not registered: a cycle needs at least one step, so it
    // can only be detected on a later iteration (or by a nested frame, which
    // sees the terms this one registered). Skipping it takes the tracking off
    // the overwhelmingly common one-step reduction entirely.
    let mut stepped = false;
    loop {
        if stepped && may_recur(&cur) && !path.enter(&cur) {
            ReductionPath::note_cut();
            return cur.clone();
        }
        stepped = true;
        // Each head-reduction arm computes the *next* term to keep reducing
        // (`next`); the terminal arms (no head step possible) early-`return`.
        // The match only borrows `cur` (via `kind()`), so the reassignment
        // `cur = next` happens strictly after the match has ended.
        let next = match cur.kind() {
            // ζ: let _ := val in body
            TermKind::Let(_, val, body) => subst_top(body, val),
            // δ: unfold a `def` constant; everything else opaque
            TermKind::Const(name) => match env.lookup(name) {
                Some(Decl { modality: Modality::Def(body), .. }) => body.clone(),
                _ => return cur.clone(),
            },
            // ι: recursor on a constructor target
            TermKind::Elim(ind, motive, minors, major) => {
                match iota_elim(env, ind, motive, minors, major) {
                    Some(reduced) => reduced,
                    None => {
                        return Term::elim(
                            ind.clone(),
                            motive.clone(),
                            minors.clone(),
                            whnf(env, major),
                        );
                    }
                }
            }
            // ι: case analysis on a constructor target (no recursion)
            TermKind::Match(ind, motive, minors, major) => {
                match iota_match(env, ind, minors, major) {
                    Some(reduced) => reduced,
                    None => {
                        return Term::mtch(
                            ind.clone(),
                            motive.clone(),
                            minors.clone(),
                            whnf(env, major),
                        );
                    }
                }
            }
            // ι: mutual recursor on a constructor target — dispatch each
            // recursive sub-call to its own group member's recursor.
            TermKind::MutElim(member, motives, minors, major) => {
                match iota_mutelim(env, member, motives, minors, major) {
                    Some(reduced) => reduced,
                    None => {
                        return Term::mutelim(
                            member.clone(),
                            motives.clone(),
                            minors.clone(),
                            whnf(env, major),
                        );
                    }
                }
            }
            TermKind::App(..) => {
                let (head, args) = collect_spine(&cur);
                let whead = whnf(env, &head);
                if let TermKind::Const(name) = whead.kind() {
                    // `ite T c a b` — and only when the face actually installed
                    // `ite`/`true`/`false`, and `T` really is a type.
                    if name == "ite"
                        && args.len() == 4
                        && is_open_const(env, "ite")
                        && is_open_const(env, "true")
                        && is_open_const(env, "false")
                        && matches!(infer_univ_ok(env, &args[0]), true)
                    {
                        let c = whnf(env, &args[1]);
                        if let TermKind::Const(cn) = c.kind() {
                            if cn == "true" {
                                cur = args[2].clone();
                                continue;
                            } else if cn == "false" {
                                cur = args[3].clone();
                                continue;
                            }
                        }
                    }
                    // `=` is POLYMORPHIC: args[0] is the type. Folding without
                    // reading it decided equality of two opaque constants by
                    // their spelling — `whnf((= S "1" "2"))` returned `false`
                    // for an uninterpreted `S`. The numeral convention only
                    // licenses the fold at an arithmetic sort.
                    if name == "="
                        && args.len() == 3
                        && is_open_const(env, "=")
                        && matches!(args[0].kind(), TermKind::Const(c) if c == theory::INT)
                    {
                        let a = whnf(env, &args[1]);
                        let b = whnf(env, &args[2]);
                        if let (Some(x), Some(y)) = (as_int_literal(&a), as_int_literal(&b)) {
                            if let Some(k) = fold_to(env, if x == y { "true" } else { "false" }) {
                                cur = k;
                                continue;
                            }
                        }
                    }
                    if name == theory::INT_LT && args.len() == 2 {
                        let a = whnf(env, &args[0]);
                        let b = whnf(env, &args[1]);
                        if let (Some(x), Some(y)) = (as_int_literal(&a), as_int_literal(&b)) {
                            if let Some(k) = fold_to(env, if x < y { "true" } else { "false" }) {
                                cur = k;
                                continue;
                            }
                        }
                    }
                    if name == theory::INT_LE && args.len() == 2 {
                        let a = whnf(env, &args[0]);
                        let b = whnf(env, &args[1]);
                        if let (Some(x), Some(y)) = (as_int_literal(&a), as_int_literal(&b)) {
                            if let Some(k) = fold_to(env, if x <= y { "true" } else { "false" }) {
                                cur = k;
                                continue;
                            }
                        }
                    }
                    if name == theory::INT_GT && args.len() == 2 {
                        let a = whnf(env, &args[0]);
                        let b = whnf(env, &args[1]);
                        if let (Some(x), Some(y)) = (as_int_literal(&a), as_int_literal(&b)) {
                            if let Some(k) = fold_to(env, if x > y { "true" } else { "false" }) {
                                cur = k;
                                continue;
                            }
                        }
                    }
                    if name == theory::INT_GE && args.len() == 2 {
                        let a = whnf(env, &args[0]);
                        let b = whnf(env, &args[1]);
                        if let (Some(x), Some(y)) = (as_int_literal(&a), as_int_literal(&b)) {
                            if let Some(k) = fold_to(env, if x >= y { "true" } else { "false" }) {
                                cur = k;
                                continue;
                            }
                        }
                    }
                    if name == theory::INT_ADD && args.len() == 2 {
                        let a = whnf(env, &args[0]);
                        let b = whnf(env, &args[1]);
                        if let (Some(x), Some(y)) = (as_int_literal(&a), as_int_literal(&b)) {
                            if let Some(sum) = x.checked_add(y) {
                                if let Some(k) = fold_to(env, sum.to_string()) {
                                    cur = k;
                                    continue;
                                }
                            }
                        }
                    }
                    if name == theory::INT_SUB && args.len() == 2 {
                        let a = whnf(env, &args[0]);
                        let b = whnf(env, &args[1]);
                        if let (Some(x), Some(y)) = (as_int_literal(&a), as_int_literal(&b)) {
                            if let Some(diff) = x.checked_sub(y) {
                                if let Some(k) = fold_to(env, diff.to_string()) {
                                    cur = k;
                                    continue;
                                }
                            }
                        }
                    }
                    if name == theory::INT_NEG && args.len() == 1 {
                        let a = whnf(env, &args[0]);
                        if let Some(x) = as_int_literal(&a) {
                            if let Some(neg) = x.checked_neg() {
                                if let Some(k) = fold_to(env, neg.to_string()) {
                                    cur = k;
                                    continue;
                                }
                            }
                        }
                    }
                }
                match whead.kind() {
                    // β: apply the first argument, re-apply the rest
                    TermKind::Lam(_, body) => {
                        Term::apps(subst_top(body, &args[0]), args[1..].to_vec())
                    }
                    // μ: a fix whose recursive argument is a constructor
                    TermKind::Fix { rec_arg, ty, body } if args.len() > *rec_arg => {
                        let rec_arg = *rec_arg;
                        let ra = whnf(env, &args[rec_arg]);
                        let is_ctor =
                            as_const_app(&ra).is_some_and(|(h, _)| env.ctor_of(&h).is_some());
                        if is_ctor {
                            let the_fix = Term::fix(rec_arg, ty.clone(), body.clone());
                            Term::apps(subst_top(body, &the_fix), args)
                        } else {
                            let mut args = args;
                            args[rec_arg] = ra;
                            return Term::apps(Term::fix(rec_arg, ty.clone(), body.clone()), args);
                        }
                    }
                    _ => return Term::apps(whead, args),
                }
            }
            _ => return cur.clone(),
        };
        cur = next;
    }
}

/// One ι step for a recursor: if the major reduces to a constructor of the
/// expected inductive,
///
/// `ind.rec P m… (c_j P b…) ⟶ m_j b… (ind.rec P m… b_recᵢ)…`
fn iota_elim(
    env: &Env,
    ind: &str,
    motive: &Term,
    minors: &[Term],
    major: &Term,
) -> Option<Term> {
    let (idx, params, ctor_args) = constructor_split(env, ind, major)?;
    // Totality: a malformed (e.g. unchecked / deserialized) eliminator with
    // too few minors or an out-of-range recursive position must stay STUCK,
    // never panic — `whnf`/`is_def_eq` are `pub` and run on not-yet-fully-
    // validated subterms (and on banks loaded via the unchecked `Env`
    // admitters). Conservative-stuck at the reduction layer, never a crash.
    let inductive = env.inductive(ind)?;
    if idx >= inductive.ctors.len() || idx >= minors.len() {
        return None;
    }
    let ctor = &inductive.ctors[idx];
    let mut applied: Vec<Term> = ctor_args.clone();
    for &r in &ctor.rec_positions {
        if r >= ctor_args.len() {
            return None;
        }
        let call = rec_subcall(&ctor.ty, &params, &ctor_args, r, &|major2, lift| {
            Term::elim(
                ind.to_string(),
                shift(lift, 0, motive),
                minors.iter().map(|mn| shift(lift, 0, mn)).collect(),
                major2,
            )
        })?;
        applied.push(call);
    }
    Some(Term::apps(minors[idx].clone(), applied))
}

/// One ι step for a case analysis: `ind.match m… (c_j P b…) ⟶ m_j b…`
/// (the constructor's non-parameter arguments — no recursive calls).
fn iota_match(env: &Env, ind: &str, minors: &[Term], major: &Term) -> Option<Term> {
    let (idx, _params, ctor_args) = constructor_split(env, ind, major)?;
    if idx >= minors.len() {
        return None;
    }
    Some(Term::apps(minors[idx].clone(), ctor_args))
}

/// Arg `r`'s type with the concrete `params` and the earlier `ctor_args`
/// substituted (pure substitution) — used to recover a higher-order recursive
/// argument's function-domain telescope at ι time.
fn instantiate_arg_type(
    ctor_ty: &Term,
    params: &[Term],
    ctor_args: &[Term],
    r: usize,
) -> Option<Term> {
    let mut t = ctor_ty.clone();
    for p in params {
        let next = match t.kind() {
            TermKind::Pi(_, body) => subst_top(body, p),
            _ => return None,
        };
        t = next;
    }
    for arg in &ctor_args[..r] {
        let next = match t.kind() {
            TermKind::Pi(_, body) => subst_top(body, arg),
            _ => return None,
        };
        t = next;
    }
    match t.kind() {
        TermKind::Pi(dom, _) => Some(dom.clone()),
        _ => None,
    }
}

/// Build the recursive eliminator sub-call for recursive position `r`. For a
/// **first-order** argument (`q = 0`) this is just `make_elim(g, 0)`. For a
/// **higher-order** argument `g : Π(z:D). I params idx` it is the *functorial*
/// `λ(z:D). make_elim((g z), q)` — the recursor threaded *through* the
/// function, never over the function space (whnf does not reduce under the λ,
/// so the inner eliminator fires only when later applied, on the structurally
/// smaller `g z`).
fn rec_subcall(
    ctor_ty: &Term,
    params: &[Term],
    ctor_args: &[Term],
    r: usize,
    make_elim: &dyn Fn(Term, usize) -> Term,
) -> Option<Term> {
    let arg_ty = instantiate_arg_type(ctor_ty, params, ctor_args, r)?;
    let (doms, _body) = peel_all_pis(&arg_ty);
    let q = doms.len();
    if q == 0 {
        return Some(make_elim(ctor_args[r].clone(), 0));
    }
    let g_lifted = shift(q, 0, &ctor_args[r]);
    let z_vars: Vec<Term> = (0..q).map(|j| Term::bound(q - 1 - j)).collect();
    let inner = make_elim(Term::apps(g_lifted, z_vars), q);
    Some(doms.iter().rev().fold(inner, |acc, d| Term::lam(d.clone(), acc)))
}

/// One ι step for a **mutual** recursor: if the major reduces to a
/// constructor of `member`, apply `member`'s method (selected from the flat
/// `minors` list) to the constructor's args, then one recursive `MutElim`
/// per group-recursive argument — each **dispatched to that argument's own
/// member** (`rec_member`) with the same motive tuple and minor list.
fn iota_mutelim(
    env: &Env,
    member: &str,
    motives: &[Term],
    minors: &[Term],
    major: &Term,
) -> Option<Term> {
    let group = env.group_of(member)?;
    let a = group.iter().position(|n| n == member)?;
    let (idx_in_member, params, ctor_args) = constructor_split(env, member, major)?;
    let ind = env.inductive(member)?;
    if idx_in_member >= ind.ctors.len() {
        return None;
    }
    let ctor = &ind.ctors[idx_in_member];
    // Flat minor index: Σ_{b<a} |ctors_b| + idx_in_member.
    let mut mi = idx_in_member;
    for name in &group[..a] {
        mi += env.inductive(name)?.ctors.len();
    }
    if mi >= minors.len() {
        return None;
    }
    let mut applied = ctor_args.clone();
    for (t, &r) in ctor.mut_rec_positions.iter().enumerate() {
        if r >= ctor_args.len() || t >= ctor.rec_member.len() {
            return None;
        }
        let b_prime = ctor.rec_member[t];
        if b_prime >= group.len() {
            return None;
        }
        let call = rec_subcall(&ctor.ty, &params, &ctor_args, r, &|major2, lift| {
            Term::mutelim(
                group[b_prime].clone(),
                motives.iter().map(|mn| shift(lift, 0, mn)).collect(),
                minors.iter().map(|mn| shift(lift, 0, mn)).collect(),
                major2,
            )
        })?;
        applied.push(call);
    }
    Some(Term::apps(minors[mi].clone(), applied))
}

/// If `major` whnf-reduces to a constructor of inductive `ind`, return its
/// constructor index, its parameters, and its non-parameter arguments. Total:
/// returns `None` (stuck) on any structural mismatch rather than indexing out
/// of bounds.
fn constructor_split(env: &Env, ind: &str, major: &Term) -> Option<(usize, Vec<Term>, Vec<Term>)> {
    let mj = whnf(env, major);
    let (head, spine) = as_const_app(&mj)?;
    let (ctor_ind, idx) = env.ctor_of(&head)?;
    if ctor_ind != ind {
        return None;
    }
    let n_params = env.inductive(ind)?.params.len();
    if spine.len() < n_params {
        return None;
    }
    Some((*idx, spine[..n_params].to_vec(), spine[n_params..].to_vec()))
}

/// Definitional equality (convertibility) under β/ζ/δ. After
/// [`whnf`], a `def` constant can never remain at the head, so a
/// surviving `Const` is `open`/unknown and compares by name — which is
/// exactly the opaque, theory-owned reading.
///
/// **Memoized + the hash-cons fast-path:** structurally identical inputs are
/// convertible by α-equivalence, so `a == b` (O(1) `ptr_eq`) short-circuits to
/// `true`; otherwise the verdict is cached on `env` keyed by the (canonicalized)
/// pair. Both are sound (a pure function of the env-state, which the memo is
/// cleared on) and verdict-preserving (the short-circuit returns exactly what
/// the full check would).
pub fn is_def_eq(env: &Env, a: &Term, b: &Term) -> bool {
    if a == b {
        return true;
    }
    if let Some(cached) = env.memo_defeq_get(a, b) {
        return cached;
    }
    let cuts_before = ReductionPath::cuts();
    let result = is_def_eq_uncached(env, a, b);
    // Same rule as the whnf memo: a verdict reached while a reduction below
    // was cut short is not the verdict a complete reduction would give, so it
    // must not be frozen into the cache for the rest of the session. (A cut
    // can only turn `true` into `false` — a term left un-reduced fails to
    // match one that was reduced — so caching it would make the kernel
    // PERMANENTLY reject conversions it can decide.)
    if ReductionPath::cuts() == cuts_before {
        env.memo_defeq_put(a, b, result);
    }
    result
}

/// The uncached convertibility check behind [`is_def_eq`] (its recursive calls
/// go back through the memoized [`is_def_eq`]).
fn is_def_eq_uncached(env: &Env, a: &Term, b: &Term) -> bool {
    let a = whnf(env, a);
    let b = whnf(env, b);
    match (a.kind(), b.kind()) {
        (TermKind::Sort(u), TermKind::Sort(v)) => u == v,
        (TermKind::Bound(i), TermKind::Bound(j)) => i == j,
        (TermKind::Const(x), TermKind::Const(y)) => x == y,
        (TermKind::App(f1, a1), TermKind::App(f2, a2)) => {
            is_def_eq(env, f1, f2) && is_def_eq(env, a1, a2)
        }
        (TermKind::Lam(d1, b1), TermKind::Lam(d2, b2)) => {
            is_def_eq(env, d1, d2) && is_def_eq(env, b1, b2)
        }
        (TermKind::Pi(d1, b1), TermKind::Pi(d2, b2)) => {
            is_def_eq(env, d1, d2) && is_def_eq(env, b1, b2)
        }
        // Two stuck eliminators / case analyses (ι could not fire on
        // either): compare congruently.
        (TermKind::Elim(i1, m1, ns1, j1), TermKind::Elim(i2, m2, ns2, j2))
        | (TermKind::Match(i1, m1, ns1, j1), TermKind::Match(i2, m2, ns2, j2)) => {
            i1 == i2
                && ns1.len() == ns2.len()
                && is_def_eq(env, m1, m2)
                && is_def_eq(env, j1, j2)
                && ns1.iter().zip(ns2).all(|(a, b)| is_def_eq(env, a, b))
        }
        // Two stuck fixpoints (neither applied to a constructor argument):
        // compare structurally (bodies under the `f` binder — de Bruijn).
        (
            TermKind::Fix { rec_arg: r1, ty: t1, body: b1 },
            TermKind::Fix { rec_arg: r2, ty: t2, body: b2 },
        ) => r1 == r2 && is_def_eq(env, t1, t2) && is_def_eq(env, b1, b2),
        // Two stuck mutual eliminators: same member (⇒ same group + minor
        // layout) and equal-length motive/minor tuples, compared pointwise.
        (TermKind::MutElim(m1, ps1, ns1, j1), TermKind::MutElim(m2, ps2, ns2, j2)) => {
            m1 == m2
                && ps1.len() == ps2.len()
                && ns1.len() == ns2.len()
                && is_def_eq(env, j1, j2)
                && ps1.iter().zip(ps2).all(|(a, b)| is_def_eq(env, a, b))
                && ns1.iter().zip(ns2).all(|(a, b)| is_def_eq(env, a, b))
        }
        _ => false,
    }
}
