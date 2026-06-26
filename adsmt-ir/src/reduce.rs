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

/// Weak-head normal form: reduce the **head** under β, ζ, δ, ι (`Elim` /
/// `Match` on a constructor), and μ (a guarded `Fix` applied with its
/// recursive argument in constructor form) until it is a sort, a variable,
/// an `open`/inductive/ctor constant, a λ/Π, a bare `Fix`, or a stuck
/// application/eliminator. Arguments are left unreduced (that is what
/// "weak" means); [`is_def_eq`] recurses into them congruently.
///
/// Termination: `def` bodies are non-recursive (head-δ cannot loop) and
/// every admitted `Fix` passed the structural-decrease guard
/// (`guard::guard_ok`), so μ strictly decreases the recursive argument —
/// whnf terminates on well-typed input.
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
    let result = whnf_uncached(env, t);
    env.memo_whnf_put(t, &result);
    result
}

/// The uncached weak-head reduction loop behind [`whnf`].
fn whnf_uncached(env: &Env, t: &Term) -> Term {
    let mut cur = t.clone();
    loop {
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
    let result = is_def_eq_uncached(env, a, b);
    env.memo_defeq_put(a, b, result);
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
