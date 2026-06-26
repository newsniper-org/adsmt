//! The **bidirectional type checker** — the kernel gate at the IR level.
//! A term that does not pass [`infer`]/[`check`] is rejected; nothing is
//! admitted to the [`Env`] until it has been checked.
//!
//! The local context `Ctx` is a stack of binder types: `ctx[len-1]` is the
//! innermost binder (`Bound(0)`). A stored binder type is valid in the
//! context that existed when it was pushed, so looking up `Bound(k)` lifts
//! it by `k+1` into the current, deeper context.

use crate::env::{Decl, Env, Modality};
use crate::error::TypeError;
use crate::reduce::{is_def_eq, whnf};
use crate::term::{Term, TermKind, Univ, shift, subst_top};

/// A local typing context: innermost binder last.
pub type Ctx = Vec<Term>;

fn lookup_local(ctx: &Ctx, k: usize) -> Result<Term, TypeError> {
    if k >= ctx.len() {
        return Err(TypeError::UnboundIndex(k));
    }
    let ty = &ctx[ctx.len() - 1 - k];
    Ok(shift(k + 1, 0, ty))
}

/// Infer the type of `t` in `ctx`. The returned term is a well-formed
/// type (itself checkable).
pub fn infer(env: &Env, ctx: &Ctx, t: &Term) -> Result<Term, TypeError> {
    match t.kind() {
        TermKind::Sort(u) => Ok(Term::sort(u.type_of())),
        TermKind::Bound(k) => lookup_local(ctx, *k),
        TermKind::Const(name) => env
            .lookup(name)
            .map(|d| d.ty.clone())
            .ok_or_else(|| TypeError::UnknownConst(name.clone())),
        TermKind::App(f, a) => {
            let tf = infer(env, ctx, f)?;
            let wf = whnf(env, &tf);
            match wf.kind() {
                TermKind::Pi(dom, cod) => {
                    check(env, ctx, a, dom)?;
                    Ok(subst_top(cod, a))
                }
                _ => Err(TypeError::NotAFunction(wf.to_string())),
            }
        }
        TermKind::Lam(dom, body) => {
            // The domain must be a type (well-sorted).
            infer_univ(env, ctx, dom)?;
            let mut ctx2 = ctx.clone();
            ctx2.push(dom.clone());
            let cod = infer(env, &ctx2, body)?;
            Ok(Term::pi(dom.clone(), cod))
        }
        TermKind::Pi(dom, cod) => {
            let s1 = infer_univ(env, ctx, dom)?;
            let mut ctx2 = ctx.clone();
            ctx2.push(dom.clone());
            let s2 = infer_univ(env, &ctx2, cod)?;
            Ok(Term::sort(Univ::product(s1, s2)))
        }
        TermKind::Let(ty, val, body) => {
            infer_univ(env, ctx, ty)?;
            check(env, ctx, val, ty)?;
            // Type the body as if under `(λ(_:ty). body) val`, so the
            // let-value flows into the result type (ζ at the type level).
            let mut ctx2 = ctx.clone();
            ctx2.push(ty.clone());
            let cod = infer(env, &ctx2, body)?;
            Ok(subst_top(&cod, val))
        }
        TermKind::Elim(ind_name, motive, minors, major) => {
            infer_eliminator(env, ctx, ind_name, motive, minors, major, true)
        }
        TermKind::Match(ind_name, motive, minors, major) => {
            infer_eliminator(env, ctx, ind_name, motive, minors, major, false)
        }
        TermKind::MutElim(member, motives, minors, major) => {
            infer_mut_eliminator(env, ctx, member, motives, minors, major)
        }
        TermKind::Fix { rec_arg, ty, body } => {
            // The function type must be well-sorted and abstract at least
            // `rec_arg+1` arguments, whose `rec_arg`-th is of an inductive
            // type (so "structurally smaller" is meaningful). `rec_arg` is
            // untrusted (a deserialized bank can carry any `usize`), so guard
            // the `+1` against overflow — `peel_pis` then rejects (returns
            // `None`) when `ty` has fewer than that many Π binders.
            infer_univ(env, ctx, ty)?;
            let arity = rec_arg.checked_add(1).ok_or_else(|| {
                TypeError::BadElim(format!("fix decreasing arg #{rec_arg} exceeds the arity"))
            })?;
            let (doms, _) = crate::term::peel_pis(ty, arity).ok_or_else(|| {
                TypeError::BadElim(format!("fix decreasing arg #{rec_arg} exceeds the arity"))
            })?;
            match crate::term::as_const_app(&whnf(env, &doms[*rec_arg])) {
                Some((h, _)) if env.inductive(&h).is_some() => {}
                _ => {
                    return Err(TypeError::BadElim(
                        "fix's decreasing argument is not of an inductive type".into(),
                    ));
                }
            }
            // Check the body against `ty` with the recursive `f : ty` bound.
            let mut ctx2 = ctx.clone();
            ctx2.push(ty.clone());
            check(env, &ctx2, body, &shift(1, 0, ty))?;
            // The structural-decrease guard — the soundness gate.
            if !crate::guard::guard_ok(env, *rec_arg, body) {
                return Err(TypeError::GuardFailed(format!(
                    "recursion on argument #{rec_arg} is not structurally decreasing"
                )));
            }
            Ok(ty.clone())
        }
    }
}

/// Shared typing for the recursor (`Elim`, `recursive = true`) and the
/// non-recursive case analysis (`Match`, `recursive = false`): recover the
/// parameters and indices from the major premise, validate the motive by
/// inferring the sort of `motive indices major`, enforce the Prop large-
/// elimination restriction, and check each minor premise against its
/// (method or match) type. The result is `motive indices major`.
fn infer_eliminator(
    env: &Env,
    ctx: &Ctx,
    ind_name: &str,
    motive: &Term,
    minors: &[Term],
    major: &Term,
    recursive: bool,
) -> Result<Term, TypeError> {
    let ind = env
        .inductive(ind_name)
        .ok_or_else(|| TypeError::UnknownConst(ind_name.to_string()))?;
    let n_params = ind.params.len();
    let n_indices = ind.indices.len();
    if minors.len() != ind.ctors.len() {
        return Err(TypeError::BadElim(format!(
            "{} minor premises, expected {}",
            minors.len(),
            ind.ctors.len()
        )));
    }
    // The major premise inhabits `I params indices`; recover both.
    let major_ty = infer(env, ctx, major)?;
    let major_w = whnf(env, &major_ty);
    let (head, spine) = crate::term::as_const_app(&major_w).ok_or_else(|| {
        TypeError::BadElim(format!("major premise is not of inductive `{ind_name}`"))
    })?;
    if head != *ind_name || spine.len() != n_params + n_indices {
        return Err(TypeError::BadElim(format!(
            "major premise has type `{major_w}`, expected `{ind_name}` \
             ({n_params} params, {n_indices} indices)"
        )));
    }
    let params = spine[..n_params].to_vec();
    let indices = spine[n_params..].to_vec();

    // Result `motive indices major`. Inferring its sort validates the
    // motive (it must accept the indices and the major and yield a `Sort`)
    // and gives the elimination sort.
    let mut motive_args = indices;
    motive_args.push(major.clone());
    let result = Term::apps(motive.clone(), motive_args);
    let elim_sort = infer_univ(env, ctx, &result)?;

    // Soundness: forbid large elimination from an impredicative-`Prop`
    // inductive into `Type` — the restriction that keeps impredicative
    // `Prop` consistent. Singleton/empty exception forgone (completeness,
    // not soundness).
    if ind.sort == Univ::Prop && matches!(elim_sort, Univ::Type(_)) {
        return Err(TypeError::BadElim(format!(
            "large elimination from Prop-inductive `{ind_name}` into {elim_sort}"
        )));
    }
    for (j, minor) in minors.iter().enumerate() {
        let expected = if recursive {
            crate::inductive::method_type(env, ind, j, &params, motive)?
        } else {
            crate::inductive::match_type(env, ind, j, &params, motive)?
        };
        check(env, ctx, minor, &expected)?;
    }
    Ok(result)
}

/// Typing for the **mutual** recursor `MutElim(member, motives, minors,
/// major)`. Recovers the shared params + indices from the major, validates
/// **every** motive in the tuple (P1-2) at a single elimination universe
/// (R3), enforces the Prop large-elim guard **per group member** (P0-3), and
/// checks each minor against its mutual method type (whose cross-member IHs
/// each use the right member's motive). Result: `motives[a] indices major`.
fn infer_mut_eliminator(
    env: &Env,
    ctx: &Ctx,
    member: &str,
    motives: &[Term],
    minors: &[Term],
    major: &Term,
) -> Result<Term, TypeError> {
    let group = env
        .group_of(member)
        .ok_or_else(|| TypeError::UnknownConst(member.to_string()))?
        .to_vec();
    let g = group.len();
    let a = group.iter().position(|n| n == member).unwrap();

    // R5: the full motive tuple and the concatenated minor list.
    if motives.len() != g {
        return Err(TypeError::BadElim(format!("{} motives, expected {g}", motives.len())));
    }
    let total_ctors: usize =
        group.iter().filter_map(|n| env.inductive(n)).map(|i| i.ctors.len()).sum();
    if minors.len() != total_ctors {
        return Err(TypeError::BadElim(format!(
            "{} minor premises, expected {total_ctors}",
            minors.len()
        )));
    }

    // R1: every member shares an identical parameter telescope.
    let ind_a = env.inductive(member).unwrap();
    let shared_params = ind_a.params.clone();
    let n_a = ind_a.indices.len();
    let k = shared_params.len();
    for n in &group {
        let ip = env.inductive(n).map(|i| &i.params);
        if ip != Some(&shared_params) {
            return Err(TypeError::BadElim(
                "mutual recursor requires a shared parameter telescope".into(),
            ));
        }
    }

    // Recover the shared params + the major's indices from its type.
    let major_ty = infer(env, ctx, major)?;
    let major_w = whnf(env, &major_ty);
    let (head, spine) = crate::term::as_const_app(&major_w)
        .ok_or_else(|| TypeError::BadElim(format!("major premise is not of inductive `{member}`")))?;
    if head != *member || spine.len() != k + n_a {
        return Err(TypeError::BadElim(format!(
            "major premise has type `{major_w}`, expected `{member}`"
        )));
    }
    let params = spine[..k].to_vec();
    let indices = spine[k..].to_vec();

    // The elimination universe, from the major's own motive applied to the
    // recovered indices+major.
    let mut motive_args = indices;
    motive_args.push(major.clone());
    let result = Term::apps(motives[a].clone(), motive_args);
    let elim_sort = infer_univ(env, ctx, &result)?;

    // P1-2 + R3: validate EVERY motive against the expected shape at the one
    // elimination universe.
    for (b, name) in group.iter().enumerate() {
        let expected = crate::inductive::expected_motive_type(env, name, &params, elim_sort)
            .ok_or_else(|| TypeError::BadElim(format!("cannot form motive type for `{name}`")))?;
        check(env, ctx, &motives[b], &expected)?;
    }

    // P0-3: large elimination from a `Prop` member into `Type` — reject if
    // ANY group member is Prop-sorted (the shared methods/IHs can transport a
    // Prop value into the Type result).
    if matches!(elim_sort, Univ::Type(_)) {
        for name in &group {
            if env.inductive(name).map(|i| i.sort) == Some(Univ::Prop) {
                return Err(TypeError::BadElim(format!(
                    "large elimination from Prop member `{name}` of the mutual group into {elim_sort}"
                )));
            }
        }
    }

    // Check each minor against its mutual method type, member by member.
    let mut mi = 0;
    for name in &group {
        let ind_b = env.inductive(name).unwrap();
        for j in 0..ind_b.ctors.len() {
            let expected = crate::inductive::mut_method_type(ind_b, j, &params, motives)?;
            check(env, ctx, &minors[mi], &expected)?;
            mi += 1;
        }
    }
    Ok(result)
}

/// Check that `t` has type `expected` (up to convertibility).
pub fn check(env: &Env, ctx: &Ctx, t: &Term, expected: &Term) -> Result<(), TypeError> {
    let inferred = infer(env, ctx, t)?;
    if is_def_eq(env, &inferred, expected) {
        Ok(())
    } else {
        Err(TypeError::Mismatch {
            expected: expected.to_string(),
            found: inferred.to_string(),
        })
    }
}

/// Infer the *sort* of a type-term: its type must reduce to a [`Sort`].
///
/// [`Sort`]: Term::Sort
pub fn infer_univ(env: &Env, ctx: &Ctx, t: &Term) -> Result<Univ, TypeError> {
    let ty = infer(env, ctx, t)?;
    let w = whnf(env, &ty);
    match w.kind() {
        TermKind::Sort(u) => Ok(*u),
        _ => Err(TypeError::NotASort(w.to_string())),
    }
}

/// Admit a **`def`** (closed-world definition): check the declared type is
/// well-sorted and the body has that type, then declare it δ-unfoldable.
pub fn define(env: &mut Env, name: &str, ty: Term, body: Term) -> Result<(), TypeError> {
    if env.lookup(name).is_some() {
        return Err(TypeError::DuplicateConst(name.to_string()));
    }
    let ctx = Ctx::new();
    infer_univ(env, &ctx, &ty)?;
    check(env, &ctx, &body, &ty)?;
    env.record(crate::env::AdmissionStep::Define {
        name: name.to_string(),
        ty: ty.clone(),
        body: body.clone(),
    });
    env.declare(name.to_string(), Decl { ty, modality: Modality::Def(body) });
    Ok(())
}

/// Admit an **`open`** (classical / theory) parameter: check its type is
/// well-sorted, then declare it opaque (no δ-reduction).
pub fn postulate(env: &mut Env, name: &str, ty: Term) -> Result<(), TypeError> {
    if env.lookup(name).is_some() {
        return Err(TypeError::DuplicateConst(name.to_string()));
    }
    let ctx = Ctx::new();
    infer_univ(env, &ctx, &ty)?;
    env.record(crate::env::AdmissionStep::Postulate { name: name.to_string(), ty: ty.clone() });
    env.declare(name.to_string(), Decl { ty, modality: Modality::Open });
    Ok(())
}

/// Convenience: infer the type of a closed term in the empty context.
pub fn type_of(env: &Env, t: &Term) -> Result<Term, TypeError> {
    infer(env, &Ctx::new(), t)
}
