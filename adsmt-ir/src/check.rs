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
/// Is `name` spelled like a numeral — the spelling `theory::literal` uses for
/// an integer or decimal constant?
///
/// The kernel's convention is that such a spelling IS that number: `literal()`
/// re-uses an already-declared constant of the same spelling rather than
/// minting a second one, `whnf` folds arithmetic over them, and the CIC→HOL
/// lowering reads the value straight off the name. The convention's stated
/// justification is that "SMT-LIB simple symbols cannot begin with a digit, so
/// an all-digit name never clashes with a user symbol" — which is true of
/// SMT-LIB and false of any caller that can quote an identifier.
pub fn is_numeral_spelling(name: &str) -> bool {
    let body = name.strip_prefix('-').unwrap_or(name);
    if body.is_empty() {
        return false;
    }
    match body.split_once('.') {
        Some((int, frac)) => {
            !int.is_empty()
                && !frac.is_empty()
                && int.bytes().all(|b| b.is_ascii_digit())
                && frac.bytes().all(|b| b.is_ascii_digit())
        }
        None => body.bytes().all(|b| b.is_ascii_digit()),
    }
}

/// Guard the numeral convention at the admission boundary.
///
/// A numeral-spelled constant may only be declared at an ARITHMETIC sort,
/// because everything downstream reads its value off the name. Admitting
/// `\`-3\` : S` for an uninterpreted `S` handed `whnf` two constants it then
/// declared unequal by spelling — `not(\`-3\` = \`-4\`)` came back `unsat`
/// where the same program with ordinary names answers `sat`.
fn check_numeral_sort(name: &str, ty: &Term) -> Result<(), TypeError> {
    if !is_numeral_spelling(name) {
        return Ok(());
    }
    let ok = matches!(
        ty.kind(),
        crate::term::TermKind::Const(c) if c == crate::theory::INT || c == crate::theory::REAL
    );
    if ok {
        Ok(())
    } else {
        Err(TypeError::BadElim(format!(
            "`{name}` is spelled like a numeral, so it may only be declared at              `Int` or `Real` — the kernel reads a numeral's VALUE off its name"
        )))
    }
}

pub fn define(env: &mut Env, name: &str, ty: Term, body: Term) -> Result<(), TypeError> {
    if env.lookup(name).is_some() {
        return Err(TypeError::DuplicateConst(name.to_string()));
    }
    check_numeral_sort(name, &ty)?;
    // A numeral is a LITERAL: opaque, with its value read off the name. It must
    // never be a definition. Defining one closes a reduction cycle with the
    // arithmetic folds in `whnf` — `define("5", Int, Int.add 2 3)` type-checks,
    // the fold rewrites `Int.add 2 3` to `Const("5")`, δ unfolds `5` back to
    // `Int.add 2 3`, and head reduction cycles. It used to HANG on that
    // (measured); since `1f600e9` the term reappears on the reduction path and
    // `whnf` returns it stuck instead — so the consequence is now an
    // un-reducible numeral rather than a non-terminating kernel. The guard
    // stays: a literal whose value is read off its name must not also have a
    // body. `theory::literal` postulates, so nothing legitimate is refused.
    if is_numeral_spelling(name) {
        return Err(TypeError::BadElim(format!(
            "`{name}` is spelled like a numeral, so it is a literal and cannot be \
             DEFINED — a numeral's value is read off its name"
        )));
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
    check_numeral_sort(name, &ty)?;
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

/// Admit a **mutually recursive group of definitions**, together.
///
/// No member of such a group can go through [`define`]: each body mentions the
/// others, so none type-checks until all the signatures exist, and once they
/// do, `define` would refuse the name as already declared. The lu-kb face
/// worked around that by [`postulate`](crate::postulate)-ing the signatures and
/// then overwriting them with `Env::declare`, the raw unchecked insertion —
/// which skipped the journal (so the group could never be banked) and, far
/// worse, skipped every termination check. `f x = g x, g x = f x` was admitted
/// and made the kernel's `whnf` diverge; with the recursive call under an
/// argument it overflowed the stack.
///
/// This is the checked way in. It accepts each member either absent, or already
/// declared `Open` at exactly the type given — the shape a face produces when
/// it postulates the signatures first — and it:
///
/// 1. type-checks every body against its signature, in the environment where
///    every member is visible;
/// 2. requires the group to be **structurally decreasing**
///    ([`mutual_guard_ok`](crate::guard::mutual_guard_ok)), searching for a
///    recursive-argument assignment that works;
/// 3. records ONE journal step, so a bank replay re-runs both checks;
/// 4. only then declares the members as `def`s.
///
/// Step 2 is what makes the resulting δ-cycle safe. A group that passes has a
/// `Match` on the recursive argument between the entry and every recursive
/// call, so head reduction is stuck on an open argument and strictly decreases
/// on a constructor one — the same argument the `fix` guard makes, on the same
/// trust level (a decision procedure, no proof term).
pub fn define_mutual(
    env: &mut Env,
    group: &[(String, Term, Term)],
) -> Result<(), TypeError> {
    use crate::guard::{GroupMember, mutual_guard_ok};

    if group.is_empty() {
        return Ok(());
    }
    // Names must be distinct: two members with one name would leave the second
    // body checked against a signature the first one owns.
    for (i, (name, _, _)) in group.iter().enumerate() {
        if group[..i].iter().any(|(n, _, _)| n == name) {
            return Err(TypeError::DuplicateConst(name.clone()));
        }
    }

    // The numeral rules, as in `define`.
    for (name, ty, _) in group {
        check_numeral_sort(name, ty)?;
        if is_numeral_spelling(name) {
            return Err(TypeError::BadElim(format!(
                "`{name}` is spelled like a numeral, so it is a literal and cannot be \
                 DEFINED — a numeral's value is read off its name"
            )));
        }
    }

    // Every member must be absent, or already `Open` at exactly this type. An
    // existing `Def`/`Inductive`/`Constructor` is a genuine clash.
    let ctx = Ctx::new();
    for (name, ty, _) in group {
        match env.lookup(name) {
            None => {}
            Some(Decl { ty: existing, modality: Modality::Open }) if existing == ty => {}
            Some(_) => return Err(TypeError::DuplicateConst(name.clone())),
        }
    }
    // Everything below runs on a COPY, so a refused group leaves the caller's
    // environment exactly as it was — no half-admitted signatures. (Same shape
    // as `declare_inductive`'s `work` env.)
    let mut work = env.clone();
    for (name, ty, _) in group {
        infer_univ(&work, &ctx, ty)?;
        if work.lookup(name).is_none() {
            work.declare(name.clone(), Decl { ty: ty.clone(), modality: Modality::Open });
        }
    }

    // 1. every body against its signature, with the whole group in scope.
    for (_, ty, body) in group {
        check(&work, &ctx, body, ty)?;
    }

    // 2. the group guard. Each member's recursive argument is unknown, so
    //    search the assignments — arities are tiny in practice, and the
    //    product is capped so a pathological group is refused rather than
    //    explored.
    let arities: Vec<usize> = group.iter().map(|(_, ty, _)| pi_arity(ty)).collect();
    let combinations: usize = arities.iter().try_fold(1usize, |acc, &a| {
        acc.checked_mul(a.max(1))
    }).unwrap_or(usize::MAX);
    if combinations > MAX_GUARD_SEARCH {
        return Err(TypeError::BadElim(format!(
            "mutual group `{}`: too many recursive-argument assignments to search \
             ({combinations} > {MAX_GUARD_SEARCH})",
            group[0].0
        )));
    }
    let bodies: Vec<(String, Term)> =
        group.iter().map(|(n, _, b)| (n.clone(), b.clone())).collect();
    let mut chosen: Option<Vec<GroupMember>> = None;
    let mut assignment = vec![0usize; group.len()];
    'search: loop {
        let members: Vec<GroupMember> = group
            .iter()
            .zip(&assignment)
            .map(|((n, _, _), &r)| GroupMember { name: n.clone(), rec_arg: r })
            .collect();
        if mutual_guard_ok(&work, &members, &bodies) {
            chosen = Some(members);
            break 'search;
        }
        // odometer over the per-member arities
        let mut i = 0;
        loop {
            if i == assignment.len() {
                break 'search;
            }
            assignment[i] += 1;
            if assignment[i] < arities[i].max(1) {
                break;
            }
            assignment[i] = 0;
            i += 1;
        }
    }
    let Some(_members) = chosen else {
        return Err(TypeError::BadElim(format!(
            "mutual `fn` group `{}`: no argument of any member is structurally \
             decreasing, so the group is not admitted. Mutual recursion must \
             destructure an inductive argument with a `match`; recursion guarded \
             by an arithmetic test (`if n = 0 …`) has no structural measure. The \
             branch that admits those on a termination proof is not implemented \
             yet — the same rule a single `rec fn` already follows.",
            group[0].0
        )));
    };

    // 3 + 4. journal the group as one step, then declare the bodies.
    env.record(crate::env::AdmissionStep::MutualDefine(
        group
            .iter()
            .map(|(name, ty, body)| crate::env::MutualDefSpec {
                name: name.clone(),
                ty: ty.clone(),
                body: body.clone(),
            })
            .collect(),
    ));
    for (name, ty, body) in group {
        env.declare(
            name.clone(),
            Decl { ty: ty.clone(), modality: Modality::Def(body.clone()) },
        );
    }
    Ok(())
}

/// Cap on the recursive-argument assignments [`define_mutual`] will try. A
/// group of realistic shape (a handful of members, a handful of arguments each)
/// is far below it; anything above is refused rather than searched.
const MAX_GUARD_SEARCH: usize = 4096;

/// How many arguments a signature abstracts (its Π-telescope length).
fn pi_arity(ty: &Term) -> usize {
    let mut n = 0;
    let mut cur = ty.clone();
    while let crate::term::TermKind::Pi(_, cod) = cur.kind() {
        n += 1;
        cur = cod.clone();
    }
    n
}
