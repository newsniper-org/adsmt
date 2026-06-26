//! Inductive types, constructors, and the dependent recursor (M2 + M2.5).
//!
//! Supports **parameterized, indexed** inductives: `Nat`, `Bool`,
//! `List A`, records, *and* index-varying families like
//! `Vec (A:Type) : Nat → Type` (`vnil : Vec A 0`,
//! `vcons : Π n. A → Vec A n → Vec A (S n)`). Parameters are *uniform*
//! across constructors; indices may *vary*.
//!
//! Admission ([`declare_inductive_indexed`], or [`declare_inductive`] for
//! the non-indexed case) checks the parameter + index telescopes and every
//! constructor is well-sorted, then runs a **conservative strict-
//! positivity check**: each constructor argument is either *recursive*
//! (`I params idxᵣ` — the uniform parameters, any indices) or must not
//! mention `I` at all; anything else is *rejected* (`NonPositive`).
//!
//! The recursor is the [`Term::Elim`] primitive. Its dependent minor-
//! premise types are produced by [`method_type`], which **instantiates a
//! per-constructor template** — `Π params. Π(motive). MethodType` — built
//! once at admission. Doing all the de Bruijn bookkeeping a single time, in
//! one uniform context (parameters and motive as binders, never mixed with
//! ambient terms), is what keeps the indexed recursor tractable and
//! auditable. ι-reduction lives in `reduce::whnf`.

use crate::check::{Ctx, infer_univ};
use crate::env::{Constructor, Decl, Env, Inductive, Modality};
use crate::error::TypeError;
use crate::term::{
    Term, TermKind, Univ, as_const_app, build_pi, occurs, peel_all_pis, peel_pis, shift, subst_top,
};

/// The de Bruijn occurrences of the `k` parameters `P_0 … P_{k-1}` in a
/// context where the params sit at the bottom and `offset` further binders
/// are above them: `P_i = Bound(offset + (k-1-i))`.
fn param_vars(offset: usize, k: usize) -> Vec<Term> {
    (0..k).map(|i| Term::bound(offset + (k - 1 - i))).collect()
}

/// Admit a parameterized, **non-indexed** inductive (the common case).
pub fn declare_inductive(
    env: &mut Env,
    name: &str,
    params: Vec<Term>,
    sort: Univ,
    ctors: Vec<(String, Vec<Term>)>,
) -> Result<(), TypeError> {
    let ctors = ctors.into_iter().map(|(n, args)| (n, args, Vec::new())).collect();
    declare_inductive_indexed(env, name, params, Vec::new(), sort, ctors)
}

/// Admit a parameterized, **indexed** inductive type.
///
/// `indices` is the index telescope (`indices[i]` in context
/// `params ++ indices[0..i]`). Each `ctors[c] = (name, args, idx_exprs)`
/// gives a constructor's argument telescope (`args[j]` in context
/// `params ++ args[0..j]`) and its **conclusion index expressions**
/// `idx_exprs` (in context `params ++ args`), so the constructor's result
/// type is `I params idx_exprs`.
pub fn declare_inductive_indexed(
    env: &mut Env,
    name: &str,
    params: Vec<Term>,
    indices: Vec<Term>,
    sort: Univ,
    ctors: Vec<(String, Vec<Term>, Vec<Term>)>,
) -> Result<(), TypeError> {
    if env.lookup(name).is_some() {
        return Err(TypeError::DuplicateConst(name.to_string()));
    }

    // 1. parameter telescope, then index telescope (on top of params).
    let mut ctx = Ctx::new();
    for p in &params {
        infer_univ(env, &ctx, p)?;
        ctx.push(p.clone());
    }
    for ix in &indices {
        infer_univ(env, &ctx, ix)?;
        ctx.push(ix.clone());
    }

    // 2. the type former `I : Π params. Π indices. Sort`, on a working copy.
    let arity = build_pi(&indices, Term::sort(sort));
    let ind_ty = build_pi(&params, arity);
    infer_univ(env, &Ctx::new(), &ind_ty)?;
    let mut work = env.clone();
    work.declare(name.to_string(), Decl { ty: ind_ty, modality: Modality::Inductive });

    // 3. each constructor (group = just this inductive).
    let group = [name];
    let mut built = Vec::with_capacity(ctors.len());
    for (cname, args, idx_exprs) in &ctors {
        let ctor = process_constructor(&work, name, &params, &group, cname, args, idx_exprs)?;
        work.declare(ctor.name.clone(), Decl { ty: ctor.ty.clone(), modality: Modality::Constructor });
        built.push(ctor);
    }

    // Record the raw admission inputs (NOT the derived templates) for the
    // AOT-bank: loading replays this through `declare_inductive_indexed`, so
    // positivity + every template is re-derived and re-checked. `ctors` is the
    // unprocessed `(name, args, idx_exprs)` input; `params`/`indices` are
    // cloned because `register_inductive` consumes them next.
    env.record(crate::env::AdmissionStep::Inductive(crate::env::IndSpec {
        name: name.to_string(),
        params: params.clone(),
        indices: indices.clone(),
        sort,
        ctors,
    }));
    env.register_inductive(Inductive { name: name.to_string(), params, indices, sort, ctors: built });
    env.register_group(vec![name.to_string()]); // its own singleton group
    Ok(())
}

/// One member of a [`declare_mutual`] group.
pub struct MutualMember {
    pub name: String,
    pub params: Vec<Term>,
    pub indices: Vec<Term>,
    pub sort: Univ,
    /// `(ctor name, arg telescope, conclusion index expressions)`.
    pub ctors: Vec<(String, Vec<Term>, Vec<Term>)>,
}

/// Admit a group of **mutually-defined** inductives: all type formers are
/// registered first, so a constructor of one member may reference the type
/// of any other (e.g. `Tree`/`Forest`, `Even`/`Odd`). Positivity is checked
/// over the *whole group*: a constructor argument is either a self-recursive
/// occurrence (`Self params idx`, which gets an induction hypothesis), or a
/// cross-reference whose head is another group member applied to non-group
/// arguments (allowed, but with **no** induction hypothesis — the recursors
/// are independent, not yet mutual), or it must mention no group member at
/// all. Anything else is *rejected*.
pub fn declare_mutual(env: &mut Env, members: Vec<MutualMember>) -> Result<(), TypeError> {
    // 1. no name collisions (with the env or within the group).
    for (i, m) in members.iter().enumerate() {
        if env.lookup(&m.name).is_some()
            || members[..i].iter().any(|p| p.name == m.name)
        {
            return Err(TypeError::DuplicateConst(m.name.clone()));
        }
    }
    // 2. register every type former on a working copy.
    let mut work = env.clone();
    for m in &members {
        let arity = build_pi(&m.indices, Term::sort(m.sort));
        let ind_ty = build_pi(&m.params, arity);
        work.declare(m.name.clone(), Decl { ty: ind_ty, modality: Modality::Inductive });
    }
    // 3. now check each former's type well-formed (telescopes may reference
    //    other group members).
    for m in &members {
        let ty = work.lookup(&m.name).unwrap().ty.clone();
        infer_univ(&work, &Ctx::new(), &ty)?;
    }
    // 4. process every constructor, group-aware.
    let group: Vec<&str> = members.iter().map(|m| m.name.as_str()).collect();
    let mut built_inds = Vec::with_capacity(members.len());
    for m in &members {
        let mut built = Vec::with_capacity(m.ctors.len());
        for (cname, args, idx_exprs) in &m.ctors {
            let ctor =
                process_constructor(&work, &m.name, &m.params, &group, cname, args, idx_exprs)?;
            work.declare(ctor.name.clone(), Decl { ty: ctor.ty.clone(), modality: Modality::Constructor });
            built.push(ctor);
        }
        built_inds.push(Inductive {
            name: m.name.clone(),
            params: m.params.clone(),
            indices: m.indices.clone(),
            sort: m.sort,
            ctors: built,
        });
    }
    // 5. commit.
    for ind in built_inds {
        env.register_inductive(ind);
    }
    env.register_group(members.iter().map(|m| m.name.clone()).collect());
    // Record the raw mutual-admission inputs for the AOT-bank (replayed
    // through `declare_mutual` on load, re-deriving every template / group).
    // `members` is consumed here (its last use), so MOVE each member's fields
    // into the journal `IndSpec` rather than cloning the (nested-`Vec`)
    // params/indices/ctors a second time.
    env.record(crate::env::AdmissionStep::Mutual(
        members
            .into_iter()
            .map(|m| crate::env::IndSpec {
                name: m.name,
                params: m.params,
                indices: m.indices,
                sort: m.sort,
                ctors: m.ctors,
            })
            .collect(),
    ));
    Ok(())
}

/// Whether any name in `group` occurs in `t`.
fn group_occurs(group: &[&str], t: &Term) -> bool {
    group.iter().any(|n| occurs(n, t))
}

/// Check one constructor (with `self_name`'s params and a `group` of
/// mutually-defined names in scope), classify each argument
/// (self-recursive / cross-reference / external / rejected), and build it.
fn process_constructor(
    work: &Env,
    self_name: &str,
    params: &[Term],
    group: &[&str],
    cname: &str,
    args: &[Term],
    idx_exprs: &[Term],
) -> Result<Constructor, TypeError> {
    if work.lookup(cname).is_some() {
        return Err(TypeError::DuplicateConst(cname.to_string()));
    }
    let k = params.len();
    let m = args.len();
    let g = group.len();
    let self_b = group.iter().position(|n| *n == self_name).unwrap_or(0);
    let mut actx: Ctx = params.to_vec();
    let mut rec_positions = Vec::new(); // self-recursive (independent recursor)
    let mut mut_rec_positions = Vec::new(); // self OR cross (mutual recursor)
    let mut rec_member = Vec::new(); // group position of each mut-rec arg's head
    for (j, s) in args.iter().enumerate() {
        infer_univ(work, &actx, s)?;
        let nonpos = || TypeError::NonPositive { ind: self_name.to_string(), ctor: cname.to_string() };
        // A **group-recursive** argument: peel any leading function domains
        // (M2.8 higher-order args `Π(z:D). I params idx`), then the *body*
        // must be a group member applied to the uniform shared params, no
        // group member nested in its indices. Strict positivity requires the
        // function domains to be group-member-free (the inductive only in the
        // codomain — a domain occurrence is a negative position ⇒ unsound).
        // Params sit under `j` argument binders PLUS `q` function-domain
        // binders ⇒ offset `j + q`; `q = 0` is the first-order case. Covers a
        // self-recursive arg (head = self) and a cross-member arg; only self
        // ones get an independent-recursor IH.
        let (fun_doms, body) = peel_all_pis(s);
        let q = fun_doms.len();
        let domains_clean = fun_doms.iter().all(|d| !group_occurs(group, d));
        match as_const_app(&body) {
            Some((h, spine))
                if domains_clean
                    && group.contains(&h.as_str())
                    && spine.len() >= k
                    && spine[..k] == param_vars(j + q, k)[..]
                    && !spine[k..].iter().any(|sp| group_occurs(group, sp)) =>
            {
                let b = group.iter().position(|n| *n == h.as_str()).unwrap();
                mut_rec_positions.push(j);
                rec_member.push(b);
                if h == self_name {
                    rec_positions.push(j);
                }
            }
            // any other occurrence of a group member (incl. a member in a
            // function domain, or a nested container) is non-strictly-positive
            // / unsupported — rejected.
            _ if group_occurs(group, s) => return Err(nonpos()),
            _ => {}
        }
        actx.push(s.clone());
    }
    // full type `Π params. Π args. Self params idx_exprs`.
    let mut concl_spine = param_vars(m, k);
    concl_spine.extend(idx_exprs.iter().cloned());
    let concl = Term::apps(Term::cnst(self_name.to_string()), concl_spine);
    let ctor_ty = build_pi(params, build_pi(args, concl));
    infer_univ(work, &Ctx::new(), &ctor_ty)?;

    let malformed = || TypeError::BadElim(format!("malformed constructor `{cname}`"));
    let method_template = build_method_template(cname, &ctor_ty, k, &rec_positions).ok_or_else(malformed)?;
    let match_template = build_method_template(cname, &ctor_ty, k, &[]).ok_or_else(malformed)?;
    let mut_method_template =
        build_mut_method_template(cname, &ctor_ty, k, g, self_b, &mut_rec_positions, &rec_member)
            .ok_or_else(malformed)?;

    Ok(Constructor {
        name: cname.to_string(),
        ty: ctor_ty,
        args_count: m,
        rec_positions,
        method_template,
        match_template,
        mut_method_template,
        mut_rec_positions,
        rec_member,
    })
}

/// Build the **mutual** method template `Π params. Π(P_0)…Π(P_{g-1}).
/// MutMethodType` — `build_method_template` with the single motive binder
/// generalized to a `g`-wide block, the conclusion using `P_{self_b}`, and
/// each recursive arg's IH using `P_{rec_member[t]}` (cross-member IHs).
#[allow(clippy::too_many_arguments)]
fn build_mut_method_template(
    ctor_name: &str,
    ctor_ty: &Term,
    k: usize,
    g: usize,
    self_b: usize,
    mut_rec_positions: &[usize],
    rec_member: &[usize],
) -> Option<Term> {
    let (param_doms, after_params) = peel_pis(ctor_ty, k)?;
    // Insert the g-wide motive block between params and args (params refs +g).
    let body1 = shift(g, 0, &after_params);
    let (arg_doms, concl) = peel_all_pis(&body1);
    let m = arg_doms.len();
    let p = mut_rec_positions.len();

    // conclusion: P_{self_b} ctor_indices (c params args), in ctx
    // [params, motives(g), args(m), IHs(p)].
    let (_i, cspine) = as_const_app(&concl)?;
    if cspine.len() < k {
        return None;
    }
    let ctor_indices = &cspine[k..];
    // motive of member b sits at Bound(below + (g-1-b)); below = p+m here.
    let motive_at_concl = Term::bound(p + m + (g - 1 - self_b));
    let mut concl_args: Vec<Term> = ctor_indices.iter().map(|x| shift(p, 0, x)).collect();
    let mut target_spine: Vec<Term> =
        (0..k).map(|i| Term::bound(p + m + g + (k - 1 - i))).collect();
    target_spine.extend((0..m).map(|i| Term::bound(p + (m - 1 - i))));
    concl_args.push(Term::apps(Term::cnst(ctor_name.to_string()), target_spine));
    let conclusion = Term::apps(motive_at_concl, concl_args);

    // one IH per group-recursive arg, at THAT member's motive — functorial
    // for a higher-order arg (`q > 0`), first-order for `q = 0`.
    let mut ih_domains = Vec::with_capacity(p);
    for (t, &r) in mut_rec_positions.iter().enumerate() {
        let b_prime = rec_member[t];
        let (doms, rbody) = peel_all_pis(&arg_doms[r]);
        let q = doms.len();
        let (_ir, rspine) = as_const_app(&rbody)?;
        if rspine.len() < k {
            return None;
        }
        let rec_indices = &rspine[k..];
        let motive_at_ih = Term::bound(t + m + q + (g - 1 - b_prime));
        ih_domains.push(build_functorial_ih(&doms, rec_indices, t, m, r, q, motive_at_ih));
    }

    let inner = build_pi(&arg_doms, build_pi(&ih_domains, conclusion));
    // g placeholder motive binders (P_{g-1} innermost … P_0 outermost).
    let mut with_motives = inner;
    for _ in 0..g {
        with_motives = Term::pi(Term::sort(Univ::Prop), with_motives);
    }
    Some(build_pi(&param_doms, with_motives))
}

/// Build the per-constructor method template `Π params. Π(motive).
/// MethodType`, with parameters and the motive as binders (so every de
/// Bruijn shift below is uniform). The motive binder's type is a
/// placeholder — the template is only ever instantiated by substitution
/// ([`method_type`]), never type-checked.
fn build_method_template(
    ctor_name: &str,
    ctor_ty: &Term,
    k: usize,
    rec_positions: &[usize],
) -> Option<Term> {
    // Peel the `k` parameter binders → `Π args. I params idx` in ctx [params].
    let (param_doms, after_params) = peel_pis(ctor_ty, k)?;
    // Insert the motive binder between params and args (params refs +1).
    let body1 = shift(1, 0, &after_params);
    // Peel the argument telescope.
    let (arg_doms, concl) = peel_all_pis(&body1);
    let m = arg_doms.len();
    let p = rec_positions.len();

    // conclusion indices: concl = I (params) (ctor_indices), in ctx
    // [params, motive, args(m)].
    let (_i, cspine) = as_const_app(&concl)?;
    if cspine.len() < k {
        return None;
    }
    let ctor_indices = &cspine[k..];

    // Conclusion, in ctx [params, motive, args(m), IHs(p)].
    let motive_at_concl = Term::bound(p + m); // motive sits below the args + IHs
    let mut concl_args: Vec<Term> = ctor_indices.iter().map(|x| shift(p, 0, x)).collect();
    let mut target_spine: Vec<Term> =
        (0..k).map(|i| Term::bound(p + m + 1 + (k - 1 - i))).collect();
    target_spine.extend((0..m).map(|i| Term::bound(p + (m - 1 - i))));
    let target = Term::apps(Term::cnst(ctor_name.to_string()), target_spine);
    concl_args.push(target);
    let conclusion = Term::apps(motive_at_concl, concl_args);

    // One induction hypothesis per recursive argument. For a higher-order arg
    // `a_r : Π(z:D). I params idx` the IH is the **functorial**
    // `Π(z:D'). motive idx' (a_r z)`; `q = 0` collapses to the first-order
    // `motive idx' a_r`.
    let mut ih_domains = Vec::with_capacity(p);
    for (t, &r) in rec_positions.iter().enumerate() {
        // arg r's type = Π(z:D). I (params) (rec_indices_r), in ctx
        // [params, motive, args(0..r)].
        let (doms, rbody) = peel_all_pis(&arg_doms[r]);
        let q = doms.len();
        let (_ir, rspine) = as_const_app(&rbody)?;
        if rspine.len() < k {
            return None;
        }
        let rec_indices = &rspine[k..];
        let ih = build_functorial_ih(&doms, rec_indices, t, m, r, q, Term::bound(t + m + q));
        ih_domains.push(ih);
    }

    let inner = build_pi(&arg_doms, build_pi(&ih_domains, conclusion));
    // motive binder: placeholder type (unused — never checked).
    let with_motive = Term::pi(Term::sort(Univ::Prop), inner);
    Some(build_pi(&param_doms, with_motive))
}

/// Build one **functorial** induction-hypothesis domain for recursive
/// argument `r` (the `t`-th recursive position) whose type is
/// `Π(z_0:D_0)…Π(z_{q-1}:D_{q-1}). I params rec_indices`:
///
/// ```text
/// Π(z_0:D_0')…Π(z_{q-1}:D_{q-1}'). motive_at_ih  idx'  (a_r z_0 … z_{q-1})
/// ```
///
/// `q = 0` collapses to the first-order `motive_at_ih idx' a_r`. `motive_at_ih`
/// is supplied by the caller (`Bound(t+m+q)` for the independent recursor,
/// `Bound(t+m+q+(g-1-b'))` for the mutual one). The `doms`/`rec_indices` are
/// read in arg `r`'s context (`[params, motive(block), args(0..r), z…]`); the
/// `t + m - r` shift relocates their outer free vars to the IH-binder context,
/// with cutoff `j`/`q` protecting the `z`-binders.
fn build_functorial_ih(
    doms: &[Term],
    rec_indices: &[Term],
    t: usize,
    m: usize,
    r: usize,
    q: usize,
    motive_at_ih: Term,
) -> Term {
    let dprime: Vec<Term> =
        doms.iter().enumerate().map(|(jj, d)| shift(t + m - r, jj, d)).collect();
    let mut ih_args: Vec<Term> =
        rec_indices.iter().map(|x| shift(t + m - r, q, x)).collect();
    let a_r = Term::bound(t + (m - 1 - r) + q);
    let z_vars: Vec<Term> = (0..q).map(|jj| Term::bound(q - 1 - jj)).collect();
    ih_args.push(Term::apps(a_r, z_vars));
    build_pi(&dprime, Term::apps(motive_at_ih, ih_args))
}

/// The dependent minor-premise (method) type for constructor `idx`,
/// obtained by instantiating its stored template with the concrete
/// parameters and motive (pure substitution — all shifting is handled by
/// `subst_top`).
pub fn method_type(
    _env: &Env,
    ind: &Inductive,
    idx: usize,
    params: &[Term],
    motive: &Term,
) -> Result<Term, TypeError> {
    instantiate_template(&ind.ctors[idx].method_template, params, motive)
}

/// The non-recursive **case** (`Match`) minor-premise type for constructor
/// `idx` — like [`method_type`] but with no induction hypotheses.
pub fn match_type(
    _env: &Env,
    ind: &Inductive,
    idx: usize,
    params: &[Term],
    motive: &Term,
) -> Result<Term, TypeError> {
    instantiate_template(&ind.ctors[idx].match_template, params, motive)
}

/// Instantiate a method/match template `Π params. Π(motive). T` with the
/// concrete parameters and motive (pure substitution).
fn instantiate_template(template: &Term, params: &[Term], motive: &Term) -> Result<Term, TypeError> {
    let mut t = template.clone();
    for p in params {
        let next = match t.kind() {
            TermKind::Pi(_dom, body) => subst_top(body, p),
            _ => return Err(TypeError::BadElim("parameter arity".into())),
        };
        t = next;
    }
    match t.kind() {
        TermKind::Pi(_dom, body) => Ok(subst_top(body, motive)),
        _ => Err(TypeError::BadElim("motive instantiation".into())),
    }
}

/// The **mutual** minor-premise type for member `b`'s constructor `idx`,
/// obtained by instantiating its mutual template with the concrete shared
/// `params` then **all `g` motives** (in group order, `P_0 … P_{g-1}`).
pub fn mut_method_type(
    ind: &Inductive,
    idx: usize,
    params: &[Term],
    motives: &[Term],
) -> Result<Term, TypeError> {
    let mut t = ind.ctors[idx].mut_method_template.clone();
    for p in params {
        t = pi_subst(t, p)?;
    }
    for pm in motives {
        t = pi_subst(t, pm)?;
    }
    Ok(t)
}

fn pi_subst(t: Term, arg: &Term) -> Result<Term, TypeError> {
    match t.kind() {
        TermKind::Pi(_dom, body) => Ok(subst_top(body, arg)),
        _ => Err(TypeError::BadElim("template arity".into())),
    }
}

/// The expected type of a motive for inductive `member` eliminating into
/// `elim_sort`: `Π(indices[params]). I member params indices → Sort(elim_sort)`.
/// Used to robustly validate every motive of a mutual recursor (arity, the
/// right inductive, and the shared elimination universe).
pub fn expected_motive_type(
    env: &Env,
    member: &str,
    params: &[Term],
    elim_sort: Univ,
) -> Option<Term> {
    let ind = env.inductive(member)?;
    // arity = Π params. Π indices. Sort, then instantiate the params.
    let arity = build_pi(&ind.params, build_pi(&ind.indices, Term::sort(ind.sort)));
    let mut t = arity;
    for p in params {
        let next = match t.kind() {
            TermKind::Pi(_dom, body) => subst_top(body, p),
            _ => return None,
        };
        t = next;
    }
    // t = Π indices[params]. Sort
    let (index_doms, _) = peel_all_pis(&t);
    let n = index_doms.len();
    // major domain in ctx [indices(n)]: I member params index_vars
    let mut spine: Vec<Term> = params.iter().map(|x| shift(n, 0, x)).collect();
    spine.extend((0..n).map(|i| Term::bound(n - 1 - i)));
    let major_dom = Term::apps(Term::cnst(member.to_string()), spine);
    Some(build_pi(&index_doms, Term::pi(major_dom, Term::sort(elim_sort))))
}
