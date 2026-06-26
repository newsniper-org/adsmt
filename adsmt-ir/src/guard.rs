//! The **structural-decrease guard** for `fix` — the soundness-critical
//! termination check. A `fix f : ty := body` decreasing on argument
//! `rec_arg` is admitted only if every recursive call `f …` passes, in
//! position `rec_arg`, a variable that is a **strict structural subterm**
//! of the original recursive argument (one exposed by destructuring it
//! with [`Match`](crate::Term::Match) / [`Elim`](crate::Term::Elim)).
//!
//! This is **deliberately conservative**: it rejects any pattern it cannot
//! prove decreasing (a non-variable recursive argument, `f` used other than
//! as the head of a fully-applied call, recursion guarded by a match on a
//! non-subterm, …). Conservative rejection is the only safe direction — a
//! too-lenient guard would admit a non-terminating term, which inhabits
//! every type and so proves `False`, exactly the prime-directive
//! violation. Completeness (accepting more valid fixpoints) is a later,
//! never-at-the-cost-of-soundness concern.
//!
//! Soundness argument: `smaller` only ever holds de Bruijn variables bound
//! as *recursive-position constructor arguments* obtained by destructuring
//! the recursive argument (or a variable already in `smaller`); such a
//! variable is a strict structural subterm of the recursive argument. A
//! recursive call is allowed only when its `rec_arg` is in `smaller`. With
//! μ-reduction firing only on constructor form, every recursive call
//! therefore strictly decreases a well-founded structural measure.

use std::collections::HashSet;

use crate::env::Env;
use crate::term::{Term, TermKind, collect_spine};

/// Whether `body` of `fix f : _ := body` (decreasing on `rec_arg`) is
/// structurally guarded. `body` is read in the context extended by the
/// recursive function `f` (`Bound(0)`).
pub fn guard_ok(env: &Env, rec_arg: usize, body: &Term) -> bool {
    // Peel the `rec_arg+1` leading λs: the last binds the decreasing
    // variable `x`. Fewer ⇒ the function does not even abstract its
    // recursive argument — reject.
    let mut cur = body.clone();
    let mut f = 0usize; // index of the recursive function in the current scope
    for _ in 0..=rec_arg {
        let next = match cur.kind() {
            TermKind::Lam(dom, b) => {
                // a binder domain may not (ab)use `f`
                if !ok(env, rec_arg, dom, f, usize::MAX, &HashSet::new()) {
                    return false;
                }
                f += 1;
                b.clone()
            }
            _ => return false,
        };
        cur = next;
    }
    // Now `f = rec_arg+1`, and the decreasing variable `x = Bound(0)`.
    ok(env, rec_arg, &cur, f, 0, &HashSet::new())
}

fn shift_set(s: &HashSet<usize>) -> HashSet<usize> {
    s.iter().map(|&i| i + 1).collect()
}

/// `f` = de Bruijn index of the recursive function, `x` = the decreasing
/// variable, `smaller` = variables known to be strict subterms of `x`.
fn ok(env: &Env, rec_arg: usize, t: &Term, f: usize, x: usize, smaller: &HashSet<usize>) -> bool {
    match t.kind() {
        TermKind::Sort(_) | TermKind::Const(_) => true,
        // a bare `f` (not the head of a guarded call) is illegal
        TermKind::Bound(k) => *k != f,
        TermKind::App(_, _) => {
            let (head, args) = collect_spine(t);
            if head == Term::bound(f) {
                // a recursive call: fully applied past `rec_arg`, and the
                // `rec_arg`-th argument a known strict subterm.
                if args.len() <= rec_arg {
                    return false;
                }
                let decreasing =
                    matches!(args[rec_arg].kind(), TermKind::Bound(j) if smaller.contains(j));
                decreasing && args.iter().all(|a| ok(env, rec_arg, a, f, x, smaller))
            } else {
                ok(env, rec_arg, &head, f, x, smaller)
                    && args.iter().all(|a| ok(env, rec_arg, a, f, x, smaller))
            }
        }
        TermKind::Lam(dom, body) | TermKind::Pi(dom, body) => {
            ok(env, rec_arg, dom, f, x, smaller)
                && ok(env, rec_arg, body, f + 1, x + 1, &shift_set(smaller))
        }
        TermKind::Let(ty, v, b) => {
            if !ok(env, rec_arg, ty, f, x, smaller) || !ok(env, rec_arg, v, f, x, smaller) {
                return false;
            }
            // ζ-alias (M2.8): if the bound value is a known *strict subterm*
            // variable, the let-bound variable (`Bound(0)` in the body)
            // aliases it — so a recursive call on it is sound. ζ fires before
            // μ inspects the recursive argument, so `f y` with `let y := j`
            // reduces identically to `f j`. We only ever GROW the recognized-
            // subterm set with an alias of an already-smaller var (never `x`
            // itself, never a non-variable), so the call-acceptance rule is
            // unchanged — over-acceptance is impossible.
            let mut body_smaller = shift_set(smaller);
            if let TermKind::Bound(j) = v.kind()
                && smaller.contains(j)
            {
                body_smaller.insert(0);
            }
            ok(env, rec_arg, b, f + 1, x + 1, &body_smaller)
        }
        TermKind::Elim(ind, motive, minors, major) | TermKind::Match(ind, motive, minors, major) => {
            if !ok(env, rec_arg, motive, f, x, smaller)
                || !ok(env, rec_arg, major, f, x, smaller)
            {
                return false;
            }
            // Destructuring `x` (or a known subterm) exposes strict subterms.
            let destructured =
                matches!(major.kind(), TermKind::Bound(j) if *j == x || smaller.contains(j));
            let inductive = match env.inductive(ind) {
                Some(i) => i,
                None => return false,
            };
            if minors.len() != inductive.ctors.len() {
                return false;
            }
            for (ci, minor) in minors.iter().enumerate() {
                let ctor = &inductive.ctors[ci];
                let pass = if destructured {
                    ok_minor(env, rec_arg, minor, ctor.args_count, &ctor.rec_positions, f, x, smaller)
                } else {
                    ok(env, rec_arg, minor, f, x, smaller)
                };
                if !pass {
                    return false;
                }
            }
            true
        }
        TermKind::Fix { ty, body, .. } => {
            ok(env, rec_arg, ty, f, x, smaller)
                && ok(env, rec_arg, body, f + 1, x + 1, &shift_set(smaller))
        }
        // Conservative: a mutual eliminator exposes no tracked subterms, so a
        // `fix` recursing through it is rejected (sound — rejects more). Its
        // sub-terms are still guard-checked.
        TermKind::MutElim(_member, motives, minors, major) => {
            ok(env, rec_arg, major, f, x, smaller)
                && motives.iter().all(|m| ok(env, rec_arg, m, f, x, smaller))
                && minors.iter().all(|m| ok(env, rec_arg, m, f, x, smaller))
        }
    }
}

/// Walk a minor premise of a destructuring match: peel its `c` constructor-
/// argument λs, then mark the **recursive-position** arguments as strict
/// subterms (`smaller`) inside the branch body.
#[allow(clippy::too_many_arguments)]
fn ok_minor(
    env: &Env,
    rec_arg: usize,
    minor: &Term,
    c: usize,
    rec_positions: &[usize],
    f: usize,
    x: usize,
    smaller: &HashSet<usize>,
) -> bool {
    let mut cur = minor.clone();
    let mut f = f;
    let mut x = x;
    let mut sm = smaller.clone();
    for _ in 0..c {
        let next = match cur.kind() {
            TermKind::Lam(dom, body) => {
                if !ok(env, rec_arg, dom, f, x, &sm) {
                    return false;
                }
                f += 1;
                x += 1;
                sm = shift_set(&sm);
                body.clone()
            }
            // not a full constructor-arg λ-telescope: cannot track the
            // subterms — fall back to plain guarding (still sound).
            _ => return ok(env, rec_arg, &cur, f, x, &sm),
        };
        cur = next;
    }
    // Under the `c` argument binders, argument `i` is `Bound(c-1-i)`; the
    // recursive ones are strict subterms of the matched term.
    for &r in rec_positions {
        sm.insert(c - 1 - r);
    }
    ok(env, rec_arg, &cur, f, x, &sm)
}
