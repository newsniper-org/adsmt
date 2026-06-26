//! Kernel terms for the dependent λΠ core, de Bruijn-indexed and
//! nameless — so α-equivalence is *structural* equality and the
//! checker needs no fresh-name supply.
//!
//! The grammar is the Pure-Type-System core of CIC: sorts, a binder
//! context (`Bound`), global references (`Const`), application, and
//! the three binders Π / λ / let. Inductive types, constructors and
//! recursors are the **M2** extension (see `DESIGN.md`); they ride on
//! top of this core without changing it.
//!
//! ## Hash-consing
//!
//! Every [`Term`] is **hash-consed**: a `Term` is a thin handle
//! (`Arc<TermData>`) and all construction goes through a global interner
//! ([`intern`]), so two *structurally* equal terms share the **same**
//! allocation. Consequently `==` is `Arc::ptr_eq` and `Hash` is a cached
//! structural hash — both **O(1)** regardless of term size (the M3-2 port;
//! the §7 prerequisite for the §8 conversion/NbE memo). Match on the payload
//! through [`Term::kind`]. α-equivalence is still plain `==` because the
//! representation is nameless.

use std::collections::HashMap;
use std::collections::hash_map::DefaultHasher;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, LazyLock, Mutex};

/// Universe levels: an **impredicative `Prop`** (where every paradigm's
/// *propositions* live — SMT-LIB's `Bool`, ASP atoms, CP literals) plus
/// a **predicative `Type(n)`** tower (`Type(0)` is the data universe).
///
/// Impredicative `Prop` is what lets quantifiers be ordinary Π-terms
/// (`∀x:A. P x : Prop` for any `A`, even `A : Type`), which is exactly
/// the "everything is a term, formula = `Bool` term, quantifier = HO
/// function" shape SMT-LIB 3.0's kernel asks for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Univ {
    Prop,
    Type(u32),
}

impl Univ {
    /// The sort that classifies this sort: `Prop : Type(0)`,
    /// `Type(n) : Type(n+1)`.
    pub fn type_of(self) -> Univ {
        match self {
            Univ::Prop => Univ::Type(0),
            Univ::Type(n) => Univ::Type(n + 1),
        }
    }

    /// The PTS **product rule** for `Π(_:A). B` where `A : dom` and
    /// `B : cod`:
    ///   * codomain `Prop` ⟹ `Prop` (impredicative: any product *into*
    ///     a proposition is a proposition);
    ///   * otherwise the predicative `max` of the two `Type` levels.
    ///
    /// This is the CIC specification; cumulativity (`Type(i) ≤ Type(j)`)
    /// is intentionally **not** yet modeled — see `DESIGN.md` §frontier.
    pub fn product(dom: Univ, cod: Univ) -> Univ {
        match cod {
            Univ::Prop => Univ::Prop,
            Univ::Type(j) => match dom {
                Univ::Prop => Univ::Type(j),
                Univ::Type(i) => Univ::Type(i.max(j)),
            },
        }
    }
}

/// The structural payload of a [`Term`]. Match on it through
/// [`Term::kind`]; build via the constructors on [`Term`] (each interns).
/// Children are themselves (interned) [`Term`]s, so the payload carries no
/// extra boxing.
#[derive(Debug)]
pub enum TermKind {
    /// A sort used as a term.
    Sort(Univ),
    /// de Bruijn index into the local binder context (`0` = innermost).
    Bound(usize),
    /// A reference to a global declaration in the [`Env`](crate::Env).
    Const(String),
    /// Application `f a`.
    App(Term, Term),
    /// Dependent abstraction `λ(_:dom). body`.
    Lam(Term, Term),
    /// Dependent function type `Π(_:dom). cod`.
    Pi(Term, Term),
    /// `let _ : ty := val in body` — typed as `(λ(_:ty). body) val`,
    /// ζ-reduced in [`whnf`](crate::whnf).
    Let(Term, Term, Term),
    /// Dependent **eliminator** (recursor) application for an inductive,
    /// `Elim(ind, motive, minors, major)` = `ind.rec motive minors… major`.
    /// The recursor is a kernel *primitive* (a typing rule + ι-reduction),
    /// not a definable constant — this is how a dependent eliminator is
    /// expressed without universe polymorphism. The inductive's parameters
    /// are recovered from `major`'s type, so they are not stored here.
    Elim(String, Term, Vec<Term>, Term),
    /// **Non-recursive case analysis** `Match(ind, motive, minors, major)`:
    /// like [`Elim`](TermKind::Elim) but the minor premises receive *no*
    /// induction hypotheses. The case principle a guarded
    /// [`Fix`](TermKind::Fix) destructures with.
    Match(String, Term, Vec<Term>, Term),
    /// **Guarded fixpoint** `fix f : ty := body`, decreasing on argument
    /// `rec_arg`. `body` is read in the context extended by the recursive
    /// function `f : ty` (`Bound(0)`); `ty` is in the outer context. Only
    /// admitted when the structural-decrease guard passes
    /// (`guard::guard_ok`); μ-reduces only when applied with its `rec_arg`
    /// in constructor form.
    Fix { rec_arg: usize, ty: Term, body: Term },
    /// **Mutual dependent eliminator** `MutElim(member, motives, minors,
    /// major)` over a registered mutual group. `member` = the group member
    /// the `major` inhabits. `motives` = the `g`-tuple `(P_0..P_{g-1})` in
    /// group order. `minors` = one method per constructor of *every* group
    /// member, concatenated in `(member, ctor)` order.
    MutElim(String, Vec<Term>, Vec<Term>, Term),
}

/// The interned record behind a [`Term`]: its payload plus a cached
/// structural hash (computed once at [`intern`] time).
#[derive(Debug)]
struct TermData {
    kind: TermKind,
    hash: u64,
}

/// A kernel term — a hash-consed handle. Structurally equal terms share one
/// [`TermData`] allocation, so [`PartialEq`] is `Arc::ptr_eq` and [`Hash`]
/// hashes the cached structural hash, both **O(1)**. Cloning is one
/// `Arc::clone`. Build via the constructors (`Term::app`, `Term::pi`, …);
/// destructure via [`kind`](Term::kind).
#[derive(Clone)]
pub struct Term(Arc<TermData>);

impl PartialEq for Term {
    /// O(1): after interning, structural equality *is* pointer equality.
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for Term {}

impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.hash);
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

// ── the hash-cons interner ──────────────────────────────────────────────
//
// A global, zero-dependency interner: a `Mutex`-guarded map from a payload's
// structural hash to a bucket of interned terms with that hash. Interning a
// payload probes its bucket by *structural* equality (`kind_eq`, which is
// O(arity) because the children are already interned ⇒ their `==` is
// `ptr_eq`); a hit returns the shared `Term`, a miss allocates one. Being
// global, structurally equal terms share one `Arc` across *all* threads, so
// `==`/`Hash` are sound regardless of which thread built a term.
//
// First-cut policy: the interner holds *strong* references, so interned
// terms are never reclaimed (an arena for the process lifetime). This is
// fine for a checker that processes queries and exits; a `Weak`-based GC
// (as in `adsmt-core`) is a later refinement, not a soundness concern.

static INTERNER: LazyLock<Mutex<HashMap<u64, Vec<Term>>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// Hash a payload as `(tag, children's cached hashes, leaf data)` with a
/// fixed-seed [`DefaultHasher`] — deterministic, and O(arity) because each
/// child contributes its cached `u64` (via [`Term`]'s [`Hash`]).
fn kind_hash(k: &TermKind) -> u64 {
    let mut h = DefaultHasher::new();
    match k {
        TermKind::Sort(u) => {
            0u8.hash(&mut h);
            u.hash(&mut h);
        }
        TermKind::Bound(i) => {
            1u8.hash(&mut h);
            i.hash(&mut h);
        }
        TermKind::Const(c) => {
            2u8.hash(&mut h);
            c.hash(&mut h);
        }
        TermKind::App(f, a) => {
            3u8.hash(&mut h);
            f.hash(&mut h);
            a.hash(&mut h);
        }
        TermKind::Lam(d, b) => {
            4u8.hash(&mut h);
            d.hash(&mut h);
            b.hash(&mut h);
        }
        TermKind::Pi(d, b) => {
            5u8.hash(&mut h);
            d.hash(&mut h);
            b.hash(&mut h);
        }
        TermKind::Let(t, v, b) => {
            6u8.hash(&mut h);
            t.hash(&mut h);
            v.hash(&mut h);
            b.hash(&mut h);
        }
        TermKind::Elim(ind, m, minors, major) => {
            7u8.hash(&mut h);
            ind.hash(&mut h);
            m.hash(&mut h);
            minors.hash(&mut h);
            major.hash(&mut h);
        }
        TermKind::Match(ind, m, minors, major) => {
            8u8.hash(&mut h);
            ind.hash(&mut h);
            m.hash(&mut h);
            minors.hash(&mut h);
            major.hash(&mut h);
        }
        TermKind::Fix { rec_arg, ty, body } => {
            9u8.hash(&mut h);
            rec_arg.hash(&mut h);
            ty.hash(&mut h);
            body.hash(&mut h);
        }
        TermKind::MutElim(member, motives, minors, major) => {
            10u8.hash(&mut h);
            member.hash(&mut h);
            motives.hash(&mut h);
            minors.hash(&mut h);
            major.hash(&mut h);
        }
    }
    h.finish()
}

/// Structural equality of two payloads — tag + leaf data + child equality,
/// where child equality is [`Term`]'s O(1) `ptr_eq` (children are interned).
/// This is the interner's collision-resolution probe; it is the *only* place
/// that compares payloads structurally.
fn kind_eq(a: &TermKind, b: &TermKind) -> bool {
    use TermKind::*;
    match (a, b) {
        (Sort(x), Sort(y)) => x == y,
        (Bound(x), Bound(y)) => x == y,
        (Const(x), Const(y)) => x == y,
        (App(f1, a1), App(f2, a2)) => f1 == f2 && a1 == a2,
        (Lam(d1, b1), Lam(d2, b2)) => d1 == d2 && b1 == b2,
        (Pi(d1, b1), Pi(d2, b2)) => d1 == d2 && b1 == b2,
        (Let(t1, v1, b1), Let(t2, v2, b2)) => t1 == t2 && v1 == v2 && b1 == b2,
        (Elim(i1, m1, n1, j1), Elim(i2, m2, n2, j2)) => {
            i1 == i2 && m1 == m2 && n1 == n2 && j1 == j2
        }
        (Match(i1, m1, n1, j1), Match(i2, m2, n2, j2)) => {
            i1 == i2 && m1 == m2 && n1 == n2 && j1 == j2
        }
        (
            Fix { rec_arg: r1, ty: t1, body: b1 },
            Fix { rec_arg: r2, ty: t2, body: b2 },
        ) => r1 == r2 && t1 == t2 && b1 == b2,
        (MutElim(m1, o1, n1, j1), MutElim(m2, o2, n2, j2)) => {
            m1 == m2 && o1 == o2 && n1 == n2 && j1 == j2
        }
        _ => false,
    }
}

/// Canonicalise a payload against the global interner and return the shared
/// [`Term`]. Re-interning a structurally equal payload returns the same
/// handle (`Arc::ptr_eq` holds).
fn intern(kind: TermKind) -> Term {
    let h = kind_hash(&kind);
    // Recover from a poisoned lock instead of cascading panics: the interner
    // is a pure cache; a prior panic leaves it structurally valid.
    let mut map = INTERNER.lock().unwrap_or_else(|p| p.into_inner());
    let bucket = map.entry(h).or_default();
    for t in bucket.iter() {
        if kind_eq(&t.0.kind, &kind) {
            return t.clone();
        }
    }
    let t = Term(Arc::new(TermData { kind, hash: h }));
    bucket.push(t.clone());
    t
}

impl Term {
    /// The interned payload, for matching.
    pub fn kind(&self) -> &TermKind {
        &self.0.kind
    }

    /// A stable per-process identity for this interned term (the `Arc`
    /// address). Structurally equal terms share one allocation, so this is a
    /// canonical key: equal terms have equal `id`, distinct terms distinct
    /// `id`. Used (`pub(crate)`) to canonicalize the unordered argument pair of
    /// the conversion memo.
    pub(crate) fn id(&self) -> usize {
        Arc::as_ptr(&self.0) as *const () as usize
    }

    pub fn sort(u: Univ) -> Term {
        intern(TermKind::Sort(u))
    }
    /// The proposition sort `Prop`.
    pub fn prop() -> Term {
        Term::sort(Univ::Prop)
    }
    /// The data sort `Type(n)`.
    pub fn type_(n: u32) -> Term {
        Term::sort(Univ::Type(n))
    }
    pub fn bound(i: usize) -> Term {
        intern(TermKind::Bound(i))
    }
    pub fn cnst(name: impl Into<String>) -> Term {
        intern(TermKind::Const(name.into()))
    }
    pub fn app(f: Term, a: Term) -> Term {
        intern(TermKind::App(f, a))
    }
    pub fn lam(dom: Term, body: Term) -> Term {
        intern(TermKind::Lam(dom, body))
    }
    pub fn pi(dom: Term, cod: Term) -> Term {
        intern(TermKind::Pi(dom, cod))
    }
    /// The **non-dependent** arrow `dom → cod`. The codomain is shifted
    /// because in de Bruijn it now sits under the Π binder even though it
    /// does not mention it.
    pub fn arrow(dom: Term, cod: Term) -> Term {
        Term::pi(dom, shift(1, 0, &cod))
    }
    pub fn let_(ty: Term, val: Term, body: Term) -> Term {
        intern(TermKind::Let(ty, val, body))
    }
    /// Eliminator application `ind.rec motive minors… major`.
    pub fn elim(ind: impl Into<String>, motive: Term, minors: Vec<Term>, major: Term) -> Term {
        intern(TermKind::Elim(ind.into(), motive, minors, major))
    }
    /// Non-recursive case analysis `ind.match motive minors… major`.
    pub fn mtch(ind: impl Into<String>, motive: Term, minors: Vec<Term>, major: Term) -> Term {
        intern(TermKind::Match(ind.into(), motive, minors, major))
    }
    /// Guarded fixpoint `fix f : ty := body`, decreasing on `rec_arg`.
    pub fn fix(rec_arg: usize, ty: Term, body: Term) -> Term {
        intern(TermKind::Fix { rec_arg, ty, body })
    }
    /// Mutual eliminator over `member`'s group with a tuple of `motives`.
    pub fn mutelim(
        member: impl Into<String>,
        motives: Vec<Term>,
        minors: Vec<Term>,
        major: Term,
    ) -> Term {
        intern(TermKind::MutElim(member.into(), motives, minors, major))
    }
    /// Left-associated application `f a1 a2 …`.
    pub fn apps(f: Term, args: impl IntoIterator<Item = Term>) -> Term {
        args.into_iter().fold(f, Term::app)
    }
}

/// Shift free de Bruijn indices `>= cutoff` up by `d`.
pub fn shift(d: usize, cutoff: usize, t: &Term) -> Term {
    match t.kind() {
        TermKind::Sort(_) | TermKind::Const(_) => t.clone(),
        TermKind::Bound(k) => {
            if *k >= cutoff {
                Term::bound(k + d)
            } else {
                t.clone()
            }
        }
        TermKind::App(f, a) => Term::app(shift(d, cutoff, f), shift(d, cutoff, a)),
        TermKind::Lam(dom, b) => Term::lam(shift(d, cutoff, dom), shift(d, cutoff + 1, b)),
        TermKind::Pi(dom, b) => Term::pi(shift(d, cutoff, dom), shift(d, cutoff + 1, b)),
        TermKind::Let(ty, v, b) => Term::let_(
            shift(d, cutoff, ty),
            shift(d, cutoff, v),
            shift(d, cutoff + 1, b),
        ),
        TermKind::Elim(ind, motive, minors, major) => Term::elim(
            ind.clone(),
            shift(d, cutoff, motive),
            minors.iter().map(|m| shift(d, cutoff, m)).collect(),
            shift(d, cutoff, major),
        ),
        TermKind::Match(ind, motive, minors, major) => Term::mtch(
            ind.clone(),
            shift(d, cutoff, motive),
            minors.iter().map(|m| shift(d, cutoff, m)).collect(),
            shift(d, cutoff, major),
        ),
        TermKind::Fix { rec_arg, ty, body } => Term::fix(
            *rec_arg,
            shift(d, cutoff, ty),
            shift(d, cutoff + 1, body),
        ),
        TermKind::MutElim(member, motives, minors, major) => Term::mutelim(
            member.clone(),
            motives.iter().map(|m| shift(d, cutoff, m)).collect(),
            minors.iter().map(|m| shift(d, cutoff, m)).collect(),
            shift(d, cutoff, major),
        ),
    }
}

/// Instantiate the binder at relative `depth` with `arg`, decrementing
/// strictly-higher free indices (the substitution underlying β/ζ). `arg`
/// is lifted past every binder crossed so its own free variables stay
/// correctly scoped.
fn inst(t: &Term, depth: usize, arg: &Term) -> Term {
    match t.kind() {
        TermKind::Sort(_) | TermKind::Const(_) => t.clone(),
        TermKind::Bound(k) => {
            if *k == depth {
                shift(depth, 0, arg)
            } else if *k > depth {
                Term::bound(k - 1)
            } else {
                t.clone()
            }
        }
        TermKind::App(f, a) => Term::app(inst(f, depth, arg), inst(a, depth, arg)),
        TermKind::Lam(dom, b) => Term::lam(inst(dom, depth, arg), inst(b, depth + 1, arg)),
        TermKind::Pi(dom, b) => Term::pi(inst(dom, depth, arg), inst(b, depth + 1, arg)),
        TermKind::Let(ty, v, b) => Term::let_(
            inst(ty, depth, arg),
            inst(v, depth, arg),
            inst(b, depth + 1, arg),
        ),
        TermKind::Elim(ind, motive, minors, major) => Term::elim(
            ind.clone(),
            inst(motive, depth, arg),
            minors.iter().map(|m| inst(m, depth, arg)).collect(),
            inst(major, depth, arg),
        ),
        TermKind::Match(ind, motive, minors, major) => Term::mtch(
            ind.clone(),
            inst(motive, depth, arg),
            minors.iter().map(|m| inst(m, depth, arg)).collect(),
            inst(major, depth, arg),
        ),
        TermKind::Fix { rec_arg, ty, body } => Term::fix(
            *rec_arg,
            inst(ty, depth, arg),
            inst(body, depth + 1, arg),
        ),
        TermKind::MutElim(member, motives, minors, major) => Term::mutelim(
            member.clone(),
            motives.iter().map(|m| inst(m, depth, arg)).collect(),
            minors.iter().map(|m| inst(m, depth, arg)).collect(),
            inst(major, depth, arg),
        ),
    }
}

/// Build the Π-telescope `Π tele[0]. … Π tele[m-1]. body`. Each `tele[i]`
/// is read in the context extended by `tele[0..i]`; `body` in the context
/// extended by all of `tele`.
pub fn build_pi(tele: &[Term], body: Term) -> Term {
    tele.iter().rev().fold(body, |acc, dom| Term::pi(dom.clone(), acc))
}

/// Peel exactly `n` Π binders off `t`, returning the domain telescope
/// (`out[i]` in the context of `out[0..i]`) and the residual body. Returns
/// `None` if `t` does not start with `n` Πs.
pub fn peel_pis(t: &Term, n: usize) -> Option<(Vec<Term>, Term)> {
    let mut doms = Vec::new();
    let mut cur = t.clone();
    for _ in 0..n {
        let next = match cur.kind() {
            TermKind::Pi(dom, body) => {
                doms.push(dom.clone());
                body.clone()
            }
            _ => return None,
        };
        cur = next;
    }
    Some((doms, cur))
}

/// Peel *every* leading Π binder off `t`, returning the domain telescope
/// and the (non-Π) residual body.
// Not a `while let`: the body reassigns the matched scrutinee (`cur`), which
// the match borrow precludes — hence compute-next-then-assign.
#[allow(clippy::while_let_loop)]
pub fn peel_all_pis(t: &Term) -> (Vec<Term>, Term) {
    let mut doms = Vec::new();
    let mut cur = t.clone();
    loop {
        let next = match cur.kind() {
            TermKind::Pi(dom, body) => {
                doms.push(dom.clone());
                body.clone()
            }
            _ => break,
        };
        cur = next;
    }
    (doms, cur)
}

/// Decompose a head-application spine `((c a_1) a_2) … a_k` into the head
/// `Const` name and its arguments `[a_1, …, a_k]`, if the head is a
/// `Const`.
pub fn as_const_app(t: &Term) -> Option<(String, Vec<Term>)> {
    let mut args = Vec::new();
    let mut cur = t.clone();
    loop {
        let next = match cur.kind() {
            TermKind::App(f, a) => {
                args.push(a.clone());
                f.clone()
            }
            TermKind::Const(name) => {
                args.reverse();
                return Some((name.clone(), args));
            }
            _ => return None,
        };
        cur = next;
    }
}

/// Decompose any application spine into its (non-`App`) head and arguments
/// `[a_1, …, a_k]` in order.
// Not a `while let`: the body reassigns the matched scrutinee (`cur`).
#[allow(clippy::while_let_loop)]
pub fn collect_spine(t: &Term) -> (Term, Vec<Term>) {
    let mut args = Vec::new();
    let mut cur = t.clone();
    loop {
        let next = match cur.kind() {
            TermKind::App(f, a) => {
                args.push(a.clone());
                f.clone()
            }
            _ => break,
        };
        cur = next;
    }
    args.reverse();
    (cur, args)
}

/// Whether `Const(name)` occurs anywhere in `t`.
pub fn occurs(name: &str, t: &Term) -> bool {
    match t.kind() {
        TermKind::Const(c) => c == name,
        TermKind::Sort(_) | TermKind::Bound(_) => false,
        TermKind::App(f, a) => occurs(name, f) || occurs(name, a),
        TermKind::Lam(d, b) | TermKind::Pi(d, b) => occurs(name, d) || occurs(name, b),
        TermKind::Let(ty, v, b) => occurs(name, ty) || occurs(name, v) || occurs(name, b),
        TermKind::Elim(ind, m, minors, major) | TermKind::Match(ind, m, minors, major) => {
            ind == name
                || occurs(name, m)
                || minors.iter().any(|x| occurs(name, x))
                || occurs(name, major)
        }
        TermKind::Fix { ty, body, .. } => occurs(name, ty) || occurs(name, body),
        TermKind::MutElim(member, motives, minors, major) => {
            member == name
                || motives.iter().any(|x| occurs(name, x))
                || minors.iter().any(|x| occurs(name, x))
                || occurs(name, major)
        }
    }
}

/// β/ζ top-level substitution: `(λ. body) arg ⟶ subst_top(body, arg)`.
pub fn subst_top(body: &Term, arg: &Term) -> Term {
    inst(body, 0, arg)
}

impl fmt::Display for Univ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Univ::Prop => write!(f, "Prop"),
            Univ::Type(n) => write!(f, "Type({n})"),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TermKind::Sort(u) => write!(f, "{u}"),
            TermKind::Bound(k) => write!(f, "#{k}"),
            TermKind::Const(n) => write!(f, "{n}"),
            TermKind::App(g, a) => write!(f, "({g} {a})"),
            TermKind::Lam(d, b) => write!(f, "(λ:{d}. {b})"),
            TermKind::Pi(d, b) => write!(f, "(Π:{d}. {b})"),
            TermKind::Let(ty, v, b) => write!(f, "(let:{ty} := {v} in {b})"),
            TermKind::Elim(ind, motive, minors, major)
            | TermKind::Match(ind, motive, minors, major) => {
                let kw = if matches!(self.kind(), TermKind::Elim(..)) { "rec" } else { "match" };
                write!(f, "({ind}.{kw} {motive}")?;
                for m in minors {
                    write!(f, " {m}")?;
                }
                write!(f, " {major})")
            }
            TermKind::Fix { rec_arg, ty, body } => {
                write!(f, "(fix/{rec_arg} : {ty} := {body})")
            }
            TermKind::MutElim(member, motives, minors, major) => {
                write!(f, "({member}.mrec")?;
                for m in motives {
                    write!(f, " {m}")?;
                }
                write!(f, " |")?;
                for m in minors {
                    write!(f, " {m}")?;
                }
                write!(f, " {major})")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::{Hash, Hasher};

    fn hash_of(t: &Term) -> u64 {
        let mut h = DefaultHasher::new();
        t.hash(&mut h);
        h.finish()
    }

    /// The load-bearing hash-cons invariant: structurally equal terms built
    /// via **different construction paths** share one allocation, so `==`
    /// (`ptr_eq`) holds and the hash agrees. This is what makes `is_def_eq`'s
    /// O(1) `==` a *correct* structural equality.
    #[test]
    fn interning_shares_structural_equals() {
        // `(λ(:Nat). #0) (S O)` built two independent ways.
        let mk = || {
            Term::app(
                Term::lam(Term::cnst("Nat"), Term::bound(0)),
                Term::app(Term::cnst("S"), Term::cnst("O")),
            )
        };
        let a = mk();
        let b = mk();
        assert!(a == b, "structural equals must share an Arc (ptr_eq)");
        assert_eq!(hash_of(&a), hash_of(&b));
        // a deep telescope, two ways.
        let deep1 = (0..200).fold(Term::cnst("O"), |acc, _| Term::app(Term::cnst("S"), acc));
        let deep2 = (0..200).fold(Term::cnst("O"), |acc, _| Term::app(Term::cnst("S"), acc));
        assert!(deep1 == deep2);
    }

    /// The **soundness** direction: structurally *distinct* terms must NEVER
    /// share an allocation (no false dedup) — else `==` would conflate them
    /// and `is_def_eq` could accept a wrong conversion (FALSE_UNSAT).
    #[test]
    fn interning_distinguishes_distinct() {
        assert!(Term::cnst("a") != Term::cnst("b"));
        assert!(Term::bound(0) != Term::bound(1));
        assert!(Term::sort(Univ::Prop) != Term::sort(Univ::Type(0)));
        assert!(Term::app(Term::cnst("f"), Term::cnst("x")) != Term::app(Term::cnst("f"), Term::cnst("y")));
        // same children, different head variant:
        let (d, b) = (Term::cnst("A"), Term::bound(0));
        assert!(Term::lam(d.clone(), b.clone()) != Term::pi(d, b));
        // Fix differing only in rec_arg:
        let ty = Term::arrow(Term::cnst("Nat"), Term::cnst("Nat"));
        let bd = Term::lam(Term::cnst("Nat"), Term::bound(0));
        assert!(Term::fix(0, ty.clone(), bd.clone()) != Term::fix(1, ty, bd));
    }

    /// The interner is **global**, so a term built on another thread shares the
    /// same Arc as the structurally-equal one on this thread — `==`/`Hash` are
    /// sound across threads, not just within one.
    #[test]
    fn interning_is_global_across_threads() {
        let here = Term::app(Term::cnst("g"), Term::bound(3));
        let there = std::thread::spawn(|| Term::app(Term::cnst("g"), Term::bound(3)))
            .join()
            .unwrap();
        assert!(here == there, "the global interner must share across threads");
        assert_eq!(hash_of(&here), hash_of(&there));
    }
}
