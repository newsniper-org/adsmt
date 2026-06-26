//! The global environment of declarations, and the **def/open
//! modality** that is the kernel's hook for paradigm ownership.

use std::cell::RefCell;
use std::collections::HashMap;

use crate::term::{Term, Univ};

/// The **conversion memo** — the algebraic-JIT cache (DESIGN §8) at the IR.
/// Type-checking is dominated by repeated reduction: the same prelude lemmas
/// are `whnf`'d / convertibility-checked over and over inside `is_def_eq`.
/// Because terms are now hash-consed (O(1) identity), a term handle *is* its
/// content key, so the memo is a plain map from the handle to the result.
///
/// **Soundness (the §3.5 discipline):** `whnf(env, t)` and `is_def_eq(env, …)`
/// are pure functions of the env's *state* (its `def` bodies + inductive
/// structure). Every cache entry is therefore valid only for the env-state
/// that produced it — so the memo is **cleared on every state mutation**
/// (`declare` / `register_inductive` / `register_group`) and **reset to empty
/// on clone** (a `work = env.clone()` admission probe must not inherit, nor
/// pollute, the live cache). A *hit* is thus always an exact match for the
/// current state; a *miss* falls through to full recomputation. A wrong/stale
/// hit is impossible by construction — the cache only ever holds work already
/// verified for the present env.
#[derive(Default)]
pub(crate) struct Memo {
    /// `t ↦ whnf(env, t)`.
    whnf: RefCell<HashMap<Term, Term>>,
    /// `{a,b} ↦ is_def_eq(env, a, b)` (the pair canonicalized by [`Term::id`]).
    defeq: RefCell<HashMap<(Term, Term), bool>>,
}

impl Clone for Memo {
    /// Reset on clone — a cloned env starts with an empty cache (sound: it
    /// recomputes; and it avoids deep-copying a possibly-large map into a
    /// short-lived admission `work` copy).
    fn clone(&self) -> Self {
        Memo::default()
    }
}

impl std::fmt::Debug for Memo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Memo(..)")
    }
}

impl Memo {
    fn clear(&mut self) {
        self.whnf.get_mut().clear();
        self.defeq.get_mut().clear();
    }
}

/// Canonicalize an unordered term pair (`is_def_eq` is symmetric) so
/// `(a,b)` and `(b,a)` hit the same slot. Ordering by [`Term::id`] (the
/// interned `Arc` address) is a valid total order because distinct interned
/// terms have distinct addresses. (The memo holds a strong ref to each key, so
/// the addresses stay stable for the entry's lifetime even if a `Weak`-GC
/// interner is ever introduced — see DESIGN §7.)
fn canon(a: &Term, b: &Term) -> (Term, Term) {
    if a.id() <= b.id() {
        (a.clone(), b.clone())
    } else {
        (b.clone(), a.clone())
    }
}

/// How a global constant behaves under the kernel's conversion checker —
/// the formal meaning of the surface `def` / `open` modifiers (plus the
/// two inductive-machinery kinds).
#[derive(Clone, Debug, PartialEq)]
pub enum Modality {
    /// `def` — a **closed-world** definition. Its body δ-unfolds during
    /// conversion: the constant *is* its definition. This is the
    /// ownership tag for defined / inductive / ASP atoms (rule-defined,
    /// least-model semantics downstream).
    Def(Term),
    /// `open` — a **classical / theory** parameter. Opaque to the kernel:
    /// it never δ-unfolds, because its meaning comes from the theory or
    /// the classical (open-world) reading, not from a definition. This is
    /// the ownership tag for theory atoms / uninterpreted symbols.
    Open,
    /// An inductive **type former** `I`. Opaque to δ (its structure lives
    /// in [`Env::inductive`]); a `def`-family ownership (closed-world).
    Inductive,
    /// A data **constructor** `c_j`. Opaque to δ — a constructor
    /// application is a *value* (a WHNF head); ι-reduction consumes it
    /// only when it is the major premise of an [`Elim`](crate::Term::Elim).
    Constructor,
}

/// A global declaration: its (closed, well-sorted) type plus its
/// modality.
#[derive(Clone, Debug, PartialEq)]
pub struct Decl {
    /// The declared type — always a closed term (no free de Bruijn
    /// indices), checked well-sorted when the declaration was admitted.
    pub ty: Term,
    pub modality: Modality,
}

impl Decl {
    /// The δ-reducible body, if this is a `def`.
    pub fn body(&self) -> Option<&Term> {
        match &self.modality {
            Modality::Def(b) => Some(b),
            _ => None,
        }
    }

    /// Whether this declaration is `open` (opaque to conversion).
    pub fn is_open(&self) -> bool {
        matches!(self.modality, Modality::Open)
    }
}

/// A data constructor of an [`Inductive`]. Stored with enough structure to
/// type and ι-reduce an [`Elim`](crate::Term::Elim) without re-deriving it.
#[derive(Clone, Debug, PartialEq)]
pub struct Constructor {
    pub name: String,
    /// The constructor's full closed type
    /// `Π params. Π args. I params ctor_indices`.
    pub ty: Term,
    /// Number of (non-parameter) arguments.
    pub args_count: usize,
    /// Argument positions that are **recursive** (type `I params idxᵣ`, the
    /// same parameters, any indices), in order — these receive an induction
    /// hypothesis / a recursive eliminator call.
    pub rec_positions: Vec<usize>,
    /// The dependent minor-premise (method) type, abstracted over the
    /// parameters and the motive: `Π params. Π(motive). MethodType`. The
    /// motive binder carries a placeholder type (never used — the template
    /// is only ever *instantiated* by substitution, in
    /// [`method_type`](crate::method_type), never type-checked). Built once
    /// at admission so all the de Bruijn bookkeeping is done a single time.
    pub method_template: Term,
    /// Like [`method_template`](Self::method_template) but with **no
    /// induction hypotheses** — the case (`Match`) minor-premise type. Used
    /// by the non-recursive [`Match`](crate::Term::Match) eliminator that a
    /// guarded [`Fix`](crate::Term::Fix) destructures with.
    pub match_template: Term,
    /// The **mutual** minor-premise type, abstracted over the shared params
    /// and **all `g` motives** of the group: `Π params. Π(P_0)…Π(P_{g-1}).
    /// MutMethodType`. A recursive argument of type `I_b` gets an IH at the
    /// `b`-th motive (cross-member IHs). Instantiated in
    /// [`mut_method_type`](crate::mut_method_type). For a singleton group it
    /// coincides with `method_template` (one motive).
    pub mut_method_template: Term,
    /// Argument positions that are **group-recursive** (self *or* cross-
    /// member: `I_b params idxᵣ`), in order — the positions that receive a
    /// mutual induction hypothesis. (Superset of `rec_positions`, which is
    /// the self-only subset used by the independent recursor.)
    pub mut_rec_positions: Vec<usize>,
    /// For each entry of `mut_rec_positions`, the group position `b` of the
    /// member that recursive argument belongs to (so its IH uses `P_b` and ι
    /// dispatches the sub-call to member `b`'s recursor).
    pub rec_member: Vec<usize>,
}

/// A (parameterized, **indexed**) inductive type definition. The type
/// former has type `Π params. Π indices. Sort(sort)`.
#[derive(Clone, Debug, PartialEq)]
pub struct Inductive {
    pub name: String,
    /// The parameter telescope (`params[i]` in the context of
    /// `params[0..i]`) — *uniform* across all constructors.
    pub params: Vec<Term>,
    /// The index telescope (`indices[i]` in the context of
    /// `params ++ indices[0..i]`) — may *vary* per constructor.
    pub indices: Vec<Term>,
    /// The result sort of the type former.
    pub sort: crate::term::Univ,
    pub ctors: Vec<Constructor>,
}

/// The raw **admission inputs** for one (possibly indexed, possibly mutual-
/// group-member) inductive — exactly the arguments
/// [`declare_inductive_indexed`](crate::declare_inductive_indexed) /
/// [`declare_mutual`](crate::declare_mutual) receive, *before* any positivity
/// classification or template derivation. This is what the AOT-bank stores:
/// the **inputs**, never the derived outputs (templates / `rec_positions` /
/// `ctor_of` …). See [`AdmissionStep`] and `bank.rs`.
#[derive(Clone, Debug, PartialEq)]
pub struct IndSpec {
    pub name: String,
    pub params: Vec<Term>,
    pub indices: Vec<Term>,
    pub sort: Univ,
    /// `(ctor name, arg telescope, conclusion index expressions)`.
    pub ctors: Vec<(String, Vec<Term>, Vec<Term>)>,
}

/// One entry of the [`Env`]'s **admission journal** — the exact sequence of
/// checked-admitter calls that built the environment. The AOT-bank
/// (`bank.rs`) serializes this journal; loading **replays it through the same
/// checked admitters**, so a loaded `Env` is type-checked identically to the
/// original. The bank therefore adds *no* trust beyond the admitters: a
/// corrupt / incompatible journal simply fails to replay (⇒ a `BankError` ⇒
/// the caller falls through to full elaboration), and no derived recursor
/// bookkeeping is ever banked or trusted.
#[derive(Clone, Debug, PartialEq)]
pub enum AdmissionStep {
    /// A [`define`](crate::define) call (a `def`).
    Define { name: String, ty: Term, body: Term },
    /// A [`postulate`](crate::postulate) call (an `open`).
    Postulate { name: String, ty: Term },
    /// A [`declare_inductive_indexed`](crate::declare_inductive_indexed) call
    /// (the non-indexed [`declare_inductive`](crate::declare_inductive)
    /// records here too, with an empty index telescope).
    Inductive(IndSpec),
    /// A [`declare_mutual`](crate::declare_mutual) call (members in order).
    Mutual(Vec<IndSpec>),
}

/// The global environment. Admission of a declaration goes through
/// [`define`](crate::define) / [`postulate`](crate::postulate), which
/// type-check before [`declare`](Env::declare)-ing — so every `Decl`
/// reachable here has already passed the kernel.
#[derive(Clone, Debug, Default)]
pub struct Env {
    decls: HashMap<String, Decl>,
    inductives: HashMap<String, Inductive>,
    /// Reverse index: a constructor name to its `(inductive, index)`.
    ctor_of: HashMap<String, (String, usize)>,
    /// Mutual groups, each = member names in declaration order. A singly-
    /// declared inductive is its own singleton group.
    groups: Vec<Vec<String>>,
    /// Member name → index into [`groups`](Self::groups).
    group_of: HashMap<String, usize>,
    /// The **admission journal** — every checked admission, in order — the
    /// source of truth the AOT-bank serializes. Only the *checked* admitters
    /// ([`define`](crate::define) / [`postulate`](crate::postulate) /
    /// [`declare_inductive_indexed`](crate::declare_inductive_indexed) /
    /// [`declare_mutual`](crate::declare_mutual)) append to it; the raw
    /// [`declare`](Self::declare) / [`register_inductive`](Self::register_inductive)
    /// paths do not (so a bank built from a raw-assembled `Env` is detected as
    /// incomplete by [`bank_encode`](crate::bank::bank_encode)'s self-check).
    journal: Vec<AdmissionStep>,
    /// The conversion memo (the §8 algebraic-JIT cache) — cleared on every
    /// state mutation, reset on clone. See [`Memo`].
    memo: Memo,
}

impl Env {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn lookup(&self, name: &str) -> Option<&Decl> {
        self.decls.get(name)
    }

    /// The inductive definition named `name`, if any.
    pub fn inductive(&self, name: &str) -> Option<&Inductive> {
        self.inductives.get(name)
    }

    /// If `name` is a constructor, its `(inductive name, ctor index)`.
    pub fn ctor_of(&self, name: &str) -> Option<&(String, usize)> {
        self.ctor_of.get(name)
    }

    /// The mutual group `name` belongs to (member names in order), if any.
    /// A singly-declared inductive is its own singleton group.
    pub fn group_of(&self, name: &str) -> Option<&[String]> {
        self.group_of.get(name).map(|&i| self.groups[i].as_slice())
    }

    /// Record a mutual group (the members must already be registered).
    pub fn register_group(&mut self, members: Vec<String>) {
        self.memo.clear(); // any state change invalidates the conversion memo
        let idx = self.groups.len();
        for m in &members {
            self.group_of.insert(m.clone(), idx);
        }
        self.groups.push(members);
    }

    /// Raw, **unchecked** insertion. Prefer the checked admitters
    /// [`define`](crate::define) / [`postulate`](crate::postulate) /
    /// [`declare_inductive`](crate::declare_inductive); this is `pub` only
    /// so out-of-kernel tooling can rebuild a known-good environment.
    pub fn declare(&mut self, name: String, decl: Decl) {
        self.memo.clear(); // a new/changed `def` can change δ/ι reduction
        self.decls.insert(name, decl);
    }

    /// Raw, **unchecked** registration of a checked inductive (the type
    /// former's `Decl`, every constructor's `Decl`, and the structural
    /// registries). Prefer [`declare_inductive`](crate::declare_inductive).
    pub fn register_inductive(&mut self, ind: Inductive) {
        self.memo.clear(); // new ctors/inductives change ι reduction
        // type former: Π params. Π indices. Sort
        let arity = crate::term::build_pi(&ind.indices, Term::sort(ind.sort));
        let ind_ty = crate::term::build_pi(&ind.params, arity);
        self.declare(ind.name.clone(), Decl { ty: ind_ty, modality: Modality::Inductive });
        for (idx, ctor) in ind.ctors.iter().enumerate() {
            self.declare(
                ctor.name.clone(),
                Decl { ty: ctor.ty.clone(), modality: Modality::Constructor },
            );
            self.ctor_of.insert(ctor.name.clone(), (ind.name.clone(), idx));
        }
        self.inductives.insert(ind.name.clone(), ind);
    }

    pub fn len(&self) -> usize {
        self.decls.len()
    }

    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }

    // ── conversion memo (the §8 algebraic-JIT cache; see [`Memo`]) ──────────
    // Read/write through `&self` (interior mutability). Entries are only ever
    // valid for the current env-state (any mutation clears the memo), so a hit
    // is an exact match and a miss falls through to recomputation.

    /// A cached `whnf(self, t)`, if present.
    pub(crate) fn memo_whnf_get(&self, t: &Term) -> Option<Term> {
        self.memo.whnf.borrow().get(t).cloned()
    }
    /// Record `whnf(self, t) = v`.
    pub(crate) fn memo_whnf_put(&self, t: &Term, v: &Term) {
        self.memo.whnf.borrow_mut().insert(t.clone(), v.clone());
    }
    /// A cached `is_def_eq(self, a, b)`, if present.
    pub(crate) fn memo_defeq_get(&self, a: &Term, b: &Term) -> Option<bool> {
        self.memo.defeq.borrow().get(&canon(a, b)).copied()
    }
    /// Record `is_def_eq(self, a, b) = v`.
    pub(crate) fn memo_defeq_put(&self, a: &Term, b: &Term, v: bool) {
        self.memo.defeq.borrow_mut().insert(canon(a, b), v);
    }

    /// The admission journal — every checked admission in order. The AOT-bank
    /// (`bank.rs`) serializes exactly this.
    pub fn journal(&self) -> &[AdmissionStep] {
        &self.journal
    }

    /// Append a step to the admission journal. Called by the checked admitters
    /// *after* a successful admission; never by the raw `declare` path.
    pub(crate) fn record(&mut self, step: AdmissionStep) {
        self.journal.push(step);
    }

    /// Structural equality of the **semantic** content (declarations,
    /// inductives, and the registries) — the journal itself is excluded.
    /// `bank_encode`'s self-check uses this to confirm replaying the journal
    /// reproduces the environment exactly (so a bank built from an `Env` that
    /// used the raw, journal-less `declare` paths is rejected, not silently
    /// shipped with missing declarations).
    pub(crate) fn semantically_eq(&self, other: &Env) -> bool {
        self.decls == other.decls
            && self.inductives == other.inductives
            && self.ctor_of == other.ctor_of
            && self.groups == other.groups
            && self.group_of == other.group_of
    }
}
