//! Theory of (inductive and finite) datatypes.
//!
//! v0.3 ships **finite-enum disjointness + cardinality witness** —
//! the most load-bearing case for polite combination (sec 26). A
//! finite datatype like
//!
//! ```text
//! data Color: Red | Green | Blue
//! ```
//!
//! contributes:
//! - constructor disjointness: `Red ≠ Green`, etc.
//! - cardinality 3 to the polite reconciliation step
//!
//! Inductive datatypes (`Nat = Zero | Succ Nat`, etc.) return ω. Their
//! structural reasoning — constructor disjointness, **injectivity**,
//! **selector reduction** (literal + through congruence), **acyclicity**
//! (occurs-check via a class-containment-graph cycle), and
//! **exhaustiveness** (a value excluded from every constructor is unsat)
//! — is all in place (#330/#331). A z3-differential over 7200+ random
//! datatype queries agrees with z3 modulo a conservative ~0.1% false-sat
//! residual (the single-survivor → acyclicity chain).

use std::collections::HashMap;

use adsmt_cert::witness::{
    DatatypeReason, DatatypeWitness, PoliteWitness, TheoryWitness,
};
use adsmt_core::{Term, TermInner, Type};

use crate::trait_::{AssertResult, CheckResult, Literal, Theory};

/// Description of one declared datatype.
#[derive(Clone, Debug)]
pub struct DatatypeDecl {
    pub sort_name: String,
    pub constructors: Vec<String>,
    pub is_finite: bool,
    /// v0.19 C.4 — per-constructor argument arity. Index aligns
    /// with `constructors`. `arities[i] = 0` for nullary
    /// constructors (the finite-enum case); positive values for
    /// argument-bearing constructors (`Succ Nat` → 1,
    /// `Cons head tail` → 2).
    pub arities: Vec<u32>,
    /// rc.30 (Y4) — per-constructor selector (field-accessor) names.
    /// `selectors[i]` aligns with `constructors[i]` and has length
    /// `arities[i]`. Empty inner vecs for nullary constructors.
    /// Drives selector-reduction `sel_j(C(x_1..x_n)) = x_j`.
    pub selectors: Vec<Vec<String>>,
    /// rc.30 (Y4) — type parameters for a parametric datatype
    /// (`(Seq T)` → `["T"]`). Empty for monomorphic datatypes.
    pub params: Vec<String>,
    /// Per-constructor **field SORT names** (not just selector names),
    /// aligned with `selectors`. Empty (the default) when a producer
    /// didn't thread them — recognizers that need the field sort (the
    /// Peano `IntegerLike` bridge: "the unary ctor's field sort == the
    /// carrier sort") must then FAIL CLOSED. Populated from the parser's
    /// already-computed field types so the bridge can tell `succ(pred
    /// Nat)` (recursive → Peano) from `wrap(Int)` (foreign field → NOT
    /// Peano) — without this the structural shape alone over-fires.
    pub field_sorts: Vec<Vec<String>>,
}

impl DatatypeDecl {
    pub fn finite_enum(sort_name: impl Into<String>, constructors: Vec<String>) -> Self {
        let len = constructors.len();
        Self {
            sort_name: sort_name.into(),
            constructors,
            is_finite: true,
            arities: vec![0u32; len],
            selectors: vec![Vec::new(); len],
            params: Vec::new(),
            field_sorts: vec![Vec::new(); len],
        }
    }

    pub fn inductive(sort_name: impl Into<String>, constructors: Vec<String>) -> Self {
        let len = constructors.len();
        Self {
            sort_name: sort_name.into(),
            constructors,
            is_finite: false,
            // Inductive constructors default to 0 (nullary); use
            // `with_arities` to populate.
            arities: vec![0u32; len],
            selectors: vec![Vec::new(); len],
            params: Vec::new(),
            field_sorts: vec![Vec::new(); len],
        }
    }

    /// Set per-constructor field SORT names (positional; aligned with
    /// `constructors`). Needed by the Peano `IntegerLike` bridge to
    /// verify a unary constructor recurses on its own sort.
    pub fn with_field_sorts(mut self, field_sorts: Vec<Vec<String>>) -> Self {
        assert_eq!(
            self.constructors.len(),
            field_sorts.len(),
            "field_sorts length must match constructors length",
        );
        self.field_sorts = field_sorts;
        self
    }

    /// v0.19 C.4 — set per-constructor arities (positional).
    /// Must match `constructors.len()` or panics.
    pub fn with_arities(mut self, arities: Vec<u32>) -> Self {
        assert_eq!(
            self.constructors.len(),
            arities.len(),
            "arities length must match constructors length",
        );
        self.arities = arities;
        self
    }

    /// rc.30 (Y4) — set per-constructor selector names (positional).
    /// Must match `constructors.len()`; each inner vec's length is
    /// taken as that constructor's arity.
    pub fn with_selectors(mut self, selectors: Vec<Vec<String>>) -> Self {
        assert_eq!(
            self.constructors.len(),
            selectors.len(),
            "selectors length must match constructors length",
        );
        self.arities = selectors.iter().map(|s| s.len() as u32).collect();
        self.selectors = selectors;
        self
    }

    /// rc.30 (Y4) — set the datatype's type parameters.
    pub fn with_params(mut self, params: Vec<String>) -> Self {
        self.params = params;
        self
    }
}

/// The structural shape of a **Peano-style** datatype
/// `S = base | succ(sel: S)` — exactly one nullary constructor plus one
/// unary constructor that recurses on its OWN sort. Such an `S` is the
/// free term algebra on {base, succ}, isomorphic to ℕ via `base ↦ 0`,
/// `succ(n) ↦ n+1`. Recognized (conservatively) to drive the
/// `IntegerLike(S)` arithmetic bridge.
#[derive(Clone, Debug)]
struct PeanoShape {
    base: String,     // the nullary constructor   (↦ 0)
    succ: String,     // the unary recursive ctor   (↦ +1)
    pred_sel: String, // the unary ctor's selector  (↦ −1)
}

#[derive(Default)]
pub struct Datatypes {
    /// Registered datatype declarations, keyed by sort name.
    decls: HashMap<String, DatatypeDecl>,
    /// rc.30 (Y4) — selector name → (constructor name, arg index),
    /// built from every declared datatype's `selectors`. Drives the
    /// selector-reduction `sel_j(C(x_1..x_n)) = x_j`.
    selector_map: HashMap<String, (String, usize)>,
    /// Asserted equalities between *constructor* terms and other terms.
    asserted_eqs: Vec<(Term, Term)>,
    /// Asserted **disequalities** `a ≠ b` (negative-polarity equality
    /// literals that aren't an immediate constructor-disjointness drop).
    /// Mined by the exhaustiveness check: a recognizer-shaped
    /// `x ≠ c(sel_c(x))` (the desugared `¬is_c(x)`) excludes constructor
    /// `c` for `x`; excluding *every* constructor is unsat. Scoped
    /// alongside `asserted_eqs`.
    disequalities: Vec<(Term, Term)>,
    /// rc.30 (Y4) — every asserted literal term, mined for
    /// selector-application subterms in `derive_equalities`. Scoped
    /// alongside `asserted_eqs`.
    asserted_terms: Vec<Term>,
    conflict: Option<TheoryWitness>,
    /// Push/pop snapshot of `(asserted_eqs, disequalities, asserted_terms)` lengths.
    scope_stack: Vec<(usize, usize, usize)>,
}

impl Datatypes {
    pub fn new() -> Self { Self::default() }

    pub fn declare(&mut self, decl: DatatypeDecl) {
        // rc.30 — index this datatype's selectors for reduction.
        for (ci, ctor) in decl.constructors.iter().enumerate() {
            if let Some(sels) = decl.selectors.get(ci) {
                for (si, sel) in sels.iter().enumerate() {
                    self.selector_map.insert(sel.clone(), (ctor.clone(), si));
                }
            }
        }
        self.decls.insert(decl.sort_name.clone(), decl);
    }

    /// rc.30 (Y4) — atom (Const/Var) name, if `t` is one.
    fn atom_name(t: &Term) -> Option<String> {
        match t.kind() {
            TermInner::Const(c) => Some(c.name.clone()),
            TermInner::Var(v) => Some(v.name.clone()),
            _ => None,
        }
    }

    /// rc.30 (Y4) — walk `t`'s subterms, emitting the selector
    /// reduction `sel_j(C(x_1..x_n)) = x_j` for every selector
    /// application whose argument is a matching constructor app.
    fn collect_selector_reductions(&self, t: &Term, out: &mut Vec<(Term, Term)>) {
        if let TermInner::App(f, x) = t.kind()
            && let Some(sel) = Self::atom_name(f)
            && let Some((ctor, idx)) = self.selector_map.get(&sel)
            && let Some((cname, args)) = Self::dest_constructor_app(x)
            && &cname == ctor
            && *idx < args.len()
        {
            out.push((t.clone(), args[*idx].clone()));
        }
        match t.kind() {
            TermInner::App(f, x) => {
                self.collect_selector_reductions(f, out);
                self.collect_selector_reductions(x, out);
            }
            TermInner::Lam(_, body) => self.collect_selector_reductions(body, out),
            _ => {}
        }
    }

    /// Selector reduction **through congruence** — the companion to the literal
    /// [`Self::collect_selector_reductions`], which only fires on a selector
    /// applied to a *syntactic* constructor app `sel(C(x⃗))`. A `sel(y)` whose
    /// argument `y` is merely *asserted equal* to a constructor (`y = C(x⃗)`)
    /// must reduce too — otherwise `x = succ zero ∧ pred x ≠ zero` is wrongly
    /// `sat` (a spurious-sat completeness gap).
    ///
    /// Close the asserted equalities into classes, find each class's constructor
    /// representative, and for every `sel(y)` subterm whose `y` lands in a class
    /// with a matching constructor `C(args)`, emit `sel(y) = args[idx]`. **Sound**:
    /// `y = C(args) ⟹ sel_{C,idx}(y) = args[idx]` is a valid consequence, so this
    /// only ever adds *true* equalities (it can derive a contradiction, never a
    /// false one).
    fn congruent_selector_reductions(&self, out: &mut Vec<(Term, Term)>) {
        if self.asserted_eqs.is_empty() {
            return;
        }
        // 1. union-find over the asserted equalities.
        let mut parent: HashMap<Term, Term> = HashMap::new();
        for (a, b) in &self.asserted_eqs {
            Self::uf_union(&mut parent, a, b);
        }
        // 2. ALL constructor applications in each class — keyed by the class
        //    representative. A class may hold *several* constructor apps of the
        //    same constructor (e.g. `x ~ succ(pred x) ~ succ zero`): keeping
        //    only one (the prior `or_insert`) was both **order-dependent** (it
        //    picked an arbitrary one per random `HashMap` iteration) and
        //    **incomplete** — reducing `pred x` against `succ(pred x)` yields
        //    the vacuous `pred x = pred x` and misses the load-bearing
        //    `pred x = zero` from `succ zero`, silently dropping a conflict →
        //    spurious `sat`. Collecting every app and emitting against all of
        //    them is deterministic and complete (a redundant reduction is
        //    harmless; the missing one is not). A *distinct* constructor in a
        //    class is a disjointness conflict already caught in `assert`.
        let mut ctors_of: HashMap<Term, Vec<(String, Vec<Term>)>> = HashMap::new();
        for t in parent.keys() {
            if let Some(ctor) = Self::dest_constructor_app(t) {
                let r = Self::uf_find(&parent, t);
                ctors_of.entry(r).or_default().push(ctor);
            }
        }
        if ctors_of.is_empty() {
            return;
        }
        // 3. each `sel(y)` subterm whose `y`'s class carries a matching ctor —
        //    reduced against every such constructor app in the class.
        let mut sel_apps: Vec<(Term, Term)> = Vec::new(); // (sel_app, arg)
        for t in &self.asserted_terms {
            self.collect_selector_apps(t, &mut sel_apps);
        }
        for (sel_app, y) in sel_apps {
            let TermInner::App(f, _) = sel_app.kind() else { continue };
            let Some(name) = Self::atom_name(f) else { continue };
            let Some((ctor, idx)) = self.selector_map.get(&name) else { continue };
            let r = Self::uf_find(&parent, &y);
            if let Some(apps) = ctors_of.get(&r) {
                for (cc, args) in apps {
                    if cc == ctor && *idx < args.len() {
                        out.push((sel_app.clone(), args[*idx].clone()));
                    }
                }
            }
        }
    }

    /// Occurs-check / **acyclicity**. In a well-founded (inductive)
    /// datatype a constructor value is strictly larger than each of its
    /// arguments, so a value can never equal a proper sub-part of itself.
    /// Build the containment graph on congruence CLASSES — `class(C(a₁,
    /// …,aₙ))` has an edge to `class(aᵢ)` for every argument — and report
    /// a conflict on any cycle (a class reachable from itself, including
    /// the self-loop `a ~ succ a`). **Sound** for inductive datatypes
    /// (every adsmt `declare-datatype` is well-founded); it only ever
    /// adds true containment edges, so a cycle is a genuine contradiction.
    /// Catches `a = succ a`, `succ b = succ(succ b)` (the merged class's
    /// `succ(succ b)` argument `succ b` lands back in the class),
    /// `xs = cons(_, xs)`, etc. — the dominant datatype false-sat class.
    fn acyclicity_conflict(&self) -> Option<TheoryWitness> {
        if self.asserted_eqs.is_empty() {
            return None;
        }
        // 1. union-find over asserted equalities (transitivity + any
        //    injectivity-derived equalities the polite loop re-asserted).
        let mut parent: HashMap<Term, Term> = HashMap::new();
        for (a, b) in &self.asserted_eqs {
            Self::uf_union(&mut parent, a, b);
        }
        // 2. every constructor-app subterm in the asserted state.
        let mut ctor_apps: Vec<(Term, Vec<Term>)> = Vec::new();
        for (a, b) in &self.asserted_eqs {
            self.collect_ctor_apps(a, &mut ctor_apps);
            self.collect_ctor_apps(b, &mut ctor_apps);
        }
        for t in &self.asserted_terms {
            self.collect_ctor_apps(t, &mut ctor_apps);
        }
        if ctor_apps.is_empty() {
            return None;
        }
        // 3. containment graph on class representatives.
        let mut adj: HashMap<Term, Vec<Term>> = HashMap::new();
        for (app, args) in &ctor_apps {
            parent.entry(app.clone()).or_insert_with(|| app.clone());
            let ra = Self::uf_find(&parent, app);
            for arg in args {
                parent.entry(arg.clone()).or_insert_with(|| arg.clone());
                let rb = Self::uf_find(&parent, arg);
                adj.entry(ra.clone()).or_default().push(rb);
            }
        }
        // 4. iterative DFS cycle detection (0 = unvisited, 1 = on-stack,
        //    2 = done). A back edge to an on-stack node is a cycle.
        let mut color: HashMap<Term, u8> = HashMap::new();
        let nodes: Vec<Term> = adj.keys().cloned().collect();
        for start in &nodes {
            if color.get(start).copied().unwrap_or(0) != 0 {
                continue;
            }
            let mut stack: Vec<(Term, usize)> = vec![(start.clone(), 0)];
            color.insert(start.clone(), 1);
            while let Some((node, idx)) = stack.last().cloned() {
                let succs = adj.get(&node).cloned().unwrap_or_default();
                if idx < succs.len() {
                    stack.last_mut().expect("non-empty").1 += 1;
                    let next = &succs[idx];
                    match color.get(next).copied().unwrap_or(0) {
                        1 => {
                            // Structured, not prose: a consumer learns
                            // WHICH datatype law was violated and on
                            // which term, mechanically. (Structured is
                            // not the same as re-checkable — the shape
                            // carries the reason, not a replayable
                            // derivation.)
                            return Some(TheoryWitness::Datatypes(DatatypeWitness {
                                kind: DatatypeReason::Acyclicity,
                                constructors: Vec::new(),
                                focused: Some(node.clone()),
                            }));
                        }
                        0 => {
                            color.insert(next.clone(), 1);
                            stack.push((next.clone(), 0));
                        }
                        _ => {}
                    }
                } else {
                    color.insert(node.clone(), 2);
                    stack.pop();
                }
            }
        }
        None
    }

    /// Collect `(ctor_app, args)` for every *registered-constructor*
    /// application subterm of `t` (nested args included). Selector apps
    /// (`pred x`) are `Var`-headed → not matched; only `Const`-headed
    /// registered constructors are.
    fn collect_ctor_apps(&self, t: &Term, out: &mut Vec<(Term, Vec<Term>)>) {
        if let Some((cname, args)) = Self::dest_constructor_app(t)
            && self.is_constructor_of(&cname).is_some()
        {
            out.push((t.clone(), args.clone()));
            for arg in &args {
                self.collect_ctor_apps(arg, out);
            }
            return;
        }
        match t.kind() {
            TermInner::App(f, x) => {
                self.collect_ctor_apps(f, out);
                self.collect_ctor_apps(x, out);
            }
            TermInner::Lam(_, body) => self.collect_ctor_apps(body, out),
            _ => {}
        }
    }

    /// **Exhaustiveness**. Every datatype element is one of its
    /// constructors, so a variable excluded from ALL of them is unsat. A
    /// recognizer-shaped disequality `x ≠ c(sel_{c,0}(x), …)` is exactly
    /// `¬is_c(x)` (the desugared recognizer) and excludes `c` for `x`; a
    /// nullary `x ≠ c` excludes the nullary `c`. Group the excluded
    /// constructors by `x`'s congruence class; if a class covers every
    /// constructor of its datatype sort, report a conflict. **Sound**:
    /// only the EXACT `c(sel_c(x))` / nullary-`c` shapes exclude a
    /// constructor — a generic `x ≠ c(t)` with a different `t` does not,
    /// and is never counted.
    fn exhaustiveness_conflict(&self) -> Option<TheoryWitness> {
        if self.disequalities.is_empty() {
            return None;
        }
        let mut parent: HashMap<Term, Term> = HashMap::new();
        for (a, b) in &self.asserted_eqs {
            Self::uf_union(&mut parent, a, b);
        }
        type ExSet = std::collections::HashSet<String>;
        let mut excluded: HashMap<Term, (String, ExSet)> = HashMap::new();
        for (a, b) in &self.disequalities {
            for (x, rhs) in [(a, b), (b, a)] {
                let Some(ctor) = self.recognizer_excluded_ctor(x, rhs) else { continue };
                let sort = x.type_of().to_string();
                let Some(decl) = self.decls.get(&sort) else { continue };
                parent.entry(x.clone()).or_insert_with(|| x.clone());
                let rep = Self::uf_find(&parent, x);
                let entry = excluded.entry(rep).or_insert_with(|| (sort.clone(), ExSet::new()));
                entry.1.insert(ctor);
                if decl.constructors.iter().all(|c| entry.1.contains(c)) {
                    return Some(TheoryWitness::Datatypes(DatatypeWitness {
                        kind: DatatypeReason::CaseSplit,
                        constructors: decl.constructors.clone(),
                        focused: Some(x.clone()),
                    }));
                }
            }
        }
        None
    }

    /// **Single-survivor witness materialization** (the sound case-split
    /// completion). When a class is excluded (via exact recognizer-shaped
    /// disequalities `x ≠ c(sel_c(x))` / `x ≠ c` — see
    /// [`Self::recognizer_excluded_ctor`]) from EVERY constructor of its
    /// sort BUT ONE survivor `c'`, exhaustiveness forces `x = c'(…)`:
    /// emit the witness equality `x = c'(sel_{c'}(x))`. **Sound** — on an
    /// exhaustive datatype a value is some constructor; all-but-one
    /// excluded ⟹ it is the last (this is the standard datatype
    /// case-split made *definite*, not a guess). The downstream
    /// injectivity / selector-reduction / **acyclicity** then discharge
    /// what the disequality alone couldn't: e.g. `b ≠ zero ∧ pred b = b`
    /// ⟹ (survivor succ) `b = succ(pred b)`, and with `pred b = b` this
    /// is `b = succ(b)` → acyclicity unsat. NO arithmetic, NO ℕ-bridge.
    ///
    /// The witness term is built ONLY when an existing `sel_{c'}(t)` (for
    /// some `t` in the class) is present, so the constructor's type is
    /// recovered from that selector application (`field → sort`) — no
    /// per-field sort metadata is needed. Absent the selector term the
    /// witness is skipped (a sound completeness restriction).
    fn single_survivor_witness(&self, out: &mut Vec<(Term, Term)>) {
        if self.disequalities.is_empty() {
            return;
        }
        let mut parent: HashMap<Term, Term> = HashMap::new();
        for (a, b) in &self.asserted_eqs {
            Self::uf_union(&mut parent, a, b);
        }
        type ExSet = std::collections::HashSet<String>;
        let mut excluded: HashMap<Term, (String, ExSet)> = HashMap::new();
        for (a, b) in &self.disequalities {
            for (x, rhs) in [(a, b), (b, a)] {
                let Some(ctor) = self.recognizer_excluded_ctor(x, rhs) else { continue };
                let sort = x.type_of().to_string();
                if !self.decls.contains_key(&sort) {
                    continue;
                }
                parent.entry(x.clone()).or_insert_with(|| x.clone());
                let rep = Self::uf_find(&parent, x);
                excluded
                    .entry(rep)
                    .or_insert_with(|| (sort.clone(), ExSet::new()))
                    .1
                    .insert(ctor);
            }
        }
        if excluded.is_empty() {
            return;
        }
        // selector apps available to recover the survivor's witness term.
        let mut sel_apps: Vec<(Term, Term)> = Vec::new();
        for t in &self.asserted_terms {
            self.collect_selector_apps(t, &mut sel_apps);
        }
        for (a, b) in &self.asserted_eqs {
            self.collect_selector_apps(a, &mut sel_apps);
            self.collect_selector_apps(b, &mut sel_apps);
        }
        for (rep, (sort, exset)) in &excluded {
            let Some(decl) = self.decls.get(sort) else { continue };
            let survivors: Vec<usize> = (0..decl.constructors.len())
                .filter(|&i| !exset.contains(&decl.constructors[i]))
                .collect();
            if survivors.len() != 1 {
                continue;
            }
            let ci = survivors[0];
            // unary survivor with exactly one selector.
            if decl.selectors.get(ci).map(Vec::len) != Some(1) {
                continue;
            }
            let cname = decl.constructors[ci].clone();
            let sel = &decl.selectors[ci][0];
            for (sel_app, arg) in &sel_apps {
                let TermInner::App(f, _) = sel_app.kind() else { continue };
                if Self::atom_name(f).as_deref() != Some(sel.as_str()) {
                    continue;
                }
                parent.entry(arg.clone()).or_insert_with(|| arg.clone());
                if &Self::uf_find(&parent, arg) != rep {
                    continue;
                }
                let Ok(ctor_ty) = Type::fun(sel_app.type_of(), arg.type_of()) else { continue };
                let Ok(witness) = Term::app(Term::const_(&cname, ctor_ty), sel_app.clone())
                else {
                    continue;
                };
                out.push((arg.clone(), witness));
                break;
            }
        }
    }

    /// CONSERVATIVE Peano-shape recognizer. Returns `Some` iff `decl` is
    /// `S = base | succ(sel: S)`: monomorphic, exactly two constructors
    /// (one nullary + one unary), and — the load-bearing guard — the
    /// unary constructor recurses on its OWN sort (`field_sort == S`).
    /// **Fails closed** when `field_sorts` is absent, so a producer that
    /// didn't thread field sorts disables the bridge (sound no-op) rather
    /// than risk a structural-only over-fire on `wrap(Int)` (foreign
    /// field) or a mutually-recursive group (field sort ≠ `S`).
    fn peano_shape(decl: &DatatypeDecl) -> Option<PeanoShape> {
        if !decl.params.is_empty() || decl.constructors.len() != 2 {
            return None;
        }
        let (base_i, succ_i) = match (decl.arities[0], decl.arities[1]) {
            (0, 1) => (0usize, 1usize),
            (1, 0) => (1, 0),
            _ => return None,
        };
        let fields = decl.field_sorts.get(succ_i)?;
        if fields.len() != 1 || fields[0] != decl.sort_name {
            return None;
        }
        let sel = decl.selectors.get(succ_i)?.first()?.clone();
        Some(PeanoShape {
            base: decl.constructors[base_i].clone(),
            succ: decl.constructors[succ_i].clone(),
            pred_sel: sel,
        })
    }

    /// The selector/function head name of an application `(f x)`.
    fn selector_head_name(app: &Term) -> Option<String> {
        let TermInner::App(f, _) = app.kind() else { return None };
        Self::atom_name(f)
    }

    /// **`IntegerLike(Peano)` arithmetic bridge.** For every Peano-shaped
    /// sort `S` (free algebra ≅ ℕ), introduce an integer IMAGE variable
    /// `img(t)` per `S`-term and emit the sound image equalities so the
    /// LIA solver can reason about Peano structure arithmetically:
    /// - `img(base) = 0`, `img(succ s) = img(s) + 1` — the isomorphism
    ///   `φ(base)=0`, `φ(succ n)=φ(n)+1`.
    /// - congruence: `t₁ = t₂` (asserted `S`-equality) ⟹ `img t₁ = img t₂`
    ///   (`φ` is a function).
    /// - GATED predecessor: `img(pred s) = img(s) − 1` ONLY when `s` is
    ///   forced succ-shaped (its class is excluded from `base` via a
    ///   recognizer disequality `s ≠ base`) — then `s = succ(p)`,
    ///   `pred s = p`, `φ(p) = φ(s)−1`. For an `s` that could be `base`,
    ///   nothing is emitted (`pred(base)` is under-specified, so its image
    ///   stays a free integer — never forced to `−1`).
    ///
    /// **Sound**: every emitted equality is a true consequence of the
    /// ℕ-isomorphism; the only conditional rule (predecessor) is gated on
    /// the datatype's own exhaustiveness so `pred(base)` never leaks a
    /// `−1`. The image vars are fresh (`!peano_img!…`, Int-sorted), so the
    /// facts can never poison user arithmetic. This closes e.g.
    /// `b ≠ zero ∧ pred b = b` as `img(pred b) = img(b) ∧ img(pred b) =
    /// img(b) − 1` ⟹ LIA conflict — and, once a surface puts arithmetic
    /// ON a Peano value, lets LIA decide Peano-depth obligations the
    /// datatype theory alone cannot reach.
    fn peano_arith_bridge(&self, out: &mut Vec<(Term, Term)>) {
        let peanos: Vec<(String, PeanoShape)> = self
            .decls
            .iter()
            .filter_map(|(s, d)| Self::peano_shape(d).map(|p| (s.clone(), p)))
            .collect();
        if peanos.is_empty() {
            return;
        }
        let peano_of = |sort: &str| peanos.iter().find(|(s, _)| s == sort).map(|(_, p)| p.clone());
        let int_ty = Type::const_("Int", adsmt_core::Kind::Type);
        let img = |t: &Term| Term::var(&format!("!peano_img!{t}"), int_ty.clone());
        let lit = |k: i128| Term::const_(&format!("int:{k}"), int_ty.clone());
        let int_bin = |op: &str, a: Term, b: Term| -> Option<Term> {
            let ty = Type::fun(int_ty.clone(), Type::fun(int_ty.clone(), int_ty.clone()).ok()?).ok()?;
            Term::app(Term::app(Term::const_(op, ty), a).ok()?, b).ok()
        };

        // (1) congruence over Peano sorts: equal terms ⟹ equal images.
        for (a, b) in &self.asserted_eqs {
            if peano_of(&a.type_of().to_string()).is_some() {
                out.push((img(a), img(b)));
            }
        }

        // collect every constructor / selector application subterm.
        let mut ctor_apps: Vec<(Term, Vec<Term>)> = Vec::new();
        let mut sel_apps: Vec<(Term, Term)> = Vec::new();
        for t in &self.asserted_terms {
            self.collect_ctor_apps(t, &mut ctor_apps);
            self.collect_selector_apps(t, &mut sel_apps);
        }
        for (a, b) in &self.asserted_eqs {
            self.collect_ctor_apps(a, &mut ctor_apps);
            self.collect_ctor_apps(b, &mut ctor_apps);
            self.collect_selector_apps(a, &mut sel_apps);
            self.collect_selector_apps(b, &mut sel_apps);
        }

        // (2) img(succ s) = img(s)+1 ; img(base) = 0.
        for (app, args) in &ctor_apps {
            let Some((cname, _)) = Self::dest_constructor_app(app) else { continue };
            let Some(p) = peano_of(&app.type_of().to_string()) else { continue };
            if cname == p.succ && args.len() == 1 {
                if let Some(rhs) = int_bin("+", img(&args[0]), lit(1)) {
                    out.push((img(app), rhs));
                }
            } else if cname == p.base && args.is_empty() {
                out.push((img(app), lit(0)));
            }
        }

        // (3) succ-shaped classes = those excluded from the base ctor.
        let mut parent: HashMap<Term, Term> = HashMap::new();
        for (a, b) in &self.asserted_eqs {
            Self::uf_union(&mut parent, a, b);
        }
        let mut succ_shaped: std::collections::HashSet<Term> = std::collections::HashSet::new();
        for (a, b) in &self.disequalities {
            for (x, rhs) in [(a, b), (b, a)] {
                let Some(p) = peano_of(&x.type_of().to_string()) else { continue };
                if self.recognizer_excluded_ctor(x, rhs).as_deref() == Some(p.base.as_str()) {
                    parent.entry(x.clone()).or_insert_with(|| x.clone());
                    succ_shaped.insert(Self::uf_find(&parent, x));
                }
            }
        }

        // (4) gated predecessor: img(pred s) = img(s)−1 for succ-shaped s.
        for (sel_app, arg) in &sel_apps {
            let Some(p) = peano_of(&arg.type_of().to_string()) else { continue };
            if Self::selector_head_name(sel_app).as_deref() != Some(p.pred_sel.as_str()) {
                continue;
            }
            parent.entry(arg.clone()).or_insert_with(|| arg.clone());
            if succ_shaped.contains(&Self::uf_find(&parent, arg))
                && let Some(rhs) = int_bin("-", img(arg), lit(1))
            {
                out.push((img(sel_app), rhs));
            }
        }
    }

    /// If `rhs` is the recognizer shape for a constructor `c` applied to
    /// `x` — a nullary constructor `c` (so `x ≠ c` ≡ `¬is_c(x)`), or
    /// `c(sel_{c,0}(x), …, sel_{c,k-1}(x))` — return `c`'s name, else
    /// `None`. The arguments must be EXACTLY `c`'s selectors applied to
    /// the same `x` (anything else is not a tester and excludes nothing).
    fn recognizer_excluded_ctor(&self, x: &Term, rhs: &Term) -> Option<String> {
        let (cname, args) = Self::dest_constructor_app(rhs)?;
        let decl = self.is_constructor_of(&cname)?;
        let ci = decl.constructors.iter().position(|c| c == &cname)?;
        let sels = decl.selectors.get(ci)?;
        if args.len() != sels.len() {
            return None;
        }
        for (arg, sel) in args.iter().zip(sels) {
            let TermInner::App(f, a) = arg.kind() else { return None };
            let Some(fname) = Self::atom_name(f) else { return None };
            if &fname != sel || a != x {
                return None;
            }
        }
        Some(cname)
    }

    /// Collect `(sel_app, arg)` for every selector-application subterm of `t`.
    fn collect_selector_apps(&self, t: &Term, out: &mut Vec<(Term, Term)>) {
        if let TermInner::App(f, x) = t.kind()
            && let Some(name) = Self::atom_name(f)
            && self.selector_map.contains_key(&name)
        {
            out.push((t.clone(), x.clone()));
        }
        match t.kind() {
            TermInner::App(f, x) => {
                self.collect_selector_apps(f, out);
                self.collect_selector_apps(x, out);
            }
            TermInner::Lam(_, body) => self.collect_selector_apps(body, out),
            _ => {}
        }
    }

    /// Union-find representative of `t` (no path compression — the asserted-
    /// equality chains are short and this stays read-only for `&self` callers).
    fn uf_find(parent: &HashMap<Term, Term>, t: &Term) -> Term {
        let mut root = t.clone();
        while let Some(p) = parent.get(&root) {
            if p == &root {
                break;
            }
            root = p.clone();
        }
        root
    }

    /// Union-find: merge the classes of `a` and `b`.
    fn uf_union(parent: &mut HashMap<Term, Term>, a: &Term, b: &Term) {
        parent.entry(a.clone()).or_insert_with(|| a.clone());
        parent.entry(b.clone()).or_insert_with(|| b.clone());
        let ra = Self::uf_find(parent, a);
        let rb = Self::uf_find(parent, b);
        if ra != rb {
            parent.insert(ra, rb);
        }
    }

    pub fn is_constructor_of(&self, ctor_name: &str) -> Option<&DatatypeDecl> {
        self.decls
            .values()
            .find(|d| d.constructors.iter().any(|c| c == ctor_name))
    }

    /// v0.19 C.4 — decompose a term of the shape
    /// `App(App(...App(Const(ctor), arg1)...), argN)` into
    /// `(ctor_name, [arg1, ..., argN])` when the head constant
    /// is a registered constructor.
    ///
    /// Static method — doesn't need `&self` because callers
    /// already know which sort they're processing; the
    /// constructor-name string is sufficient for downstream
    /// injectivity reasoning.
    pub(crate) fn dest_constructor_app(t: &Term) -> Option<(String, Vec<Term>)> {
        let mut args: Vec<Term> = Vec::new();
        let mut cur = t.clone();
        loop {
            let next = match cur.kind() {
                TermInner::App(f, x) => {
                    args.push(x.clone());
                    f.clone()
                }
                TermInner::Const(c) => {
                    args.reverse();
                    return Some((c.name.clone(), args));
                }
                _ => return None,
            };
            cur = next;
        }
    }

    /// Recognize whether `t` is a registered constructor — either a
    /// bare nullary constant (`None`) or an application
    /// (`(Some_int_ 5)`). Returns `(sort_name, constructor_name)`.
    /// rc.30 (Y4): extended to applied constructors so disjointness
    /// fires for argument-bearing constructors, not only enums.
    fn constructor_id(&self, t: &Term) -> Option<(String, String)> {
        let (cname, _args) = Self::dest_constructor_app(t)?;
        let d = self.is_constructor_of(&cname)?;
        Some((d.sort_name.clone(), cname))
    }
}

impl Theory for Datatypes {
    fn name(&self) -> &'static str { "Datatypes" }

    /// Handle any sort that has a registered datatype declaration.
    /// rc.30 (Y4) — also matches an *applied* parametric datatype
    /// (`(Seq Int)`) by its head constructor name (`Seq`).
    fn handles_sort(&self, ty: &Type) -> bool {
        if self.decls.contains_key(&ty.to_string()) {
            return true;
        }
        // Walk the leftmost head of a nested type application.
        let mut cur = ty.clone();
        loop {
            match &cur {
                Type::Const(c) => return self.decls.contains_key(&c.name),
                Type::App(f, _) => cur = (**f).clone(),
                Type::Var(_) => return false,
            }
        }
    }

    fn assert(&mut self, lit: Literal) -> AssertResult {
        // rc.30 — record the literal term for selector-reduction
        // subterm mining in `derive_equalities`.
        self.asserted_terms.push(lit.term.clone());
        if let Some((a, b)) = lit.term.dest_eq() {
            // Constructor disjointness: a, b are *distinct* concrete
            // constructors of the same datatype, so asserting `a = b`
            // is an immediate conflict; asserting `a ≠ b` is trivially
            // satisfied.
            let ctor_a = self.constructor_id(&a);
            let ctor_b = self.constructor_id(&b);
            if let (Some((s1, n1)), Some((s2, n2))) = (ctor_a, ctor_b)
                && s1 == s2 && n1 != n2 {
                    if lit.polarity {
                        let w = TheoryWitness::Datatypes(DatatypeWitness {
                            kind: DatatypeReason::Disjointness,
                            constructors: vec![n1.clone(), n2.clone()],
                            focused: Some(lit.term.clone()),
                        });
                        self.conflict = Some(w.clone());
                        return AssertResult::Conflict { witness: w };
                    }
                    // Otherwise: known-true disequality. Drop.
                    return AssertResult::Accepted;
                }
            // SOUNDNESS — only a *positive* equality may seed injectivity /
            // selector reduction. A **disequality** (`succ b ≠ succ c`, same
            // constructor so not a disjointness conflict) was previously pushed
            // here UNCONDITIONALLY → injectivity wrongly derived `b = c` →
            // congruence `succ b = succ c` contradicted the disequality →
            // spurious UNSAT (z3-differential: 57/400 false-unsat). Gate on
            // polarity; a disequality is UF's to reason about, not ours.
            if lit.polarity {
                self.asserted_eqs.push((a, b));
            } else {
                self.disequalities.push((a, b));
            }
            AssertResult::Accepted
        } else {
            AssertResult::Ignored
        }
    }

    fn check(&mut self) -> CheckResult {
        if let Some(w) = &self.conflict {
            return CheckResult::Unsat { witness: w.clone() };
        }
        // Occurs-check: a constructor value can't contain itself.
        if let Some(w) = self.acyclicity_conflict() {
            self.conflict = Some(w.clone());
            return CheckResult::Unsat { witness: w };
        }
        // Exhaustiveness: a value excluded from every constructor is unsat.
        if let Some(w) = self.exhaustiveness_conflict() {
            self.conflict = Some(w.clone());
            return CheckResult::Unsat { witness: w };
        }
        CheckResult::Sat
    }

    fn derive_equalities(&self) -> Vec<(Term, Term)> {
        // v0.19 C.4 — constructor injectivity.
        //
        // When `C(a1, ..., an) = C(b1, ..., bn)` is asserted
        // (positive polarity), the equalities `a_i = b_i` hold
        // pointwise. We mine `asserted_eqs` for any equality
        // whose both sides are applications of the *same*
        // constructor and emit the per-argument equalities.
        //
        // Pure derived equalities — caller routes them through
        // the polite combination as new assertions.
        let mut out = Vec::new();
        for (a, b) in &self.asserted_eqs {
            let head_a = Self::dest_constructor_app(a);
            let head_b = Self::dest_constructor_app(b);
            if let (Some((ca, args_a)), Some((cb, args_b))) = (head_a, head_b)
                && ca == cb && args_a.len() == args_b.len() {
                for (arg_a, arg_b) in args_a.into_iter().zip(args_b) {
                    out.push((arg_a, arg_b));
                }
            }
        }
        // rc.30 (Y4) — selector reduction `sel_j(C(x_1..x_n)) = x_j`
        // mined from every asserted literal's subterms.
        for t in &self.asserted_terms {
            self.collect_selector_reductions(t, &mut out);
        }
        // and the same reduction *through congruence* — `sel(y)` with `y` only
        // asserted-equal to a constructor (closes the spurious-sat gap).
        self.congruent_selector_reductions(&mut out);
        // Exhaustiveness made definite: an all-but-one-excluded class is
        // forced to its surviving constructor (closes `b≠zero ∧ pred b=b`
        // via the downstream acyclicity, no arithmetic bridge).
        self.single_survivor_witness(&mut out);
        // IntegerLike(Peano) bridge: emit integer image equalities for
        // Peano-shaped sorts so LIA can reason about Peano arithmetic.
        self.peano_arith_bridge(&mut out);
        out
    }

    fn explain(&self) -> Option<TheoryWitness> { self.conflict.clone() }

    fn cardinality_witness(&self, sort: &Type) -> PoliteWitness {
        let key = sort.to_string();
        match self.decls.get(&key) {
            Some(d) if d.is_finite => PoliteWitness {
                sort: key,
                upper_bound: Some(d.constructors.len() as u64),
            },
            _ => PoliteWitness { sort: key, upper_bound: None },
        }
    }

    fn push(&mut self) {
        self.scope_stack.push((
            self.asserted_eqs.len(),
            self.disequalities.len(),
            self.asserted_terms.len(),
        ));
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if let Some((neq, ndiseq, nterms)) = self.scope_stack.pop() {
                self.asserted_eqs.truncate(neq);
                self.disequalities.truncate(ndiseq);
                self.asserted_terms.truncate(nterms);
            }
        }
        self.conflict = None;
    }

    fn reset(&mut self) {
        self.asserted_eqs.clear();
        self.disequalities.clear();
        self.asserted_terms.clear();
        self.conflict = None;
        self.scope_stack.clear();
        // `decls` is structural data, kept across reset to mirror
        // SMT-LIB convention (declare-datatypes persists).
    }

    fn as_any_mut(&mut self) -> Option<&mut dyn std::any::Any> { Some(self) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Term, Type};

    fn color_sort() -> Type { Type::const_("Color", Kind::Type) }
    fn red() -> Term { Term::const_("Red", color_sort()) }
    fn green() -> Term { Term::const_("Green", color_sort()) }
    #[allow(unused)]
    fn blue() -> Term { Term::const_("Blue", color_sort()) }

    fn registered() -> Datatypes {
        let mut dt = Datatypes::new();
        dt.declare(DatatypeDecl::finite_enum(
            "Color",
            vec!["Red".into(), "Green".into(), "Blue".into()],
        ));
        dt
    }

    #[test]
    fn finite_witness_reports_constructor_count() {
        let dt = registered();
        let w = dt.cardinality_witness(&color_sort());
        assert_eq!(w.upper_bound, Some(3));
    }

    #[test]
    fn distinct_constructors_assert_equal_is_unsat() {
        let mut dt = registered();
        let eq = Term::mk_eq(red(), green()).unwrap();
        match dt.assert(Literal::positive(eq).unwrap()) {
            AssertResult::Conflict { .. } => {}
            other => panic!("expected Conflict, got {other:?}"),
        }
        assert!(matches!(dt.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn distinct_constructors_assert_disequal_is_accepted() {
        let mut dt = registered();
        let eq = Term::mk_eq(red(), green()).unwrap();
        let r = dt.assert(Literal::negative(eq).unwrap());
        assert!(matches!(r, AssertResult::Accepted));
        assert!(matches!(dt.check(), CheckResult::Sat));
    }

    #[test]
    fn same_constructor_equality_is_trivial() {
        let mut dt = registered();
        let eq = Term::mk_eq(red(), red()).unwrap();
        assert!(matches!(dt.assert(Literal::positive(eq).unwrap()), AssertResult::Accepted));
        assert!(matches!(dt.check(), CheckResult::Sat));
    }

    #[test]
    fn inductive_datatype_returns_omega() {
        let mut dt = Datatypes::new();
        let nat_sort = Type::const_("Nat", Kind::Type);
        dt.declare(DatatypeDecl::inductive(
            "Nat", vec!["Zero".into(), "Succ".into()],
        ));
        let w = dt.cardinality_witness(&nat_sort);
        assert!(w.upper_bound.is_none());
    }

    #[test]
    fn unregistered_sort_returns_omega() {
        let dt = registered();
        let other = Type::const_("Bool", Kind::Type);
        assert!(dt.cardinality_witness(&other).upper_bound.is_none());
    }

    #[test]
    fn push_pop_undoes_disequality_record() {
        let mut dt = registered();
        let eq = Term::mk_eq(red(), green()).unwrap();
        dt.push();
        // Disequalities between distinct ctors are auto-accepted but
        // we still want push/pop semantics to be coherent.
        let _ = dt.assert(Literal::negative(eq).unwrap());
        dt.pop(1);
        assert!(matches!(dt.check(), CheckResult::Sat));
    }

    // === v0.19 C.4 — recursive datatypes (injectivity) ===

    #[test]
    fn dest_constructor_app_extracts_arity_one() {
        // `Succ x` decomposed into ("Succ", [x]).
        let nat_ty = Type::const_("Nat", Kind::Type);
        let succ = Term::const_(
            "Succ",
            Type::fun(nat_ty.clone(), nat_ty.clone()).unwrap(),
        );
        let x = Term::var("x", nat_ty);
        let term = Term::app(succ, x.clone()).unwrap();
        let (name, args) = Datatypes::dest_constructor_app(&term)
            .expect("decomposition succeeds");
        assert_eq!(name, "Succ");
        assert_eq!(args.len(), 1);
        assert!(args[0].alpha_eq(&x));
    }

    #[test]
    fn dest_constructor_app_extracts_arity_two() {
        // `Cons h t` decomposed into ("Cons", [h, t]).
        let int_ty = Type::const_("Int", Kind::Type);
        let list_ty = Type::const_("List_Int", Kind::Type);
        let cons_ty = Type::fun(
            int_ty.clone(),
            Type::fun(list_ty.clone(), list_ty.clone()).unwrap(),
        )
        .unwrap();
        let cons = Term::const_("Cons", cons_ty);
        let h = Term::var("h", int_ty);
        let t = Term::var("t", list_ty);
        let term =
            Term::app(Term::app(cons, h.clone()).unwrap(), t.clone()).unwrap();
        let (name, args) = Datatypes::dest_constructor_app(&term)
            .expect("decomposition succeeds");
        assert_eq!(name, "Cons");
        assert_eq!(args.len(), 2);
        assert!(args[0].alpha_eq(&h));
        assert!(args[1].alpha_eq(&t));
    }

    #[test]
    fn injectivity_derives_argument_equalities() {
        // Assert `Cons h1 t1 = Cons h2 t2` and check
        // derive_equalities yields h1 = h2, t1 = t2.
        let int_ty = Type::const_("Int", Kind::Type);
        let list_ty = Type::const_("List_Int", Kind::Type);
        let cons_ty = Type::fun(
            int_ty.clone(),
            Type::fun(list_ty.clone(), list_ty.clone()).unwrap(),
        )
        .unwrap();
        let cons = Term::const_("Cons", cons_ty);
        let h1 = Term::var("h1", int_ty.clone());
        let h2 = Term::var("h2", int_ty);
        let t1 = Term::var("t1", list_ty.clone());
        let t2 = Term::var("t2", list_ty);
        let lhs = Term::app(
            Term::app(cons.clone(), h1.clone()).unwrap(),
            t1.clone(),
        )
        .unwrap();
        let rhs = Term::app(
            Term::app(cons, h2.clone()).unwrap(),
            t2.clone(),
        )
        .unwrap();

        let mut dt = Datatypes::new();
        dt.declare(
            DatatypeDecl::inductive(
                "List_Int",
                vec!["Cons".into(), "Nil".into()],
            )
            .with_arities(vec![2, 0]),
        );
        let eq = Term::mk_eq(lhs, rhs).unwrap();
        let _ = dt.assert(Literal::positive(eq).unwrap());

        let derived = dt.derive_equalities();
        assert_eq!(derived.len(), 2, "expected pointwise injectivity");
        assert!(derived.iter().any(|(a, b)| a.alpha_eq(&h1) && b.alpha_eq(&h2)));
        assert!(derived.iter().any(|(a, b)| a.alpha_eq(&t1) && b.alpha_eq(&t2)));
    }

    #[test]
    fn disequality_is_not_treated_as_equality() {
        // SOUNDNESS — a same-constructor **disequality** `Cons h1 t1 ≠ Cons h2 t2`
        // is satisfiable (h1≠h2 or t1≠t2) and must NOT seed injectivity. Pushing
        // it to `asserted_eqs` (ignoring polarity) wrongly derived `h1 = h2` →
        // congruence → contradiction → spurious UNSAT (z3-differential: 57/400).
        let int_ty = Type::const_("Int", Kind::Type);
        let list_ty = Type::const_("List_Int", Kind::Type);
        let cons_ty =
            Type::fun(int_ty.clone(), Type::fun(list_ty.clone(), list_ty.clone()).unwrap()).unwrap();
        let cons = Term::const_("Cons", cons_ty);
        let mk = |h: &str, t: &str| {
            Term::app(
                Term::app(cons.clone(), Term::var(h, int_ty.clone())).unwrap(),
                Term::var(t, list_ty.clone()),
            )
            .unwrap()
        };
        let mut dt = Datatypes::new();
        dt.declare(
            DatatypeDecl::inductive("List_Int", vec!["Cons".into(), "Nil".into()])
                .with_arities(vec![2, 0]),
        );
        let eq = Term::mk_eq(mk("h1", "t1"), mk("h2", "t2")).unwrap();
        let r = dt.assert(Literal::negative(eq).unwrap());
        assert!(matches!(r, AssertResult::Accepted), "a same-ctor disequality is sat, not a conflict");
        assert!(dt.derive_equalities().is_empty(), "a DISEQUALITY must derive no injective equalities");
    }

    #[test]
    fn selector_reduces_through_congruence() {
        // `x = succ z` ⟹ `pred x = z` — selector reduction must chase the
        // asserted equality, not only a *literal* `pred(succ z)`. Else
        // `x = succ z ∧ pred x ≠ z` is wrongly `sat` (z3: unsat).
        let nat = Type::const_("Nat", Kind::Type);
        let x = Term::var("x", nat.clone());
        let z = Term::var("z", nat.clone());
        let succ_z =
            Term::app(Term::const_("succ", Type::fun(nat.clone(), nat.clone()).unwrap()), z.clone())
                .unwrap();
        let pred_x =
            Term::app(Term::const_("pred", Type::fun(nat.clone(), nat.clone()).unwrap()), x.clone())
                .unwrap();
        let mut dt = Datatypes::new();
        dt.declare(
            DatatypeDecl::inductive("Nat", vec!["zero".into(), "succ".into()])
                .with_selectors(vec![vec![], vec!["pred".into()]]),
        );
        let _ = dt.assert(Literal::positive(Term::mk_eq(x.clone(), succ_z).unwrap()).unwrap());
        // mention `pred x` (a known subterm) without seeding an equality.
        let _ = dt.assert(Literal::negative(Term::mk_eq(pred_x.clone(), z.clone()).unwrap()).unwrap());
        let derived = dt.derive_equalities();
        assert!(
            derived.iter().any(|(a, b)| a.alpha_eq(&pred_x) && b.alpha_eq(&z)),
            "expected the congruence selector reduction pred(x) = z; got {derived:?}"
        );
    }

    #[test]
    fn selector_reduces_against_all_ctor_apps_in_a_class() {
        // A class holding *two* constructor apps — `x ~ succ(p) ~ succ zero`
        // (from `x = succ p` and `x = succ zero`). The congruence selector
        // reduction must emit `pred x = zero` (against `succ zero`), not only
        // the vacuous `pred x = p` (against `succ p`). Keeping a single
        // arbitrary representative was order-dependent (random `HashMap`
        // iteration) and could drop the load-bearing reduction → a
        // nondeterministic spurious `sat`.
        let nat = Type::const_("Nat", Kind::Type);
        let succ = Type::fun(nat.clone(), nat.clone()).unwrap();
        let x = Term::var("x", nat.clone());
        let p = Term::var("p", nat.clone());
        let zero = Term::const_("zero", nat.clone());
        let succ_p = Term::app(Term::const_("succ", succ.clone()), p.clone()).unwrap();
        let succ_zero = Term::app(Term::const_("succ", succ.clone()), zero.clone()).unwrap();
        let pred_x = Term::app(
            Term::const_("pred", Type::fun(nat.clone(), nat.clone()).unwrap()),
            x.clone(),
        )
        .unwrap();
        let mut dt = Datatypes::new();
        dt.declare(
            DatatypeDecl::inductive("Nat", vec!["zero".into(), "succ".into()])
                .with_selectors(vec![vec![], vec!["pred".into()]]),
        );
        let _ = dt.assert(Literal::positive(Term::mk_eq(x.clone(), succ_p).unwrap()).unwrap());
        let _ = dt.assert(Literal::positive(Term::mk_eq(x.clone(), succ_zero).unwrap()).unwrap());
        let _ = dt.assert(Literal::negative(Term::mk_eq(pred_x.clone(), zero.clone()).unwrap()).unwrap());
        let derived = dt.derive_equalities();
        assert!(
            derived.iter().any(|(a, b)| a.alpha_eq(&pred_x) && b.alpha_eq(&zero)),
            "expected pred(x) = zero against the succ(zero) app; got {derived:?}"
        );
    }

    fn nat_dt() -> Datatypes {
        let mut dt = Datatypes::new();
        dt.declare(
            DatatypeDecl::inductive("Nat", vec!["zero".into(), "succ".into()])
                .with_selectors(vec![vec![], vec!["pred".into()]]),
        );
        dt
    }
    fn nat_ty() -> Type { Type::const_("Nat", Kind::Type) }
    fn succ_of(t: Term) -> Term {
        Term::app(Term::const_("succ", Type::fun(nat_ty(), nat_ty()).unwrap()), t).unwrap()
    }
    fn pred_of(t: Term) -> Term {
        Term::app(Term::var("pred", Type::fun(nat_ty(), nat_ty()).unwrap()), t).unwrap()
    }

    #[test]
    fn acyclicity_direct_self_successor_is_unsat() {
        // `a = succ a` — a value cannot contain itself.
        let mut dt = nat_dt();
        let a = Term::var("a", nat_ty());
        dt.assert(Literal::positive(Term::mk_eq(a.clone(), succ_of(a.clone())).unwrap()).unwrap());
        assert!(matches!(dt.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn acyclicity_through_injectivity_is_unsat() {
        // `succ b = succ(succ b)` — the merged class's `succ(succ b)` argument
        // `succ b` lands back in the class → self-loop.
        let mut dt = nat_dt();
        let b = Term::var("b", nat_ty());
        let sb = succ_of(b.clone());
        let ssb = succ_of(sb.clone());
        dt.assert(Literal::positive(Term::mk_eq(sb, ssb).unwrap()).unwrap());
        assert!(matches!(dt.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn acyclicity_does_not_overfire_on_selector_reconstruction() {
        // `a = succ(pred a)` is the is-succ identity — SAT, not a cycle
        // (`pred a` is a selector app, not `a`).
        let mut dt = nat_dt();
        let a = Term::var("a", nat_ty());
        dt.assert(
            Literal::positive(Term::mk_eq(a.clone(), succ_of(pred_of(a.clone()))).unwrap())
                .unwrap(),
        );
        assert!(matches!(dt.check(), CheckResult::Sat));
    }

    #[test]
    fn exhaustiveness_excluding_all_constructors_is_unsat() {
        // `¬is_zero(a) ∧ ¬is_succ(a)` (desugared `a ≠ zero ∧ a ≠ succ(pred a)`)
        // — a Nat must be one of its constructors.
        let mut dt = nat_dt();
        let a = Term::var("a", nat_ty());
        let zero = Term::const_("zero", nat_ty());
        dt.assert(Literal::negative(Term::mk_eq(a.clone(), zero).unwrap()).unwrap());
        dt.assert(
            Literal::negative(Term::mk_eq(a.clone(), succ_of(pred_of(a.clone()))).unwrap())
                .unwrap(),
        );
        assert!(matches!(dt.check(), CheckResult::Unsat { .. }));
    }

    fn nat_dt_peano() -> Datatypes {
        let mut dt = Datatypes::new();
        dt.declare(
            DatatypeDecl::inductive("Nat", vec!["zero".into(), "succ".into()])
                .with_selectors(vec![vec![], vec!["pred".into()]])
                .with_field_sorts(vec![vec![], vec!["Nat".into()]]),
        );
        dt
    }
    fn img_of(t: &Term) -> Term {
        Term::var(&format!("!peano_img!{t}"), Type::const_("Int", Kind::Type))
    }

    #[test]
    fn peano_recognizer_accepts_nat_rejects_foreign_and_missing() {
        let nat = DatatypeDecl::inductive("Nat", vec!["zero".into(), "succ".into()])
            .with_selectors(vec![vec![], vec!["pred".into()]])
            .with_field_sorts(vec![vec![], vec!["Nat".into()]]);
        assert!(Datatypes::peano_shape(&nat).is_some());
        // `wrap(Int)`: unary ctor over a FOREIGN sort → NOT Peano.
        let wrap = DatatypeDecl::inductive("W", vec!["mt".into(), "wrap".into()])
            .with_selectors(vec![vec![], vec!["un".into()]])
            .with_field_sorts(vec![vec![], vec!["Int".into()]]);
        assert!(Datatypes::peano_shape(&wrap).is_none());
        // missing `field_sorts` → fails closed (bridge stays inert).
        let no_fs = DatatypeDecl::inductive("Nat", vec!["zero".into(), "succ".into()])
            .with_selectors(vec![vec![], vec!["pred".into()]]);
        assert!(Datatypes::peano_shape(&no_fs).is_none());
        // 3 constructors → not Peano.
        let three = DatatypeDecl::inductive("T", vec!["a".into(), "b".into(), "c".into()])
            .with_field_sorts(vec![vec![], vec![], vec![]]);
        assert!(Datatypes::peano_shape(&three).is_none());
    }

    #[test]
    fn peano_bridge_emits_image_relations() {
        // `b ≠ zero ∧ pred b = b`: the bridge emits the congruence
        // img(pred b)=img(b) AND the gated img(pred b)=img(b)−1.
        let mut dt = nat_dt_peano();
        let b = Term::var("b", nat_ty());
        let zero = Term::const_("zero", nat_ty());
        let pred_b = pred_of(b.clone());
        dt.assert(Literal::negative(Term::mk_eq(b.clone(), zero).unwrap()).unwrap());
        dt.assert(Literal::positive(Term::mk_eq(pred_b.clone(), b.clone()).unwrap()).unwrap());
        let derived = dt.derive_equalities();
        let (ib, ipb) = (img_of(&b), img_of(&pred_b));
        assert!(
            derived.iter().any(|(a, c)| a.alpha_eq(&ipb) && c.alpha_eq(&ib)),
            "expected congruence img(pred b) = img(b); got {derived:?}"
        );
        // the gated predecessor fact: img(pred b) = (- img(b) 1).
        assert!(
            derived.iter().any(|(a, c)| a.alpha_eq(&ipb)
                && matches!(c.kind(), TermInner::App(..))
                && format!("{c}").contains("- ")),
            "expected gated img(pred b) = img(b) - 1; got {derived:?}"
        );
    }

    #[test]
    fn peano_bridge_inert_on_non_peano() {
        // A non-Peano datatype (zero field_sorts) emits NO image facts.
        let mut dt = nat_dt(); // no field_sorts → peano_shape fails closed
        let b = Term::var("b", nat_ty());
        let zero = Term::const_("zero", nat_ty());
        dt.assert(Literal::negative(Term::mk_eq(b.clone(), zero).unwrap()).unwrap());
        dt.assert(Literal::positive(Term::mk_eq(pred_of(b.clone()), b).unwrap()).unwrap());
        let derived = dt.derive_equalities();
        assert!(
            !derived.iter().any(|(a, _)| format!("{a}").contains("!peano_img!")),
            "bridge must be inert without field_sorts; got {derived:?}"
        );
    }

    #[test]
    fn single_survivor_witness_closes_pred_self_chain() {
        // `b ≠ zero ∧ pred b = b` (Nat): excluding `zero` leaves `succ`
        // as the single survivor → witness `b = succ(pred b)`; with
        // `pred b = b` that is `b = succ b` → acyclicity unsat. The
        // exhaustiveness case-split made definite + the occurs-check.
        let mut dt = nat_dt();
        let b = Term::var("b", nat_ty());
        let zero = Term::const_("zero", nat_ty());
        let pred_b = pred_of(b.clone());
        // mention `pred b` so the witness term can be recovered.
        dt.assert(Literal::negative(Term::mk_eq(b.clone(), zero).unwrap()).unwrap());
        dt.assert(Literal::positive(Term::mk_eq(pred_b.clone(), b.clone()).unwrap()).unwrap());
        // derive_equalities must surface the witness `b = succ(pred b)`.
        let derived = dt.derive_equalities();
        let witness = succ_of(pred_b.clone());
        assert!(
            derived.iter().any(|(a, c)| a.alpha_eq(&b) && c.alpha_eq(&witness)),
            "expected the single-survivor witness b = succ(pred b); got {derived:?}"
        );
    }

    #[test]
    fn single_survivor_does_not_overfire_when_a_ctor_survives() {
        // Excluding only `zero` leaves `succ` possible and introduces no
        // contradiction unless one is forced — `b ≠ zero ∧ pred b = zero`
        // is satisfiable (b = succ zero). The witness must not manufacture
        // a cycle.
        let mut dt = nat_dt();
        let b = Term::var("b", nat_ty());
        let zero = Term::const_("zero", nat_ty());
        dt.assert(Literal::negative(Term::mk_eq(b.clone(), zero.clone()).unwrap()).unwrap());
        dt.assert(Literal::positive(Term::mk_eq(pred_of(b.clone()), zero).unwrap()).unwrap());
        // route the witness back in (as the polite loop would) then check.
        for (a, c) in dt.derive_equalities() {
            dt.assert(Literal::positive(Term::mk_eq(a, c).unwrap()).unwrap());
        }
        assert!(matches!(dt.check(), CheckResult::Sat));
    }

    #[test]
    fn exhaustiveness_single_exclusion_stays_sat() {
        // Excluding only `zero` leaves `succ` open → SAT.
        let mut dt = nat_dt();
        let a = Term::var("a", nat_ty());
        let zero = Term::const_("zero", nat_ty());
        dt.assert(Literal::negative(Term::mk_eq(a.clone(), zero).unwrap()).unwrap());
        assert!(matches!(dt.check(), CheckResult::Sat));
    }

    #[test]
    fn exhaustiveness_generic_disequality_excludes_nothing() {
        // `a ≠ succ b` (a generic disequality, NOT the `succ(pred a)` tester
        // shape) must not be read as `¬is_succ(a)` — adding `a ≠ zero` must
        // stay SAT (a could still be `succ`).
        let mut dt = nat_dt();
        let a = Term::var("a", nat_ty());
        let b = Term::var("b", nat_ty());
        let zero = Term::const_("zero", nat_ty());
        dt.assert(Literal::negative(Term::mk_eq(a.clone(), zero).unwrap()).unwrap());
        dt.assert(Literal::negative(Term::mk_eq(a.clone(), succ_of(b)).unwrap()).unwrap());
        assert!(matches!(dt.check(), CheckResult::Sat));
    }

    #[test]
    fn with_arities_sets_per_constructor_arity() {
        let decl = DatatypeDecl::inductive(
            "Tree_Int",
            vec!["Leaf".into(), "Node".into()],
        )
        .with_arities(vec![1, 3]);
        assert_eq!(decl.arities, vec![1, 3]);
    }

    #[test]
    #[should_panic]
    fn with_arities_panics_on_length_mismatch() {
        let _ = DatatypeDecl::inductive(
            "Bad",
            vec!["A".into(), "B".into()],
        )
        .with_arities(vec![1]);
    }

    // === rc.30 (Y4) — selectors, parametric, applied disjointness ===

    /// `Option_int_` with a `value` selector on `Some_int_`.
    fn opt_registered() -> Datatypes {
        let mut dt = Datatypes::new();
        dt.declare(
            DatatypeDecl::inductive("Option_int_", vec!["None".into(), "Some_int_".into()])
                .with_selectors(vec![vec![], vec!["value".into()]]),
        );
        dt
    }

    fn opt_ty() -> Type {
        Type::const_("Option_int_", Kind::Type)
    }
    fn int_ty() -> Type {
        Type::const_("Int", Kind::Type)
    }
    fn some_int() -> Term {
        Term::const_("Some_int_", Type::fun(int_ty(), opt_ty()).unwrap())
    }
    fn value_sel() -> Term {
        Term::var("value", Type::fun(opt_ty(), int_ty()).unwrap())
    }

    #[test]
    fn with_selectors_sets_arities_and_names() {
        let decl =
            DatatypeDecl::inductive("Opt", vec!["None".into(), "Some".into()])
                .with_selectors(vec![vec![], vec!["value".into()]]);
        assert_eq!(decl.arities, vec![0, 1]);
        assert_eq!(decl.selectors[1], vec!["value".to_string()]);
    }

    #[test]
    fn selector_reduction_emits_field_equality() {
        // value(Some_int_ x) should reduce to x.
        let mut dt = opt_registered();
        let x = Term::var("x", int_ty());
        let some_x = Term::app(some_int(), x.clone()).unwrap();
        let val_some_x = Term::app(value_sel(), some_x).unwrap();
        let y = Term::var("y", int_ty());
        // Assert a literal whose subterm carries the selector app.
        let eq = Term::mk_eq(val_some_x.clone(), y).unwrap();
        let _ = dt.assert(Literal::positive(eq).unwrap());
        let derived = dt.derive_equalities();
        assert!(
            derived
                .iter()
                .any(|(a, b)| a.alpha_eq(&val_some_x) && b.alpha_eq(&x)),
            "expected selector reduction value(Some_int_ x) = x, got {derived:?}"
        );
    }

    #[test]
    fn applied_constructor_disjointness_is_unsat() {
        // (Some_int_ x) = None — distinct constructors → conflict.
        let mut dt = opt_registered();
        let x = Term::var("x", int_ty());
        let some_x = Term::app(some_int(), x).unwrap();
        let none = Term::const_("None", opt_ty());
        let eq = Term::mk_eq(some_x, none).unwrap();
        match dt.assert(Literal::positive(eq).unwrap()) {
            AssertResult::Conflict { .. } => {}
            other => panic!("expected Conflict for applied-ctor disjointness, got {other:?}"),
        }
    }

    #[test]
    fn parametric_datatype_handles_applied_sort() {
        // A `Seq` of arity 1 should be `handles_sort`-recognised both
        // bare and applied (`(Seq Int)`).
        let mut dt = Datatypes::new();
        dt.declare(
            DatatypeDecl::inductive("Seq", vec!["seq_empty".into(), "seq_cons".into()])
                .with_selectors(vec![vec![], vec!["head".into(), "tail".into()]])
                .with_params(vec!["T".into()]),
        );
        let seq_head = Type::const_("Seq", Kind::first_order(1));
        let applied = Type::app(seq_head, int_ty()).unwrap();
        assert!(dt.handles_sort(&applied), "applied (Seq Int) must be handled");
    }
}
