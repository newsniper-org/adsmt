//! The M3-8a lowering core: kernel CIC term → adsmt-core HOL term.
//!
//! See `adsmt-ir/DESIGN.md` §5.1 for the full design + the four P0 soundness
//! guards. This slice covers the **first-order / EUF / quantifier core**:
//! `Prop`↦`Bool`, the logical connectives, EUF (declared sorts / functions /
//! constants as uninterpreted target symbols), n-ary `=`, `Π`-into-`Prop`↦
//! `mk_forall`, implication, and `∃`. **Plus the linear-arithmetic core**: the
//! `theory` prelude's `Int.*` / `Real.*` operators (`+ - * div mod neg abs` and
//! `< <= > >=`) lower to the adsmt-core arith-theory operators — the *same*
//! const names the native SMT-LIB parser emits — so the engine's LIA/LRA solver
//! decides them (numeric literals already lower as `const_(numeral, Int/Real)`;
//! see [`Lowerer::try_arith`]). **Ground integer arithmetic is constant-folded**
//! in the lowering (`(+ 2 1)`↦`3`, `(= 4 3)`↦`false`, `(< 4 3)`↦`false`): the
//! bare engine merges two distinct integer-literal `Const`s in UF (it has no
//! built-in `4 ≠ 3` — `LinArith::assert` `Ignored`s a lit-vs-lit `=`), so the
//! lowering DECIDES a literal (dis)equality / comparison rather than hand the
//! engine an atom it would close unsoundly. This is the native-CLI text
//! preprocessing the lowering path bypasses, replicated soundly (it only ever
//! replaces an under-determined atom with its true value); see [`as_int_lit`] /
//! [`fold_int_binop`]. `int2real` and `pow` / `odd` / `prime` are NOT
//! theory-mapped: they fall through to **EUF** (an uninterpreted function —
//! sound, since it can never manufacture an arithmetic fact, but incomplete; a
//! later slice). The `Nat`/`WNat` injections (`nat2int`/`wnat2int`/`nat2wnat`)
//! are NOT EUF — they lower to the **identity** (the §3b refinement-collapse):
//! a `Nat`/`WNat` variable reaches the engine as a bare `Int` Var carrying its
//! **positivity guard** (`Nat ⟹ x≥1`, `WNat ⟹ x≥0`), emitted at binders and free
//! constants in the canonical `(>= var lo)` orientation. So the **lu-kb type
//! relation IS a decision input**: the positivity drives LIA (`c:Nat ∧ c<1` is
//! `unsat`; #338 LANDED), the soundness-monotone lever — coupled to the
//! sort-collapse (never collapse `Nat`→`Int` without re-asserting positivity).
//! NOTE: this is unrelated to the datatype-acyclicity / LIA-singleton false-sat
//! residuals (those live in `adsmt-theory`'s datatype / LIA solvers, NOT here).
//! Genuinely unlowerable terms — *data-valued* `Match`, `Elim`/recursors,
//! `Fix`, dependent types, proof-as-data, higher-order applications — **abstain**
//! (`Unlowerable`), degrading the whole query to `Unknown`. A *Bool-valued*
//! `Match` DOES lower (the tester+selector encoding) and the engine decides it
//! (selector reduction through congruence).

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

use adsmt_core::{Kind as CKind, Term as CTerm, TermInner as CTermInner, Type as CType, Var as CVar};
use adsmt_ir::{
    AdmissionStep, Ctx, Env, IndSpec, Modality, Term, TermKind, TriggerMap, Univ, as_const_app,
    infer, is_def_eq, occurs, peel_pis, subst_top, whnf,
};
use adsmt_theory::datatypes::DatatypeDecl;

use crate::error::LowerError;

/// The result of lowering: the **datatype declarations** to register with the
/// engine (`Solver::declare_datatype`) plus the asserted goals as adsmt-core
/// `Bool` terms (`Solver::assert`). (adsmt-core has no symbol table — declared
/// sorts and functions are *implicit* in the terms, minted on use; only
/// datatypes need an out-of-band declaration so the engine knows their
/// constructors / disjointness / injectivity.)
#[derive(Debug, Clone)]
pub struct Lowered {
    /// Datatype declarations, in journal order — register each with the engine
    /// *before* asserting the goals.
    pub datatypes: Vec<DatatypeDecl>,
    /// Each goal, a closed adsmt-core term of sort `Bool`.
    pub goals: Vec<CTerm>,
    /// Lowered `:pattern` trigger annotations, keyed by the OUTERMOST lowered
    /// HOL `forall` term (a subterm of some goal — hash-consed, so the
    /// renderer's recursion recognizes it by `==`). Advisory metadata: absent
    /// for every quantifier whose kernel triggers could not be honored.
    pub triggers: HashMap<CTerm, LoweredTriggers>,
}

/// One lowered quantifier's trigger annotation: the telescope arity its
/// re-collected binder list must span, plus the trigger groups (each a
/// multi-pattern), lowered in the SAME binder frame as the body.
#[derive(Debug, Clone)]
pub struct LoweredTriggers {
    pub arity: usize,
    pub groups: Vec<Vec<CTerm>>,
}

/// Lower a checked kernel `Env` + its `Prop` goals into adsmt-core `Bool`
/// terms. **Whole-query, all-or-nothing**: if *any* subterm of *any* goal is
/// unlowerable, the whole call returns `Err` (the caller reports `Unknown`) —
/// never a partial assertion set (dropping a constraint preserves `Unsat` but
/// destroys `Sat`; DESIGN.md §5.1).
pub fn lower(env: &Env, goals: &[Term]) -> Result<Lowered, LowerError> {
    lower_with_triggers(env, goals, &TriggerMap::new())
}

/// [`lower`] with an out-of-band kernel [`TriggerMap`] (the lu-kb face's
/// `trigger` clauses; see `adsmt_ir::triggers`). On a map hit at a `Π` node
/// whose whole telescope is plain data binders, the quantifier lowers in ONE
/// multi-binder step so the pattern terms (de Bruijn over the FULL telescope)
/// lower in the same frame as the body; the result is recorded in
/// [`Lowered::triggers`]. ANY deviation (universe/`Prop` dom, proof binder,
/// unlowerable pattern) just drops that quantifier's triggers — never an
/// error, and with an empty map this is exactly [`lower`].
pub fn lower_with_triggers(
    env: &Env,
    goals: &[Term],
    triggers: &TriggerMap,
) -> Result<Lowered, LowerError> {
    let lw = Lowerer {
        env,
        counter: Cell::new(0),
        extra_hyps: RefCell::new(Vec::new()),
        seen_refinement_consts: RefCell::new(HashSet::new()),
        triggers,
        out_triggers: RefCell::new(HashMap::new()),
    };
    // datatype declarations first (from the admission journal) — if ANY
    // declared inductive is unlowerable (indexed/parametric/Prop-sorted/bad
    // field), the whole query abstains.
    let datatypes = lw.lower_datatypes()?;
    let mut out = Vec::with_capacity(goals.len());
    for g in goals {
        let mut frames = Vec::new();
        let t = lw.lower_term(g, &mut frames)?;
        if t.type_of() != CType::bool_() {
            return Err(LowerError::unlowerable(format!(
                "a goal did not lower to a Bool formula (got sort `{}`)",
                t.type_of()
            )));
        }
        // One whole-formula literal fold per goal (see [`fold_bool_lits`]):
        // a `true`/`false` `Const` leaf must never reach the engine in a
        // connective position — its CNF reads it as a FREE atom. The ∀Bool
        // case split injects literals ARBITRARILY deep (and its folded-to-⊤
        // result can itself sit under an outer `not`/`and` — the third
        // differential round caught exactly that), so the guarantee has to
        // be top-level, not per-construction-site.
        out.push(fold_bool_lits(&t));
    }
    // Nat/WNat refinement-collapse: append the positivity of every free
    // Nat/WNat constant lowered above (a true fact — asserting it is sound and
    // is what keeps the sort-collapse honest; see the design doc §4 invariant A⟺B).
    out.extend(lw.extra_hyps.borrow_mut().drain(..));
    // Re-key the trigger annotations through the SAME whole-formula literal
    // fold the goals get: `fold_bool_lits` is a pure post-order rewrite, so
    // wherever a quantifier survives in a folded goal, the surviving subterm
    // IS `fold_bool_lits(key)` (the tester/`∀Bool` encodings inject literals
    // INSIDE quantifier bodies, so an unfolded key would never be found by
    // the renderer's recursion). A key whose quantifier folded away entirely
    // becomes a dead entry — harmless, advisory.
    let triggers = lw
        .out_triggers
        .into_inner()
        .into_iter()
        .map(|(k, v)| {
            let groups =
                v.groups.iter().map(|g| g.iter().map(fold_bool_lits).collect()).collect();
            (fold_bool_lits(&k), LoweredTriggers { arity: v.arity, groups })
        })
        .collect();
    Ok(Lowered { datatypes, goals: out, triggers })
}

/// One de Bruijn binder, paired across the two representations: the kernel
/// binder *type* (for `infer`'s `Ctx`) and the **globally-fresh** target `Var`
/// it lowered to (the name env). `Bound(0)` = the last frame.
struct Frame {
    ir_sort: Term,
    /// The target term a `Bound` resolving to this frame lowers to: a fresh
    /// `Var` for a quantifier / Π binder, or a **selector application**
    /// `sel_i(major)` for a `match` field binder (so a minor's body reads its
    /// constructor fields off the scrutinee — see [`Lowerer::lower_match`]).
    value: CTerm,
}

struct Lowerer<'e> {
    env: &'e Env,
    /// Monotonic across the whole query → **globally** fresh binder names. NOT
    /// in-scope-unique: the target hash-conses a `Var` by `(name, ty)`, so two
    /// distinct kernel binders sharing a name+sort would alias onto one `Var`
    /// and `mk_forall` would capture across them (DESIGN.md §5.1 P0-3).
    counter: Cell<usize>,
    /// Positivity hypotheses for FREE `Nat`/`WNat` constants encountered while
    /// lowering (the Nat/WNat refinement-collapse §3c free-variable case): a
    /// declared `c : Nat` lowers to a free `Int` `Var`, and `c ≥ 1` must be
    /// asserted alongside the goals or the collapse is a false-sat. Bound
    /// `Nat`/`WNat` variables are guarded inline at the binder (`lower_pi` /
    /// `exists`) instead. See `docs/design/NAT_WNAT_REFINEMENT_COLLAPSE.md`.
    extra_hyps: RefCell<Vec<CTerm>>,
    /// Free-constant names already given a positivity hypothesis (dedup).
    seen_refinement_consts: RefCell<HashSet<String>>,
    /// The out-of-band kernel trigger map ([`lower_with_triggers`]); empty for
    /// plain [`lower`], in which case the takeover path never activates.
    triggers: &'e TriggerMap,
    /// Lowered trigger annotations, keyed by the outermost lowered `forall`
    /// ([`Lowered::triggers`]).
    out_triggers: RefCell<HashMap<CTerm, LoweredTriggers>>,
}

impl Lowerer<'_> {
    fn fresh(&self) -> String {
        let n = self.counter.get();
        self.counter.set(n + 1);
        // `!` cannot appear in an SMT-LIB simple symbol the face elaborates, so
        // a fresh name never collides with a user one.
        format!("x!{n}")
    }

    /// The kernel typing context (binder sorts, innermost last) from `frames`.
    fn ctx(frames: &[Frame]) -> Ctx {
        frames.iter().map(|f| f.ir_sort.clone()).collect()
    }

    /// Walk the admission journal and lower every declared kernel `Inductive` /
    /// mutual group into an engine [`DatatypeDecl`]. An **indexed** (GADT),
    /// **parametric**, or `Prop`/`Type(n>0)`-sorted inductive, or one with a
    /// non-first-order constructor field, has no datatype-theory image →
    /// abstain the whole query (the engine's `Datatypes` theory carries params
    /// but no indices, and an inductive-`Prop` is not an SMT datatype).
    fn lower_datatypes(&self) -> Result<Vec<DatatypeDecl>, LowerError> {
        let mut out = Vec::new();
        for step in self.env.journal() {
            match step {
                AdmissionStep::Inductive(spec) => out.push(self.spec_to_decl(spec)?),
                AdmissionStep::Mutual(specs) => {
                    for spec in specs {
                        out.push(self.spec_to_decl(spec)?);
                    }
                }
                AdmissionStep::Define { .. } | AdmissionStep::Postulate { .. } => {}
            }
        }
        Ok(out)
    }

    /// One kernel inductive spec → an engine `DatatypeDecl`. Selector names are
    /// **synthesized** positionally (`{ctor}!sel{i}`) — the canonical spelling
    /// [`Self::lower_match`]'s tester encoding and [`Self::try_selector`]'s
    /// field-selector dispatch (#403) both emit, and the engine's datatype
    /// theory reduces (`sel(C(..a..)) = a_i`, #330); a `!`-tagged name cannot
    /// collide with a plainly-spelled user symbol.
    fn spec_to_decl(&self, spec: &IndSpec) -> Result<DatatypeDecl, LowerError> {
        if !spec.indices.is_empty() {
            return Err(unl(format!("indexed inductive `{}` (GADT) has no datatype image", spec.name)));
        }
        if !spec.params.is_empty() {
            return Err(unl(format!("parametric inductive `{}` (kernel params)", spec.name)));
        }
        if !matches!(spec.sort, Univ::Type(0)) {
            return Err(unl(format!("inductive `{}` is not `Type(0)` (not an SMT datatype)", spec.name)));
        }
        let mut constructors = Vec::with_capacity(spec.ctors.len());
        let mut arities = Vec::with_capacity(spec.ctors.len());
        let mut selectors = Vec::with_capacity(spec.ctors.len());
        let mut field_sorts = Vec::with_capacity(spec.ctors.len());
        for (cname, fields, _indices) in &spec.ctors {
            // every constructor field sort must lower to a first-order target
            // sort (recursive / cross-member refs resolve via `lower_sort`).
            // Record the lowered field-sort NAME so the engine's Peano
            // `IntegerLike` bridge can verify a recursive `succ(pred Nat)`.
            let mut fs = Vec::with_capacity(fields.len());
            for f in fields {
                fs.push(self.lower_sort(f)?.to_string());
            }
            let n = u32::try_from(fields.len())
                .map_err(|_| unl(format!("constructor `{cname}` has too many fields")))?;
            selectors.push((0..fields.len()).map(|i| format!("{cname}!sel{i}")).collect());
            field_sorts.push(fs);
            arities.push(n);
            constructors.push(cname.clone());
        }
        // finite iff a pure enum (every constructor nullary); conservative —
        // a finite-but-argument-bearing datatype reports infinite (sound: the
        // engine then forgoes finite-domain reasoning, never wrongly applies it).
        let is_finite = arities.iter().all(|&a| a == 0);
        Ok(DatatypeDecl {
            sort_name: spec.name.clone(),
            constructors,
            is_finite,
            arities,
            selectors,
            params: vec![],
            field_sorts,
        })
    }

    /// Lower a kernel **term** (a `Bool` formula or a first-order element).
    /// `whnf` first (δ-unfold defs / β-redexes / ζ-lets), then match the head.
    fn lower_term(&self, term: &Term, frames: &mut Vec<Frame>) -> Result<CTerm, LowerError> {
        let t = whnf(self.env, term);
        // Term-level `ite` lifting: `adsmt-core` has no term-level conditional, so
        // a term-`ite` `(ite A c a b)` (A a non-Bool sort) nested in an atom's
        // argument is removed by **atom duplication** — rewrite the atom
        // `F[ite]` into `(¬c ∨ F[a]) ∧ (c ∨ F[b])` (classically the verified
        // `(c→F[a]) ∧ (¬c→F[b])`) and lower THAT. Applied in place at the smallest
        // enclosing atom, so `c` never crosses a binder — capture-free, no fresh
        // var, no de-Bruijn shift. See docs/design/TERM_ITE_LIFTING.md and the
        // 선검증 `~/term-ite-lifting-verification`.
        if let Some(hoisted) = self.hoist_term_ite(&t) {
            return self.lower_term(&hoisted, frames);
        }
        match t.kind() {
            TermKind::Sort(_) => Err(unl("a sort cannot appear as a first-order term")),
            TermKind::Bound(i) => {
                let idx = frames
                    .len()
                    .checked_sub(1)
                    .and_then(|last| last.checked_sub(*i))
                    .ok_or_else(|| unl("unbound de Bruijn index"))?;
                Ok(frames[idx].value.clone())
            }
            TermKind::Const(name) => self.lower_const(name),
            TermKind::App(..) => self.lower_app(&t, frames),
            TermKind::Pi(dom, cod) => {
                // trigger takeover: a map-keyed telescope lowers in ONE
                // multi-binder step (pattern terms are de Bruijn over the FULL
                // telescope, which the one-binder recursion cannot scope).
                // `None` = no hit / a deviation ⇒ the unchanged path below.
                if let Some(out) = self.try_pi_trigger_takeover(&t, frames)? {
                    return Ok(out);
                }
                self.lower_pi(dom, cod, frames)
            }
            TermKind::Lam(..) => Err(unl("a bare lambda (function value) is not first-order")),
            // whnf ζ-reduces Let and β-reduces (λ.)x, so these never survive as a head.
            TermKind::Let(..) => Err(unl("let survived whnf (unexpected)")),
            TermKind::Match(ind, _motive, minors, major) => {
                self.lower_match(ind, minors, major, &t, frames)
            }
            // `Elim`/`Fix`/`MutElim` are recursion/induction — a first-order
            // solver has no faithful image (the `Match` case below covers
            // non-recursive case analysis, the practical SMT fragment).
            TermKind::Elim(..) | TermKind::Fix { .. } | TermKind::MutElim(..) => {
                Err(unl("datatype recursor / fixpoint lowering (recursion/induction) is a later slice"))
            }
        }
    }

    /// If `t` is a hoistable **atom** (a comparison / equality / predicate
    /// application — NOT a connective or quantifier) whose argument terms contain
    /// a term-`ite`, return the atom-duplication rewrite
    /// `(¬c ∨ t[ite:=a]) ∧ (c ∨ t[ite:=b])` for an innermost such ite; else `None`.
    ///
    /// Only atoms are targets: a connective / quantifier recurses via the normal
    /// dispatch, so the ite is lifted at its SMALLEST enclosing atom — keeping the
    /// condition `c` inside any surrounding binder's scope (capture-free). The
    /// rewrite uses only the non-binding `and`/`or`/`not` prelude consts, so no
    /// de-Bruijn index shifts. Soundness (satisfiability-preserving, both
    /// directions) is pre-verified — see [`lower_term`]'s note.
    fn hoist_term_ite(&self, t: &Term) -> Option<Term> {
        let (name, _) = as_const_app(t)?;
        // Connectives / quantifiers recurse (the ite is lifted at the inner atom);
        // a whole Bool-`ite` formula is handled by `try_prelude`'s `ite` arm.
        if matches!(name.as_str(), "not" | "and" | "or" | "exists" | "forall" | "ite") {
            return None;
        }
        let Some(ite) = find_hoistable_ite(t) else {
            // No hoistable ite — but a `let` / β-redex in the skeleton may be
            // HIDING one (the verus fuel-definition shape
            // `let p = sel(x) in ite(p < 10, …)` — the #403 corpus residual):
            // ζ/β-inline it (the same definitional step `whnf` applies at head
            // position) so the re-entry hoists what surfaces.
            return inline_definitional_redex(t);
        };
        let (_, ia) = as_const_app(&ite)?; // ia = [A, c, a, b]
        if ia.len() != 4 {
            return None;
        }
        let (c, a, b) = (&ia[1], &ia[2], &ia[3]);
        let t_a = subst_kernel(t, &ite, a);
        let t_b = subst_kernel(t, &ite, b);
        let not_c = Term::app(Term::cnst("not"), c.clone());
        let branch_a = Term::apps(Term::cnst("or"), [not_c, t_a]);
        let branch_b = Term::apps(Term::cnst("or"), [c.clone(), t_b]);
        Some(Term::apps(Term::cnst("and"), [branch_a, branch_b]))
    }

    /// A bare constant (post-whnf, so not a `def`): `true`/`false`, or a
    /// declared `open` value. A partially-applied connective / a bare function
    /// symbol / a datatype symbol → abstain.
    fn lower_const(&self, name: &str) -> Result<CTerm, LowerError> {
        match name {
            "true" => return Ok(CTerm::true_const()),
            "false" => return Ok(CTerm::false_const()),
            "not" | "and" | "or" | "=" | "exists" | "forall" | "ite" => {
                return Err(unl(format!("prelude `{name}` used without full application")));
            }
            _ => {}
        }
        let decl = self.env.lookup(name).ok_or_else(|| unl(format!("unknown constant `{name}`")))?;
        match &decl.modality {
            // an `open` symbol or a (nullary) data constructor used as a value.
            Modality::Open | Modality::Constructor => {
                let ty = self.lower_sort(&decl.ty)?;
                if ty.is_fun() {
                    return Err(unl(format!(
                        "bare function / constructor symbol `{name}` used as a value (higher-order)"
                    )));
                }
                let leaf_t = leaf(name, ty, &decl.modality);
                // Nat/WNat refinement-collapse (§3c free-variable case): a free
                // `Nat`/`WNat` constant lowered to a free `Int` Var needs its
                // positivity asserted (the sort-collapse forgets it otherwise →
                // false-sat). Recorded once per name; `lower` appends them.
                if let Some(lo) = self.refinement_lo(&decl.ty)
                    && self.seen_refinement_consts.borrow_mut().insert(name.to_string())
                {
                    let hyp = self.positivity(lo, leaf_t.clone())?;
                    self.extra_hyps.borrow_mut().push(hyp);
                }
                Ok(leaf_t)
            }
            Modality::Def(_) => Err(unl(format!("def `{name}` survived whnf as a value"))),
            Modality::Inductive => {
                Err(unl(format!("inductive type `{name}` used as a first-order value")))
            }
        }
    }

    /// An application: a prelude connective/quantifier/equality (dispatched
    /// arity-exactly), or a structural EUF application of a declared function.
    fn lower_app(&self, t: &Term, frames: &mut Vec<Frame>) -> Result<CTerm, LowerError> {
        let Some((name, args)) = as_const_app(t) else {
            // the head is a `Bound` (applied function variable) or otherwise not
            // a constant → higher-order, no first-order image.
            return Err(unl("higher-order application (a non-constant head)"));
        };
        if let Some(r) = self.try_prelude(&name, &args, frames)? {
            return Ok(r);
        }
        if let Some(r) = self.try_arith(&name, &args, frames)? {
            return Ok(r);
        }
        if let Some(r) = self.try_selector(&name, &args, frames)? {
            return Ok(r);
        }
        // a declared function symbol applied to arguments (EUF).
        let decl = self.env.lookup(&name).ok_or_else(|| unl(format!("unknown function `{name}`")))?;
        match &decl.modality {
            // a declared function (EUF) or a data constructor applied to its
            // arguments — both lower to a structural application of a target
            // symbol; the engine's datatype theory recognizes a constructor by
            // name (from its `DatatypeDecl`).
            Modality::Open | Modality::Constructor => {
                let fty = self.lower_sort(&decl.ty)?;
                let mut cur = leaf(&name, fty, &decl.modality);
                for a in &args {
                    let ca = self.lower_term(a, frames)?;
                    cur = CTerm::app(cur, ca)
                        .map_err(|e| unl(format!("ill-typed application of `{name}`: {e}")))?;
                }
                Ok(cur)
            }
            Modality::Inductive => {
                Err(unl(format!("inductive type former `{name}` applied as a term")))
            }
            Modality::Def(_) => Err(unl(format!("def `{name}` application survived whnf"))),
        }
    }

    /// Dispatch a **canonical selector** application `{ctor}!sel{i}(t)` (#403),
    /// or `Ok(None)` when `name` does not have the exact canonical shape /
    /// `ctor` is not a declared constructor of a non-parametric datatype /
    /// `i` is out of the constructor's field range — falling through keeps the
    /// generic path, so a user symbol that merely LOOKS like a selector still
    /// lowers as its own declared function. The head lowers as a **`Const`
    /// leaf** — the exact idiom [`Self::lower_match`] uses for its synthesized
    /// selector applications — because the engine already declares
    /// `{ctor}!sel{i}` via the `DatatypeDecl` ([`Self::spec_to_decl`]); a
    /// `Var` leaf here would make the render emit a colliding duplicate
    /// `declare-fun`. The lukb face postulates the canonical name `Open` (so
    /// kernel `infer` types the elaborated term), which is why this hook must
    /// run BEFORE the generic declared-symbol dispatch.
    fn try_selector(
        &self,
        name: &str,
        args: &[Term],
        frames: &mut Vec<Frame>,
    ) -> Result<Option<CTerm>, LowerError> {
        let Some((cname, idx)) = name.rsplit_once("!sel") else { return Ok(None) };
        let Ok(i) = idx.parse::<usize>() else { return Ok(None) };
        // exact canonical spelling only (`sel01` is NOT `sel1` — the engine
        // declares the latter; a near-miss must not silently alias onto it).
        if idx != i.to_string() {
            return Ok(None);
        }
        let Some(decl) = self.env.lookup(cname) else { return Ok(None) };
        if !matches!(decl.modality, Modality::Constructor) {
            return Ok(None);
        }
        // the constructor's (non-parametric, non-dependent) telescope
        // `field₀ → … → D`: the i-th domain is the selector's codomain.
        let mut doms = Vec::new();
        let mut rty = decl.ty.clone();
        while let TermKind::Pi(d, b) = rty.kind() {
            doms.push(d.clone());
            rty = b.clone();
        }
        let Some((_dt, targs)) = as_const_app(&rty) else { return Ok(None) };
        if !targs.is_empty() {
            return Ok(None); // parametric datatype — its declaration abstains too
        }
        let Some(fty) = doms.get(i) else { return Ok(None) };
        let dsort = self.lower_sort(&rty)?;
        let fsort = self.lower_sort(fty)?;
        let mut cur = CTerm::const_(name, cfun(dsort, fsort)?);
        for a in args {
            cur = capp(cur, self.lower_term(a, frames)?)?;
        }
        Ok(Some(cur))
    }

    /// Dispatch a prelude operator, or `Ok(None)` if `name` is not one. A
    /// prelude *name* with the wrong arity → abstain (never falls through to a
    /// structural application — a connective is not a first-class value).
    /// Dispatch is guarded on the resolved decl being the prelude `open` const
    /// (a prelude name cannot be user-redeclared — the kernel rejects it — but
    /// we check defensively rather than trusting the string; DESIGN.md §5.1 P0-4).
    fn try_prelude(
        &self,
        name: &str,
        args: &[Term],
        frames: &mut Vec<Frame>,
    ) -> Result<Option<CTerm>, LowerError> {
        let is_prelude = matches!(name, "not" | "and" | "or" | "=" | "exists" | "forall" | "ite");
        if !is_prelude {
            return Ok(None);
        }
        if !matches!(self.env.lookup(name), Some(d) if matches!(d.modality, Modality::Open)) {
            return Err(unl(format!("`{name}` is not bound as the prelude operator")));
        }
        let r = match name {
            "not" => {
                self.arity(name, args, 1)?;
                CTerm::mk_not(self.lower_term(&args[0], frames)?).map_err(meq)?
            }
            "and" => {
                self.arity(name, args, 2)?;
                let a = self.lower_term(&args[0], frames)?;
                let b = self.lower_term(&args[1], frames)?;
                CTerm::mk_and(a, b).map_err(meq)?
            }
            "or" => {
                self.arity(name, args, 2)?;
                let a = self.lower_term(&args[0], frames)?;
                let b = self.lower_term(&args[1], frames)?;
                CTerm::mk_or(a, b).map_err(meq)?
            }
            "=" => {
                // `= : Π(A:Type0). A → A → Prop` — applied as `(= S a b)`.
                self.arity(name, args, 3)?;
                // DROP args[0] (the type argument — a type, not an operand).
                let a = self.lower_term(&args[1], frames)?;
                let b = self.lower_term(&args[2], frames)?;
                if a.type_of().is_fun() {
                    return Err(unl("equality over a function sort (extensional, unsupported)"));
                }
                // Ground constant-fold: a literal-vs-literal **integer** equality
                // is DECIDED here. The bare engine's UF merges two distinct
                // integer-literal `Const`s (it has no built-in `4 ≠ 3` —
                // `LinArith::assert` returns `Ignored` for a lit-vs-lit `=`,
                // leaving it to congruence, which happily unifies them), so
                // handing it `(= 4 3)` is a false-`sat`. See [`as_int_lit`].
                match (as_int_lit(&a), as_int_lit(&b)) {
                    (Some(x), Some(y)) => bool_lit(x == y),
                    // Bool-literal fold — the SAME false-`sat` shape as the
                    // integer fold above, over `true`/`false`: the bare
                    // engine's UF has no built-in `true ≠ false`, so an
                    // opaque Bool-sorted `(= true r)` atom (which the ∀Bool
                    // case split mints: substituting ⊤/⊥ into an `=`-atom
                    // leaves the other side symbolic) merges freely — the
                    // 3-way z3 differential caught `∀h:Bool. h = r` going
                    // `sat`. Fold it away: `(= ⊤ φ) ⟿ φ`, `(= ⊥ φ) ⟿ ¬φ`,
                    // literal-vs-literal decided outright.
                    _ if a.is_true_const() || a.is_false_const()
                        || b.is_true_const() || b.is_false_const() =>
                    {
                        let (lit, other, other_lit) = if a.is_true_const() || a.is_false_const()
                        {
                            (a.is_true_const(), b.clone(), &b)
                        } else {
                            (b.is_true_const(), a.clone(), &a)
                        };
                        if other_lit.is_true_const() || other_lit.is_false_const() {
                            bool_lit(lit == other_lit.is_true_const())
                        } else if lit {
                            other
                        } else {
                            CTerm::mk_not(other).map_err(meq)?
                        }
                    }
                    _ => CTerm::mk_eq(a, b).map_err(meq)?,
                }
            }
            "exists" => {
                // `exists : Π(A:Type0). (A → Prop) → Prop` — `(exists S (λ. ·))`.
                self.arity(name, args, 2)?;
                let asort = self.lower_sort(&args[0])?;
                if asort.is_fun() {
                    return Err(unl("existential over a function sort (higher-order)"));
                }
                let TermKind::Lam(dom, body) = args[1].kind() else {
                    return Err(unl("`exists` predicate is not a lambda"));
                };
                let v = CVar { name: self.fresh(), ty: asort };
                let v_term = CTerm::var(&v.name, v.ty.clone());
                frames.push(Frame { ir_sort: dom.clone(), value: v_term.clone() });
                let body_c = self.lower_term(body, frames);
                frames.pop();
                let body_c = body_c?;
                // Nat/WNat refinement-collapse (§3c): `∃(x:S). P → ∃(x:Int). dom_S(x) ∧ P`
                // (the ∧ polarity is the pre-verified soundness crux; swapping
                // to ⟹ would let an out-of-domain witness satisfy it).
                let body_c = match self.refinement_lo(&args[0]) {
                    Some(lo) => CTerm::mk_and(self.positivity(lo, v_term)?, body_c).map_err(meq)?,
                    None => body_c,
                };
                CTerm::mk_exists(v, body_c).map_err(meq)?
            }
            "ite" => {
                // `ite : Π(A:Type0). Prop → A → A → A` — `(ite A c a b)`. The
                // solver has no `ite` term, but a **Bool-branch** ite (a formula)
                // is classically `(c → a) ∧ (¬c → b)` (faithful). A **term**-`ite`
                // over a non-Bool sort is removed UPSTREAM by atom duplication
                // (`hoist_term_ite`, before this arm), so it never reaches here in
                // a term position; the abstain below is now only a defensive guard
                // for a (mis-checked) non-Bool ite standing as a whole formula.
                self.arity(name, args, 4)?;
                if self.lower_sort(&args[0])? != CType::bool_() {
                    return Err(unl("ite over a non-Bool sort (the solver has no ite term)"));
                }
                let c = self.lower_term(&args[1], frames)?;
                let a = self.lower_term(&args[2], frames)?;
                let b = self.lower_term(&args[3], frames)?;
                let then_b = CTerm::mk_imp(c.clone(), a).map_err(meq)?;
                let else_b = CTerm::mk_imp(CTerm::mk_not(c).map_err(meq)?, b).map_err(meq)?;
                CTerm::mk_and(then_b, else_b).map_err(meq)?
            }
            // `forall` is the kernel arrow/`Π` (handled by lower_pi); a `Const`
            // named `forall` abstains.
            _ => return Err(unl(format!("prelude `{name}` lowering is a later slice"))),
        };
        Ok(Some(r))
    }

    fn arity(&self, name: &str, args: &[Term], want: usize) -> Result<(), LowerError> {
        if args.len() != want {
            return Err(unl(format!(
                "`{name}` applied to {} arguments, expected {want} (partial application abstains)",
                args.len()
            )));
        }
        Ok(())
    }

    /// Recognise a kernel **arithmetic operator** (the [`theory`](adsmt_ir::theory)
    /// prelude's `Int.*` / `Real.*` symbols) and lower it to the adsmt-core
    /// arith-theory operator — the **same const names the native SMT-LIB parser
    /// emits** (`+ - * div mod / < <= > >=`, unary `-` as `(- 0 x)`, `abs`), so
    /// the engine's LIA/LRA solver decides it and the lowered term is *identical*
    /// to the native path (no new soundness surface; the verdict-differential
    /// must agree on pure arithmetic). `Ok(None)` if `name` is not a mapped arith
    /// operator → the EUF fallback (sound-but-uninterpreted for `int2real` /
    /// `pow` / `odd` / `prime` / the `Nat`/`WNat` injections). Numeric literals
    /// need no case here — they already lower as `const_(numeral, Int/Real)` via
    /// [`Self::lower_const`], the native representation.
    fn try_arith(
        &self,
        name: &str,
        args: &[Term],
        frames: &mut Vec<Frame>,
    ) -> Result<Option<CTerm>, LowerError> {
        use adsmt_ir::theory as th;
        // Nat/WNat refinement-collapse (§3b): the Int-internal injections
        // `nat2int`/`wnat2int`/`nat2wnat` are the IDENTITY inclusion (their
        // source and target both lower to the `Int` sort), so erase them and
        // lower the argument directly — a `Nat` variable then reaches LinArith
        // as a bare arith `Var`, not an opaque function application. (The Real
        // injections `nat2real`/`wnat2real`/`int2real` stay EUF — a genuine
        // coercion — sound but uninterpreted, as today.)
        if matches!(name, th::NAT2INT | th::WNAT2INT | th::NAT2WNAT) {
            if !matches!(self.env.lookup(name), Some(d) if matches!(d.modality, Modality::Open)) {
                return Err(unl(format!("`{name}` is not bound as the prelude injection")));
            }
            self.arity(name, args, 1)?;
            return self.lower_term(&args[0], frames).map(Some);
        }
        let int = || CType::const_("Int", CKind::Type);
        let real = || CType::const_("Real", CKind::Type);
        // a binary operator → (smtlib op name, element sort, result-is-Bool).
        let binary: Option<(&str, CType, bool)> = match name {
            th::INT_ADD => Some(("+", int(), false)),
            th::INT_SUB => Some(("-", int(), false)),
            th::INT_MUL => Some(("*", int(), false)),
            th::INT_DIV => Some(("div", int(), false)),
            th::INT_MOD => Some(("mod", int(), false)),
            th::INT_LT => Some(("<", int(), true)),
            th::INT_LE => Some(("<=", int(), true)),
            th::INT_GT => Some((">", int(), true)),
            th::INT_GE => Some((">=", int(), true)),
            th::REAL_ADD => Some(("+", real(), false)),
            th::REAL_SUB => Some(("-", real(), false)),
            th::REAL_MUL => Some(("*", real(), false)),
            th::REAL_DIV => Some(("/", real(), false)),
            th::REAL_LT => Some(("<", real(), true)),
            th::REAL_LE => Some(("<=", real(), true)),
            th::REAL_GT => Some((">", real(), true)),
            th::REAL_GE => Some((">=", real(), true)),
            _ => None,
        };
        let is_unary = matches!(name, th::INT_NEG | th::REAL_NEG | th::INT_ABS);
        if binary.is_none() && !is_unary {
            return Ok(None); // not an arith operator → EUF fallback.
        }
        // Defensive: a prelude arith name cannot be user-rebound (the kernel
        // rejects a duplicate postulate), but verify the resolved decl is the
        // `open` theory symbol rather than trusting the string (DESIGN.md §5.1 P0-4).
        if !matches!(self.env.lookup(name), Some(d) if matches!(d.modality, Modality::Open)) {
            return Err(unl(format!("`{name}` is not bound as the arith prelude operator")));
        }
        // unary: negation → `(- 0 x)`; `abs` → the native `abs` const.
        if matches!(name, th::INT_NEG | th::REAL_NEG) {
            let elem = if name == th::INT_NEG { int() } else { real() };
            return self.arith_neg(name, args, elem, frames).map(Some);
        }
        if name == th::INT_ABS {
            self.arity(name, args, 1)?;
            let x = self.lower_term(&args[0], frames)?;
            let head = CTerm::const_("abs", cfun(int(), int())?);
            return capp(head, x).map(Some);
        }
        // binary operator / comparison.
        let (op, elem, is_rel) = binary.expect("checked non-None above");
        self.arity(name, args, 2)?;
        let a = self.lower_term(&args[0], frames)?;
        let b = self.lower_term(&args[1], frames)?;
        // Ground constant-fold over **integer** literals: a literal-vs-literal
        // `+`/`-`/`*` folds to its value and a comparison to `true`/`false`, so
        // the bare engine never sees a lit-vs-lit atom its arith/UF mishandles
        // (a comparison whose lhs is a literal is not claimed by
        // `LinArith::parse_comparison` → `Unknown`; a lit-vs-lit `=` is merged
        // by UF → false-`sat`). Overflow / div / mod / Real abstain to the
        // plain term (sound — the engine still tries). See [`fold_int_binop`].
        if let (Some(x), Some(y)) = (as_int_lit(&a), as_int_lit(&b))
            && let Some(folded) = fold_int_binop(op, x, y)
        {
            return Ok(Some(folded));
        }
        let result = if is_rel { CType::bool_() } else { elem.clone() };
        let op_ty = cfun(elem.clone(), cfun(elem, result)?)?;
        let head = CTerm::const_(op, op_ty);
        capp(capp(head, a)?, b).map(Some)
    }

    /// Unary minus → the binary `(- 0 x)` (subtraction from a sort-appropriate
    /// zero literal), the representation the arith theory's subtraction handler
    /// expects — mirrors the native parser's `convert_arith_minus`.
    fn arith_neg(
        &self,
        name: &str,
        args: &[Term],
        elem: CType,
        frames: &mut Vec<Frame>,
    ) -> Result<CTerm, LowerError> {
        self.arity(name, args, 1)?;
        let x = self.lower_term(&args[0], frames)?;
        // Ground fold of `-lit` (integer only; `i128::MIN` abstains to the
        // `(- 0 x)` form). Keeps a folded negative literal flowing into outer
        // folds / the engine's `int_lit` reader. See [`as_int_lit`].
        if let Some(v) = as_int_lit(&x)
            && let Some(n) = v.checked_neg()
        {
            return Ok(CTerm::const_(&n.to_string(), int_ty()));
        }
        let op_ty = cfun(elem.clone(), cfun(elem.clone(), elem.clone())?)?;
        let zero = CTerm::const_("0", elem);
        let head = CTerm::const_("-", op_ty);
        capp(capp(head, zero)?, x)
    }

    /// Lower a **non-recursive case analysis** `Match(ind, motive, minors,
    /// major)` (post-`whnf`, so the `major` is *not* a constructor — an
    /// ι-reducible match is already gone). Only a **Bool-valued (Prop)** match —
    /// a case-analysis *formula* — has a first-order image; a data-valued match
    /// needs a value-level `ite` the solver has no term for → abstain (exactly
    /// as a non-Bool `ite` does).
    ///
    /// The encoding mirrors Bool-`ite`'s, generalized to a datatype: for each
    /// constructor `c_j` with fields, emit
    ///
    /// ```text
    ///   major = c_j(sel_{c_j,0}(major), …, sel_{c_j,a-1}(major))  ⇒  minor_j[fields := sel(major)]
    /// ```
    ///
    /// and conjoin over all constructors. The antecedent is a **tester encoded
    /// by equality** — `c_j(sel(major))` rebuilds `major` from its `c_j`-fields,
    /// so the engine's *selector reduction* (`sel_j(C x⃗) = x_j`) + *constructor
    /// disjointness* make it true iff `major`'s head is `c_j` (the engine has no
    /// native tester term; this equality form is the one it actually reasons
    /// about). Sound: for `major = c_m(args)` the `c_m` clause asserts
    /// `minor_m[args]` (the match's value) and every other clause is vacuously
    /// true (its antecedent is disjointness-false) — no over-constraint. The
    /// encoding is also sound under an *incomplete* engine: an under-approximated
    /// selector reduction only fails to derive equalities, so it can never claim
    /// a false UNSAT.
    ///
    /// VERDICT (gate CLOSED): the engine now *decides* the result —
    /// `adsmt-theory`'s datatype theory reduces a selector both on a **literal**
    /// `sel(C(..))` AND on `sel(x)` with `x` congruent to a constructor
    /// (`congruent_selector_reductions`), so the once-gating
    /// `x = succ zero ∧ pred x ≠ zero` is correctly `unsat`. The end-to-end match
    /// verdict is covered by `tests/solve.rs`
    /// `match_reaches_a_sound_unsat_through_selector_congruence`; the lowering
    /// fidelity is verified separately. (Soundness holds regardless: an
    /// under-approximated selector reduction can only fail to derive equalities,
    /// never claim a false UNSAT.)
    fn lower_match(
        &self,
        ind_name: &str,
        minors: &[Term],
        major: &Term,
        match_term: &Term,
        frames: &mut Vec<Frame>,
    ) -> Result<CTerm, LowerError> {
        let ctx = Self::ctx(frames);
        let mty = infer(self.env, &ctx, match_term).map_err(terr)?;
        if !is_def_eq(self.env, &mty, &Term::prop()) {
            return Err(unl("a data-valued match (a value-level case split has no first-order image)"));
        }
        let spec = self
            .ind_spec(ind_name)
            .ok_or_else(|| unl(format!("unknown inductive `{ind_name}` in match")))?;
        // selectors/ctors of a parametric/indexed inductive need the param/index
        // instances — out of scope (its DECLARATION already abstains too).
        if !spec.params.is_empty() || !spec.indices.is_empty() {
            return Err(unl(format!("match over parametric/indexed `{ind_name}` (a later slice)")));
        }
        if minors.len() != spec.ctors.len() {
            return Err(unl("match minor count != constructor count (mis-checked term)"));
        }
        let major_c = self.lower_term(major, frames)?;
        let major_sort = major_c.type_of();
        let mut clauses: Vec<CTerm> = Vec::with_capacity(spec.ctors.len());
        for (j, (cname, fields, _ix)) in spec.ctors.iter().enumerate() {
            // selector applications  sel_{c_j,i}(major)  (the synthesized names
            // MUST match `spec_to_decl`, which registers them with the engine).
            let mut sels = Vec::with_capacity(fields.len());
            for (i, f) in fields.iter().enumerate() {
                let fsort = self.lower_sort(f)?;
                let sel = format!("{cname}!sel{i}");
                sels.push(capp(CTerm::const_(&sel, cfun(major_sort.clone(), fsort)?), major_c.clone())?);
            }
            // tester by equality:  major = c_j(sel_0(major), …).  Build the
            // constructor's (non-parametric) kernel type `fields → I` to lower.
            let mut ctor_ty = Term::cnst(ind_name);
            for f in fields.iter().rev() {
                ctor_ty = Term::arrow(f.clone(), ctor_ty);
            }
            let mut ctor_app = CTerm::const_(cname, self.lower_sort(&ctor_ty)?);
            for s in &sels {
                ctor_app = capp(ctor_app, s.clone())?;
            }
            let is_cj = CTerm::mk_eq(major_c.clone(), ctor_app).map_err(meq)?;
            let branch = self.lower_minor(&minors[j], fields, &sels, frames)?;
            clauses.push(CTerm::mk_imp(is_cj, branch).map_err(meq)?);
        }
        // ⋀ clauses (an uninhabited type → no clauses → vacuously `true`).
        let mut it = clauses.into_iter();
        let Some(first) = it.next() else { return Ok(CTerm::true_const()) };
        it.try_fold(first, |acc, c| CTerm::mk_and(acc, c).map_err(meq))
    }

    /// Lower a `match` minor `minor_j : Π(fields). motive(c_j fields)` with its
    /// field binders mapped to the selector terms `sels` — peel exactly
    /// `fields.len()` leading lambdas (pushing a selector-valued [`Frame`] per
    /// field) and lower the body. A minor that is not a constructor-arity lambda
    /// (not η-long) → abstain.
    fn lower_minor(
        &self,
        minor: &Term,
        fields: &[Term],
        sels: &[CTerm],
        frames: &mut Vec<Frame>,
    ) -> Result<CTerm, LowerError> {
        let base = frames.len();
        let mut cur = minor.clone();
        for (i, f) in fields.iter().enumerate() {
            let w = whnf(self.env, &cur);
            let TermKind::Lam(_dom, body) = w.kind() else {
                frames.truncate(base);
                return Err(unl("match minor is not a constructor-arity lambda (η-expansion needed)"));
            };
            frames.push(Frame { ir_sort: f.clone(), value: sels[i].clone() });
            cur = body.clone();
        }
        let r = self.lower_term(&cur, frames);
        frames.truncate(base);
        r
    }

    /// The admission-journal [`IndSpec`] for `name` (carrying the clean
    /// `(ctor, fields, indices)` telescopes), or `None`. Mirrors
    /// [`Self::lower_datatypes`]'s journal walk.
    fn ind_spec(&self, name: &str) -> Option<&IndSpec> {
        for step in self.env.journal() {
            match step {
                AdmissionStep::Inductive(spec) if spec.name == name => return Some(spec),
                AdmissionStep::Mutual(specs) => {
                    if let Some(s) = specs.iter().find(|s| s.name == name) {
                        return Some(s);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// `Π(x:dom). cod` — a quantified **formula**. Four cases (DESIGN.md §5.1):
    /// quantify-over-`Prop` → the classical finite case split (below);
    /// quantify-over-a-type-universe → abstain; a *proof* binder (`dom : Prop`)
    /// → implication if unused else abstain (proof-as-data); a *data* binder
    /// with `cod : Prop` → `mk_forall`; a function type / dependent codomain →
    /// abstain.
    fn lower_pi(&self, dom: &Term, cod: &Term, frames: &mut Vec<Frame>) -> Result<CTerm, LowerError> {
        if matches!(dom.kind(), TermKind::Sort(Univ::Prop)) {
            // The binder ranges over PROPOSITIONS. The face's `Bool`↦`Prop`
            // collapse makes a surface `forall b: Bool. φ` (the verus Poly
            // prelude quantifies over Bool) and genuine second-order
            // `∀(P:Prop). φ` the SAME kernel term `Pi(Sort(Prop), ·)` — and
            // the TARGET is classical two-valued HOL, where both read as the
            // finite case split
            //
            //     ∀(b:Prop). φ  ⟺  φ[⊤] ∧ φ[⊥]
            //
            // — a logical EQUIVALENCE (classical two-valuedness /
            // propositional extensionality), hence polarity-safe in
            // hypothesis and goal position alike, and it ELIMINATES the
            // quantifier (a single-Bool-binder axiom grounds outright). This
            // closes the former §5.1 P1 deliberate abstain; the `exists` arm
            // already committed to the classical reading (a `Prop` binder
            // lowers to a `Bool`-sorted target variable). The binder value is
            // supplied per branch through the frame (the `lower_match` field
            // idiom) — no kernel-side substitution.
            let mut halves = Vec::with_capacity(2);
            for val in [CTerm::true_const(), CTerm::false_const()] {
                frames.push(Frame { ir_sort: dom.clone(), value: val });
                let half = self.lower_term(cod, frames);
                frames.pop();
                halves.push(half?);
            }
            let bot = halves.pop().expect("two halves");
            let top = halves.pop().expect("two halves");
            // Constant-fold the injected literals THROUGH the halves'
            // connectives (the whole-formula fold in [`lower`] repeats this
            // as the total guarantee — folding here keeps the intermediate
            // term small and the split's own result canonical): the bare
            // engine's CNF treats a `true`/`false` `Const` leaf in a
            // connective position as an ordinary (free!) propositional atom
            // — the 3-way z3 differential caught `∀h:Bool. h ⇒ p` going
            // `sat` (assign the "true" ATOM false and `(=> true p)` is
            // vacuously satisfied).
            return Ok(fold_bool_lits(
                &CTerm::mk_and(top, bot).map_err(meq)?,
            ));
        }
        if matches!(dom.kind(), TermKind::Sort(_)) {
            // The binder ranges over a *type universe*: genuine second-order
            // quantification over types (no first-order image) — abstain.
            return Err(unl("quantification over a sort / universe (second-order)"));
        }
        let ctx = Self::ctx(frames);
        // the binder's sort (reduced) decides proof-vs-data.
        let dom_sort = whnf(self.env, &infer(self.env, &ctx, dom).map_err(terr)?);
        if matches!(dom_sort.kind(), TermKind::Sort(Univ::Prop)) {
            // a proof binder. Faithful only as an implication, and only if the
            // proof is unused (else it is proof-as-data).
            if db_occurs(cod, 0) {
                return Err(unl("dependent proof binder (a proof used as data)"));
            }
            let p = self.lower_term(dom, frames)?;
            // cod is in the extended context but does not use the binder; a
            // dummy frame keeps the de Bruijn levels aligned.
            let dummy = CVar { name: self.fresh(), ty: CType::bool_() };
            frames.push(Frame {
                ir_sort: dom.clone(),
                value: CTerm::var(&dummy.name, dummy.ty.clone()),
            });
            let q = self.lower_term(cod, frames);
            frames.pop();
            return CTerm::mk_imp(p, q?).map_err(meq).map(Ok)?;
        }
        // a data binder: the Pi is a universal formula iff `cod : Prop`.
        let mut ext = ctx.clone();
        ext.push(dom.clone());
        let cod_sort = infer(self.env, &ext, cod).map_err(terr)?;
        if !is_def_eq(self.env, &cod_sort, &Term::prop()) {
            // a genuine function type (or a dependent codomain) used as a term.
            return Err(unl("a (possibly dependent) function type is not a first-order formula"));
        }
        let asort = self.lower_sort(dom)?;
        if asort.is_fun() {
            return Err(unl("universal quantification over a function sort (higher-order)"));
        }
        let v = CVar { name: self.fresh(), ty: asort };
        let v_term = CTerm::var(&v.name, v.ty.clone());
        frames.push(Frame { ir_sort: dom.clone(), value: v_term.clone() });
        let body = self.lower_term(cod, frames);
        frames.pop();
        let body = body?;
        // Nat/WNat refinement-collapse (§3c): `∀(x:S). P → ∀(x:Int). dom_S(x) ⟹ P`
        // (the ⟹ polarity is the pre-verified soundness crux).
        let body = match self.refinement_lo(dom) {
            Some(lo) => CTerm::mk_imp(self.positivity(lo, v_term)?, body).map_err(meq)?,
            None => body,
        };
        CTerm::mk_forall(v, body).map_err(meq)
    }

    /// The **trigger takeover** for a map-keyed `Π` telescope (see
    /// [`lower_with_triggers`]). Picks the LARGEST recorded arity whose
    /// telescope peels cleanly into plain data binders, lowers the residual
    /// body AND every pattern term in the SAME n-binder frame, then folds
    /// `mk_forall` right-to-left — replicating the one-binder path's fresh-var
    /// order and per-binder Nat/WNat positivity guard, so the folded result is
    /// byte-identical to what [`Self::lower_pi`] would have produced. Returns
    /// `Ok(None)` on no map hit or any telescope deviation (universe / `Prop`
    /// dom, proof binder, non-first-order sort, non-`Prop` residual) — the
    /// caller then takes the unchanged one-binder path (triggers dropped). A
    /// pattern that fails to lower drops ONLY the annotation, never the
    /// quantifier: advisory metadata must not degrade a working obligation.
    fn try_pi_trigger_takeover(
        &self,
        t: &Term,
        frames: &mut Vec<Frame>,
    ) -> Result<Option<CTerm>, LowerError> {
        if self.triggers.is_empty() {
            return Ok(None);
        }
        let Some(entries) = self.triggers.get(t) else {
            return Ok(None);
        };
        let mut cands: Vec<&adsmt_ir::QuantTriggers> =
            entries.iter().filter(|e| e.arity > 0 && !e.groups.is_empty()).collect();
        cands.sort_by_key(|e| std::cmp::Reverse(e.arity));
        'cand: for qt in cands {
            let Some((doms, residual)) = peel_pis(t, qt.arity) else { continue };
            // every dom must be a PLAIN data binder (no universe, no `Prop`
            // case-split dom, no proof binder, first-order non-function sort)
            // — checked BEFORE any fresh var is allocated, so declining here
            // leaves the one-binder path's output untouched.
            let mut ctx = Self::ctx(frames);
            let mut sorts = Vec::with_capacity(doms.len());
            for dom in &doms {
                if matches!(dom.kind(), TermKind::Sort(_)) {
                    continue 'cand;
                }
                let Ok(dom_sort) = infer(self.env, &ctx, dom) else { continue 'cand };
                if matches!(whnf(self.env, &dom_sort).kind(), TermKind::Sort(Univ::Prop)) {
                    continue 'cand; // a proof binder — the mk_imp path owns it
                }
                let Ok(asort) = self.lower_sort(dom) else { continue 'cand };
                if asort.is_fun() {
                    continue 'cand;
                }
                sorts.push(asort);
                ctx.push(dom.clone());
            }
            // the residual (guard-arrows included) must be a Prop formula.
            let Ok(cod_sort) = infer(self.env, &ctx, &residual) else { continue 'cand };
            if !is_def_eq(self.env, &cod_sort, &Term::prop()) {
                continue 'cand;
            }
            // push the n binder frames in outer-to-inner order — the same
            // fresh-name sequence the one-binder recursion would consume.
            let base = frames.len();
            let mut vars = Vec::with_capacity(doms.len());
            for (dom, asort) in doms.iter().zip(sorts) {
                let v = CVar { name: self.fresh(), ty: asort };
                let v_term = CTerm::var(&v.name, v.ty.clone());
                frames.push(Frame { ir_sort: dom.clone(), value: v_term.clone() });
                vars.push((v, v_term, dom.clone()));
            }
            let body = self.lower_term(&residual, frames);
            // patterns lower in the SAME frame (after the body, so a
            // fresh-consuming body leaves identical names to the plain path);
            // a failure yields `None` = keep the quantifier, drop the triggers.
            let groups: Option<Vec<Vec<CTerm>>> = body.is_ok().then(|| {
                qt.groups
                    .iter()
                    .map(|g| g.iter().map(|p| self.lower_term(p, frames)).collect())
                    .collect::<Result<_, _>>()
                    .ok()
            }).flatten();
            frames.truncate(base);
            let body = body?; // the one-binder path fails identically here
            // fold right-to-left, replicating lower_pi's positivity guard.
            let mut acc = body;
            for (v, v_term, dom) in vars.into_iter().rev() {
                if let Some(lo) = self.refinement_lo(&dom) {
                    acc = CTerm::mk_imp(self.positivity(lo, v_term)?, acc).map_err(meq)?;
                }
                acc = CTerm::mk_forall(v, acc).map_err(meq)?;
            }
            if let Some(groups) = groups {
                self.out_triggers
                    .borrow_mut()
                    .insert(acc.clone(), LoweredTriggers { arity: qt.arity, groups });
            }
            return Ok(Some(acc));
        }
        Ok(None)
    }

    /// A kernel **type** (a sort) → an adsmt-core `Type`. `Prop`↦`Bool`; a
    /// declared sort `S : Type(0)`↦`Type::const_(S)`; a *non-dependent* function
    /// type `A → B`↦`Type::fun`. A universe / dependent function type / datatype
    /// sort → abstain.
    /// The carrier's positivity lower bound if `ir_sort` (reduced) is a
    /// refinement carrier: `Nat ⟹ 1` (since `0 ∉ Nat`), `WNat ⟹ 0`. `None` for
    /// any other sort. The Nat/WNat refinement-collapse treats these as `Int`
    /// carved out by `x ≥ lo` (see the design doc).
    fn refinement_lo(&self, ir_sort: &Term) -> Option<i128> {
        use adsmt_ir::theory as th;
        let t = whnf(self.env, ir_sort);
        let TermKind::Const(n) = t.kind() else { return None };
        let lo = if n == th::NAT {
            1
        } else if n == th::WNAT {
            0
        } else {
            return None;
        };
        // ONLY the theory's built-in `Nat`/`WNat` (a postulated `Open` sort)
        // collapses — a user `(declare-datatype Nat …)` is `Inductive` and stays
        // a genuine datatype, never coerced to `Int`.
        match self.env.lookup(n) {
            Some(d) if matches!(d.modality, Modality::Open) => Some(lo),
            _ => None,
        }
    }

    /// The positivity atom `v ≥ lo` for a carrier whose refinement lower bound is
    /// `lo` (`Nat ⟹ ≥1`, `WNat ⟹ ≥0`). Emitted in the canonical
    /// **`(op var literal)`** orientation `(>= v lo)` — *not* the equivalent
    /// `(<= lo v)`. The engine's LinArith claims a comparison directly only in the
    /// var-on-the-left form; a literal-on-the-left `(<= lo v)` is re-oriented only
    /// by the lu-smt CLI's preprocessing, so it reached the bare solver as an
    /// uninterpreted atom → `Unknown`, leaving the positivity un-decided (#338).
    /// `v ≥ lo` ≡ `lo ≤ v`, so the §3c relativization polarity is unchanged.
    fn positivity(&self, lo: i128, v: CTerm) -> Result<CTerm, LowerError> {
        let int = CType::const_("Int", CKind::Type);
        let ge_ty = cfun(int.clone(), cfun(int.clone(), CType::bool_())?)?;
        let ge = CTerm::const_(">=", ge_ty);
        let lit = CTerm::const_(&lo.to_string(), int);
        capp(capp(ge, v)?, lit)
    }

    fn lower_sort(&self, ty: &Term) -> Result<CType, LowerError> {
        let t = whnf(self.env, ty);
        match t.kind() {
            TermKind::Sort(Univ::Prop) => Ok(CType::bool_()),
            TermKind::Sort(Univ::Type(_)) => Err(unl("a universe is not a first-order sort")),
            TermKind::Const(name) => {
                use adsmt_ir::theory as th;
                let decl =
                    self.env.lookup(name).ok_or_else(|| unl(format!("unknown sort `{name}`")))?;
                // Nat/WNat refinement-collapse (§3a): the refinement carriers
                // ARE the `Int` solver sort (carved out by a positivity
                // predicate emitted at binders / free constants); the injections
                // into Int become the identity. Soundness is coupled to that
                // positivity — never collapse the sort without it. Guard on
                // `Open` modality: ONLY the theory's built-in Nat/WNat collapses,
                // never a user `(declare-datatype Nat …)` (which is `Inductive`).
                if (name == th::NAT || name == th::WNAT)
                    && matches!(decl.modality, Modality::Open)
                {
                    return Ok(CType::const_(th::INT, CKind::Type));
                }
                match &decl.modality {
                    // a declared sort `S : Type(0)`, or a datatype type former
                    // (the engine knows it is a datatype via its `DatatypeDecl`).
                    Modality::Open
                        if matches!(decl.ty.kind(), TermKind::Sort(Univ::Type(0))) =>
                    {
                        Ok(CType::const_(name, CKind::Type))
                    }
                    Modality::Inductive => Ok(CType::const_(name, CKind::Type)),
                    _ => Err(unl(format!("`{name}` is not a first-order sort"))),
                }
            }
            TermKind::Pi(dom, cod) => {
                if db_occurs(cod, 0) {
                    return Err(unl("a dependent function type has no simply-typed image"));
                }
                let d = self.lower_sort(dom)?;
                let c = self.lower_sort(cod)?;
                CType::fun(d, c).map_err(|e| unl(format!("function sort rejected: {e}")))
            }
            _ => Err(unl("unsupported sort shape")),
        }
    }
}

/// Does de Bruijn `Bound(idx)` (relative to the top of `t`) occur in `t`? Used
/// to split a non-dependent function type (case 3) from a dependent one
/// (case 4). The kernel's `occurs` is by *constant name*, not index, so this is
/// a small dedicated walker.
fn db_occurs(t: &Term, idx: usize) -> bool {
    match t.kind() {
        TermKind::Bound(i) => *i == idx,
        TermKind::Sort(_) | TermKind::Const(_) => false,
        TermKind::App(f, a) => db_occurs(f, idx) || db_occurs(a, idx),
        TermKind::Lam(d, b) | TermKind::Pi(d, b) => db_occurs(d, idx) || db_occurs(b, idx + 1),
        TermKind::Let(ty, v, b) => {
            db_occurs(ty, idx) || db_occurs(v, idx) || db_occurs(b, idx + 1)
        }
        TermKind::Elim(_, m, minors, major) | TermKind::Match(_, m, minors, major) => {
            db_occurs(m, idx) || minors.iter().any(|x| db_occurs(x, idx)) || db_occurs(major, idx)
        }
        TermKind::Fix { ty, body, .. } => db_occurs(ty, idx) || db_occurs(body, idx + 1),
        TermKind::MutElim(_, motives, minors, major) => {
            motives.iter().any(|x| db_occurs(x, idx))
                || minors.iter().any(|x| db_occurs(x, idx))
                || db_occurs(major, idx)
        }
    }
}

/// Find an **innermost** term-`ite` in a term position of `t` — one whose
/// `then`/`else` branches carry no further term-ite, so the atom-duplication
/// measure `Σ_atoms(2^#ite − 1)` strictly decreases per lift (termination).
/// Descends only through application spines and ite BRANCHES — never an ite
/// CONDITION or a binder (`Pi`/`Lam`/`Match`/…) — so the returned ite is reachable
/// from `t` without crossing a binder, and lifting it to `t`'s level is
/// capture-free. See [`Lowerer::hoist_term_ite`].
fn find_hoistable_ite(t: &Term) -> Option<Term> {
    if let Some((name, args)) = as_const_app(t)
        && name == "ite"
        && args.len() == 4
    {
        return find_hoistable_ite(&args[2])
            .or_else(|| find_hoistable_ite(&args[3]))
            .or_else(|| Some(t.clone()));
    }
    match t.kind() {
        TermKind::App(f, a) => find_hoistable_ite(f).or_else(|| find_hoistable_ite(a)),
        _ => None,
    }
}

/// ζ/β-inline ONE ite-carrying definitional redex in `t`'s binder-free term
/// skeleton — the same application-spine + ite-branch descent as
/// [`find_hoistable_ite`]. The verus fuel definitions bind selector reads
/// inside data-valued ite branches (`let p = sel(x) in ite(p < 10, …)`); the
/// `Let` node blocks the hoist descent, and by the time the ordinary
/// recursion ζ-reduces it at head position (`whnf`) the enclosing atom is
/// gone — the revealed non-Bool ite then has no lift site and abstains. Both
/// redex forms are inlined: a kernel `Let` (the lukb face keeps them) and a
/// β-redex `(λx. b) v` (the SMT-LIB face elaborates `let` that way). The
/// rewrite is the kernel's own definitional ζ/β-step (`subst_top` — exactly
/// what `whnf` applies at head position), so it is conversion-sound and, as a
/// reduction of a strongly-normalizing kernel term, terminating. A redex with
/// no `ite` anywhere inside is SKIPPED (it head-reduces on the normal path;
/// rewriting it here would only force a wasted atom re-descent).
fn inline_definitional_redex(t: &Term) -> Option<Term> {
    if let TermKind::Let(_, v, b) = t.kind()
        && (occurs("ite", v) || occurs("ite", b))
    {
        return Some(subst_top(b, v));
    }
    if let TermKind::App(f, a) = t.kind()
        && let TermKind::Lam(_, b) = f.kind()
        && (occurs("ite", a) || occurs("ite", b))
    {
        return Some(subst_top(b, a));
    }
    if let Some((name, args)) = as_const_app(t)
        && name == "ite"
        && args.len() == 4
    {
        // mirror the hoist descent: branches only (a condition's own atoms
        // inline when the classical Bool-`ite` lowering recurses into it).
        for i in [2usize, 3] {
            if let Some(nb) = inline_definitional_redex(&args[i]) {
                let mut na = args.clone();
                na[i] = nb;
                return Some(Term::apps(Term::cnst("ite"), na));
            }
        }
        return None;
    }
    match t.kind() {
        TermKind::App(f, a) => {
            if let Some(nf) = inline_definitional_redex(f) {
                Some(Term::app(nf, a.clone()))
            } else {
                inline_definitional_redex(a).map(|na| Term::app(f.clone(), na))
            }
        }
        _ => None,
    }
}

/// Replace every occurrence of the subterm `target` by `repl` within `t`'s
/// binder-free term skeleton (application spines + ite branches). Mirrors
/// [`find_hoistable_ite`]'s descent: never rewrites inside an ite CONDITION or a
/// binder, so a structurally-identical term at a different scope is untouched.
/// (Leaving an unreplaced copy inside a condition is sound — it collapses to the
/// same branch value under the `c`-case-split, and the recursion hoists it later.)
fn subst_kernel(t: &Term, target: &Term, repl: &Term) -> Term {
    if t == target {
        return repl.clone();
    }
    if let Some((name, args)) = as_const_app(t)
        && name == "ite"
        && args.len() == 4
    {
        return Term::apps(
            Term::cnst("ite"),
            [
                args[0].clone(),
                args[1].clone(),
                subst_kernel(&args[2], target, repl),
                subst_kernel(&args[3], target, repl),
            ],
        );
    }
    match t.kind() {
        TermKind::App(f, a) => {
            Term::app(subst_kernel(f, target, repl), subst_kernel(a, target, repl))
        }
        _ => t.clone(),
    }
}

fn unl(m: impl Into<String>) -> LowerError {
    LowerError::unlowerable(m)
}

/// The adsmt-core `Int` sort (the arith/datatype theories key on its
/// `to_string()`), used by the ground constant-fold.
fn int_ty() -> CType {
    CType::const_("Int", CKind::Type)
}

/// `true`/`false` as an adsmt-core `Bool` literal — the folded value of a
/// ground comparison / (dis)equality.
fn bool_lit(b: bool) -> CTerm {
    if b { CTerm::true_const() } else { CTerm::false_const() }
}

/// An `Int`-sorted integer-literal `Const` as its `i128` value, or `None`.
/// Mirrors the engine's own numeral reader (`adsmt_theory`'s
/// `LinArith::int_lit`): the name `parse::<i128>()`s (so a folded negative
/// literal `Const("-3", Int)` round-trips) **and** the sort is `Int` (so a
/// datatype constructor or a `Real`/`Color` `Const` is never mistaken for a
/// numeral). This is the gate for the ground constant-fold: the bare engine
/// treats two distinct integer-literal `Const`s as opaque UF atoms and merges
/// them (it has no built-in `4 ≠ 3` — `LinArith::assert` `Ignored`s a
/// lit-vs-lit `=`), so the lowering must DECIDE a ground literal
/// (dis)equality / comparison itself rather than hand the engine an atom it
/// would close unsoundly. Soundness-monotone: folding only ever replaces an
/// under-determined atom with its true value (DESIGN.md §5.1 — produce terms
/// the engine decides soundly).
fn as_int_lit(t: &CTerm) -> Option<i128> {
    let CTermInner::Const(c) = t.kind() else { return None };
    if c.ty != int_ty() {
        return None;
    }
    c.name.parse::<i128>().ok()
}

/// `Some(v)` iff `t` is the Bool literal `true`/`false`.
fn as_bool_lit(t: &CTerm) -> Option<bool> {
    if t.is_true_const() {
        Some(true)
    } else if t.is_false_const() {
        Some(false)
    } else {
        None
    }
}

/// Recursively constant-fold `true`/`false` literals through the lowered
/// propositional structure. Used on the `∀Bool` case-split halves, whose
/// substituted branch literal would otherwise survive INSIDE connectives —
/// and the bare engine's CNF reads a `true`/`false` `Const` leaf in a
/// connective position as an ordinary FREE atom (assigning "true" ↦ false
/// satisfies `(=> true p)` vacuously → the differential-caught false-`sat`).
/// Every rule is a propositional identity; a node with no literal operand is
/// rebuilt unchanged (hash-consing keeps that cheap).
fn fold_bool_lits(t: &CTerm) -> CTerm {
    // fold children first (post-order), then the node itself.
    let node = match t.kind() {
        CTermInner::App(f, x) => {
            let (ff, xx) = (fold_bool_lits(f), fold_bool_lits(x));
            CTerm::app(ff, xx).unwrap_or_else(|_| t.clone())
        }
        CTermInner::Lam(v, b) => CTerm::lam((**v).clone(), fold_bool_lits(b)),
        _ => t.clone(),
    };
    if let CTermInner::App(f, rhs) = node.kind() {
        // unary `not`.
        if let CTermInner::Const(c) = f.kind() {
            if c.name == "not" {
                if let Some(v) = as_bool_lit(rhs) {
                    return bool_lit(!v);
                }
                return node;
            }
        }
        // binary connectives `App(App(Const(op), lhs), rhs)`.
        if let CTermInner::App(g, lhs) = f.kind() {
            if let CTermInner::Const(c) = g.kind() {
                let folded = match c.name.as_str() {
                    "and" => match (as_bool_lit(lhs), as_bool_lit(rhs)) {
                        (Some(true), _) => Some(rhs.clone()),
                        (_, Some(true)) => Some(lhs.clone()),
                        (Some(false), _) | (_, Some(false)) => Some(bool_lit(false)),
                        _ => None,
                    },
                    "or" => match (as_bool_lit(lhs), as_bool_lit(rhs)) {
                        (Some(false), _) => Some(rhs.clone()),
                        (_, Some(false)) => Some(lhs.clone()),
                        (Some(true), _) | (_, Some(true)) => Some(bool_lit(true)),
                        _ => None,
                    },
                    "=>" => match (as_bool_lit(lhs), as_bool_lit(rhs)) {
                        (Some(true), _) => Some(rhs.clone()),
                        (Some(false), _) | (_, Some(true)) => Some(bool_lit(true)),
                        (_, Some(false)) => CTerm::mk_not(lhs.clone()).ok(),
                        _ => None,
                    },
                    // Bool-sorted `=` is iff: the same fold as the `"="`
                    // construction arm, re-applied because an INNER fold can
                    // newly expose a literal side ((= (or ⊤ p) q) ⟿ (= ⊤ q)).
                    "=" => match (as_bool_lit(lhs), as_bool_lit(rhs)) {
                        (Some(x), Some(y)) => Some(bool_lit(x == y)),
                        (Some(true), _) => Some(rhs.clone()),
                        (_, Some(true)) => Some(lhs.clone()),
                        (Some(false), _) => CTerm::mk_not(rhs.clone()).ok(),
                        (_, Some(false)) => CTerm::mk_not(lhs.clone()).ok(),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(ft) = folded {
                    return ft;
                }
            }
        }
    }
    node
}

/// Fold a binary integer-arithmetic operator over two literal operands: the
/// `+`/`-`/`*` arms return the value literal, the `<`/`<=`/`>`/`>=` arms the
/// boolean. `None` (→ no fold, emit the plain term, sound) on a non-foldable
/// operator (`div`/`mod`/`/` — Euclidean / Real semantics, left to the engine)
/// or on `i128` overflow.
fn fold_int_binop(op: &str, x: i128, y: i128) -> Option<CTerm> {
    let lit = |n: i128| CTerm::const_(&n.to_string(), int_ty());
    Some(match op {
        "+" => lit(x.checked_add(y)?),
        "-" => lit(x.checked_sub(y)?),
        "*" => lit(x.checked_mul(y)?),
        "<" => bool_lit(x < y),
        "<=" => bool_lit(x <= y),
        ">" => bool_lit(x > y),
        ">=" => bool_lit(x >= y),
        _ => return None,
    })
}

/// A nullary value / applied-function head → the **same adsmt-core leaf the
/// native SMT-LIB parser** (`convert_symbol`) produces: a **numeric literal**
/// (its name leads with a digit — and SMT-LIB simple symbols cannot, so this
/// never misfires on a user symbol) or a **datatype constructor** is a `Const`
/// (the arith / datatype theories recognise it by name); every other declared
/// `open` symbol is a free **`Var`**. This distinction is load-bearing for the
/// arith theory: `LinArith::parse_comparison` only claims `(< x k)` when `x` is
/// a `Var`, so a declared arithmetic operand MUST lower to a `Var` (a `Const`
/// would leave its comparisons uninterpreted → a sound but useless `Unknown`).
/// EUF is indifferent (congruence handles either), which is why the EUF/datatype
/// slices worked before this fix.
fn leaf(name: &str, ty: CType, modality: &Modality) -> CTerm {
    if matches!(modality, Modality::Constructor)
        || name.starts_with(|c: char| c.is_ascii_digit())
    {
        CTerm::const_(name, ty)
    } else {
        CTerm::var(name, ty)
    }
}

/// Build a target function type, mapping a rejection to a clean abstain.
fn cfun(dom: CType, cod: CType) -> Result<CType, LowerError> {
    CType::fun(dom, cod).map_err(|e| unl(format!("arith operator type rejected: {e}")))
}

/// Build a target application, mapping a rejection to a clean abstain.
fn capp(f: CTerm, a: CTerm) -> Result<CTerm, LowerError> {
    CTerm::app(f, a).map_err(|e| unl(format!("arith application rejected: {e}")))
}

/// The target kernel rejected a build step — surface it as a clean abstain
/// (defense-in-depth: a mis-lowering the target's type-checker catches).
fn meq(e: adsmt_core::KernelError) -> LowerError {
    LowerError::unlowerable(format!("target kernel rejected the lowered term: {e}"))
}

/// A source `infer` failed — should not happen on a checked `Env`, but map it
/// to a clean abstain rather than panic.
fn terr(e: adsmt_ir::TypeError) -> LowerError {
    LowerError::unlowerable(format!("source inference failed during lowering: {e}"))
}
