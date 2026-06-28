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
//! see [`Lowerer::try_arith`]). `int2real` and `pow` / `odd` / `prime` are NOT
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
use std::collections::HashSet;

use adsmt_core::{Kind as CKind, Term as CTerm, Type as CType, Var as CVar};
use adsmt_ir::{
    AdmissionStep, Ctx, Env, IndSpec, Modality, Term, TermKind, Univ, as_const_app, infer,
    is_def_eq, whnf,
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
}

/// Lower a checked kernel `Env` + its `Prop` goals into adsmt-core `Bool`
/// terms. **Whole-query, all-or-nothing**: if *any* subterm of *any* goal is
/// unlowerable, the whole call returns `Err` (the caller reports `Unknown`) —
/// never a partial assertion set (dropping a constraint preserves `Unsat` but
/// destroys `Sat`; DESIGN.md §5.1).
pub fn lower(env: &Env, goals: &[Term]) -> Result<Lowered, LowerError> {
    let lw = Lowerer {
        env,
        counter: Cell::new(0),
        extra_hyps: RefCell::new(Vec::new()),
        seen_refinement_consts: RefCell::new(HashSet::new()),
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
        out.push(t);
    }
    // Nat/WNat refinement-collapse: append the positivity of every free
    // Nat/WNat constant lowered above (a true fact — asserting it is sound and
    // is what keeps the sort-collapse honest; see the design doc §4 invariant A⟺B).
    out.extend(lw.extra_hyps.borrow_mut().drain(..));
    Ok(Lowered { datatypes, goals: out })
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
    /// **synthesized** (the face drops them; no `Match`/selector term lowering
    /// in this slice references them, but the engine needs them for injectivity
    /// reasoning); a fresh `!`-tagged name cannot collide with a user symbol.
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
            TermKind::Pi(dom, cod) => self.lower_pi(dom, cod, frames),
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
                CTerm::mk_eq(a, b).map_err(meq)?
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
                // solver has no `ite` term, but a **Bool-branch** ite is
                // classically `(c → a) ∧ (¬c → b)` (faithful); an ite over a
                // non-Bool sort abstains (it would need a fresh-var flattening).
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
    /// quantify-over-a-universe → abstain; a *proof* binder (`dom : Prop`) →
    /// implication if unused else abstain (proof-as-data); a *data* binder with
    /// `cod : Prop` → `mk_forall`; a function type / dependent codomain → abstain.
    fn lower_pi(&self, dom: &Term, cod: &Term, frames: &mut Vec<Frame>) -> Result<CTerm, LowerError> {
        if matches!(dom.kind(), TermKind::Sort(_)) {
            // The binder ranges over a *universe*. `Sort(Type n)` is genuine
            // second-order quantification over types (no first-order image).
            // `Sort(Prop)` is ALSO abstained here, conservatively: the face's
            // `Bool`↦`Prop` collapse makes `∀(h:Bool). φ` and second-order
            // `∀(P:Prop). φ` the SAME kernel term `Pi(Sort(Prop), ·)`, so we
            // cannot tell a (lowerable) Bool quantifier from (unsound) prop
            // quantification — abstaining on both is sound (a deliberate
            // completeness gap; DESIGN.md §5.1 P1).
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

fn unl(m: impl Into<String>) -> LowerError {
    LowerError::unlowerable(m)
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
