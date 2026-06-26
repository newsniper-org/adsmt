//! Elaborate SMT-LIB commands into the typed CIC kernel IR.
//!
//! This is **slice 1**: the propositional + uninterpreted-function + quantifier
//! core. SMT `Bool` is the kernel's `Prop`; the logical connectives are a
//! small `open` (classical / theory-owned) prelude; `=>` is the kernel arrow
//! (implication = a function into `Prop`, impredicatively a `Prop`); `forall`
//! is `Π`. Sorts (`declare-sort`), constants/functions (`declare-const`/
//! `declare-fun`), and `assert` are supported; `define-fun`, datatypes,
//! arithmetic, `ite`/`let`, and the `Int`/`Real`/`Array`/`BitVec` theories are
//! later slices and are *rejected* (sound by omission).
//!
//! Every elaborated declaration is admitted through the kernel's **checked**
//! admitters (`postulate`), and every `assert`ed formula is checked to be a
//! `Prop` by the kernel — so a face bug can only ever yield a [`FaceError`],
//! never a trusted ill-typed term.

use std::collections::HashMap;

use adsmt_ir::{
    Ctx, Env, MutualMember, Term, Univ, build_pi, declare_inductive_indexed, declare_mutual, define,
    infer, is_def_eq, postulate,
};

use crate::error::FaceError;
use crate::sexpr::Sexpr;

/// The result of elaborating an SMT-LIB script: the checked kernel
/// environment (the logical prelude + the user's declarations) and the list
/// of asserted goals (each a kernel-checked `Prop`).
#[derive(Debug)]
pub struct Elaborated {
    pub env: Env,
    /// The asserted formulas, in order — each a closed term of type `Prop`.
    pub goals: Vec<Term>,
}

/// Elaborate a full SMT-LIB script.
pub fn elaborate(src: &str) -> Result<Elaborated, FaceError> {
    let cmds = crate::sexpr::parse_all(src)?;
    let mut e = Elaborator::new()?;
    for cmd in &cmds {
        e.command(cmd)?;
    }
    Ok(Elaborated { env: e.env, goals: e.goals })
}

struct Elaborator {
    env: Env,
    goals: Vec<Term>,
    /// Parametric datatypes (`(declare-datatypes ((List 1) …) ((par (T) …) …))`
    /// members with arity > 0). These are **not** admitted to the kernel — they
    /// are *templates* to be monomorphized at a nested container-application
    /// field sort (`(List Tree)` → a fresh dedicated member). Keyed by the
    /// parametric datatype's name; the constructor field sorts are kept as raw,
    /// un-elaborated S-exprs so they can be substituted then elaborated per
    /// specialization.
    param_dts: HashMap<String, ParamDt>,
}

/// A stored, **not-yet-admitted** parametric datatype template (the SMT-LIB
/// `(par (T1 …) ((ctor (sel sort) …) …))` form). [`Elaborator::specialize`]
/// monomorphizes it at concrete arguments into a fresh kernel mutual member.
struct ParamDt {
    /// The formal type parameters (`T1 …`), substituted at a specialization.
    params: Vec<String>,
    /// `(constructor name, raw field-sort S-exprs)` — the selector names are
    /// dropped (no selectors/testers in this slice) and the field sorts are
    /// kept un-elaborated for per-specialization substitution.
    ctors: Vec<(String, Vec<Sexpr>)>,
}

/// The monomorphization budget: at most this many distinct container
/// specializations per `declare-datatypes` declaration. A polymorphic-recursive
/// / non-regular nesting (`Nest A = nil | cons A (Nest (Pair A A))`) generates
/// ever-larger argument shapes and never saturates — on overflow the whole
/// declaration is *rejected* (`FaceError::Unsupported`), never looped.
const MONO_BUDGET: usize = 256;

/// The maximum **argument-shape depth** of a single specialization site. A
/// *regular* nesting keeps the argument depth bounded (`List Tree`, `List (List
/// Tree)`, … each a fixed depth); a *non-regular* one (`Nest (Pair A A)`)
/// deepens the argument shape without bound — and each level can DOUBLE the
/// argument size, so this cap is what stops a single specialization from
/// exploding *before* the count budget is reached. Tripping it rejects the
/// declaration (sound by omission), never loops. Kept modest because a
/// non-regular site's *size* can double per level (so even constructing the
/// next-level field is exponential): a regular nesting like `List (List (List
/// Tree))` reaches depth ~3-4, far below this.
const MONO_MAX_SITE_DEPTH: usize = 12;

/// A constructor input list — `(ctor name, field-sort telescope, conclusion
/// index expressions)` per constructor — for the kernel's inductive admitters.
type CtorSpecs = Vec<(String, Vec<Term>, Vec<Term>)>;

fn unsupported(m: impl Into<String>) -> FaceError {
    FaceError::Unsupported(m.into())
}

impl Elaborator {
    /// A fresh elaborator with the logical prelude installed (all `open`).
    fn new() -> Result<Self, FaceError> {
        let mut env = Env::new();
        let prop = Term::prop();
        let pp = || Term::arrow(Term::prop(), Term::prop());
        // true, false : Prop
        postulate(&mut env, "true", prop.clone())?;
        postulate(&mut env, "false", prop.clone())?;
        // not : Prop → Prop ; and, or : Prop → Prop → Prop
        postulate(&mut env, "not", pp())?;
        postulate(&mut env, "and", Term::arrow(Term::prop(), pp()))?;
        postulate(&mut env, "or", Term::arrow(Term::prop(), pp()))?;
        // Eq : Π(A:Type0). A → A → Prop
        let eq_ty = Term::pi(
            Term::type_(0),
            Term::arrow(Term::bound(0), Term::arrow(Term::bound(0), Term::prop())),
        );
        postulate(&mut env, "=", eq_ty)?;
        // Exists : Π(A:Type0). (A → Prop) → Prop
        let ex_ty = Term::pi(
            Term::type_(0),
            Term::arrow(Term::arrow(Term::bound(0), Term::prop()), Term::prop()),
        );
        postulate(&mut env, "exists", ex_ty)?;
        // ite : Π(A:Type0). Prop → A → A → A  (theory if-then-else; opaque)
        let ite_ty = Term::pi(
            Term::type_(0),
            Term::arrow(
                Term::prop(),
                Term::arrow(Term::bound(0), Term::arrow(Term::bound(0), Term::bound(0))),
            ),
        );
        postulate(&mut env, "ite", ite_ty)?;
        // the SMT-LIB-standard arithmetic prelude (Int/Real sorts + ops +
        // int2real; all `open`). NOT the lu-kb-only Nat/WNat/pow/odd/prime —
        // those are not SMT-LIB symbols (a user may declare a `Nat` datatype).
        adsmt_ir::theory::install_int_real(&mut env)?;
        Ok(Elaborator { env, goals: Vec::new(), param_dts: HashMap::new() })
    }

    fn command(&mut self, cmd: &Sexpr) -> Result<(), FaceError> {
        let xs = cmd.as_list().ok_or_else(|| unsupported(format!("not a command: {cmd}")))?;
        let head = xs.first().and_then(Sexpr::as_atom).unwrap_or("");
        match head {
            // ignored (no semantic effect on slice 1's job)
            "set-logic" | "set-info" | "set-option" | "check-sat" | "exit" | "push" | "pop"
            | "get-model" | "get-value" | "get-unsat-core" | "echo" | "reset" => Ok(()),
            "declare-sort" => self.declare_sort(xs),
            "declare-const" => self.declare_const(xs),
            "declare-fun" => self.declare_fun(xs),
            "assert" => self.assert(xs),
            "define-fun" => self.define_fun(xs),
            "define-fun-rec" | "define-funs-rec" => {
                Err(unsupported("recursive definitions (define-fun-rec) are a later slice"))
            }
            "declare-datatype" => self.declare_datatype(xs),
            "declare-datatypes" => self.declare_datatypes(xs),
            other => Err(unsupported(format!("command `{other}`"))),
        }
    }

    /// `(declare-sort S 0)` → `open S : Type(0)`.
    fn declare_sort(&mut self, xs: &[Sexpr]) -> Result<(), FaceError> {
        let name = sym(xs, 1, "declare-sort")?;
        let arity = xs.get(2).and_then(Sexpr::as_atom).unwrap_or("0");
        if arity != "0" {
            return Err(unsupported(format!("declare-sort `{name}` arity {arity} (only 0)")));
        }
        postulate(&mut self.env, name, Term::type_(0))?;
        Ok(())
    }

    /// `(declare-const c Sort)` → `open c : Sort`.
    fn declare_const(&mut self, xs: &[Sexpr]) -> Result<(), FaceError> {
        let name = sym(xs, 1, "declare-const")?;
        let sort = xs.get(2).ok_or_else(|| unsupported("declare-const: missing sort"))?;
        let ty = self.elab_sort(sort)?;
        postulate(&mut self.env, name, ty)?;
        Ok(())
    }

    /// `(declare-fun f (A B …) C)` → `open f : A → B → … → C`.
    fn declare_fun(&mut self, xs: &[Sexpr]) -> Result<(), FaceError> {
        let name = sym(xs, 1, "declare-fun")?;
        let params = xs.get(2).and_then(Sexpr::as_list).ok_or_else(|| {
            unsupported(format!("declare-fun `{name}`: expected a parameter list"))
        })?;
        let result = xs.get(3).ok_or_else(|| unsupported("declare-fun: missing result sort"))?;
        let mut ty = self.elab_sort(result)?;
        for p in params.iter().rev() {
            ty = Term::arrow(self.elab_sort(p)?, ty);
        }
        postulate(&mut self.env, name, ty)?;
        Ok(())
    }

    /// `(define-fun f ((x A) …) C body)` → `def f : A → … → C := λ(x:A)…. body`
    /// (non-recursive). The kernel's checked [`define`] verifies the body has
    /// the declared type.
    fn define_fun(&mut self, xs: &[Sexpr]) -> Result<(), FaceError> {
        let name = sym(xs, 1, "define-fun")?.to_string();
        let params = xs.get(2).and_then(Sexpr::as_list).ok_or_else(|| {
            unsupported(format!("define-fun `{name}`: expected a parameter list"))
        })?;
        let ret = xs.get(3).ok_or_else(|| unsupported("define-fun: missing result sort"))?;
        let body = xs.get(4).ok_or_else(|| unsupported("define-fun: missing body"))?;

        let mut ctx: Vec<(String, Term)> = Vec::new();
        let mut sorts = Vec::new();
        for p in params {
            let pair = p.as_list().ok_or_else(|| unsupported("define-fun param `(x Sort)`"))?;
            let pname = pair.first().and_then(Sexpr::as_atom)
                .ok_or_else(|| unsupported("define-fun param name"))?;
            let ty = self.elab_sort(pair.get(1).ok_or_else(|| unsupported("param sort"))?)?;
            sorts.push(ty.clone());
            ctx.push((pname.to_string(), ty));
        }
        let ret_ty = self.elab_sort(ret)?;
        let body_t = self.elab_term(&mut ctx, body)?;
        // f : Π(sorts). ret  :=  λ(sorts). body   (sorts/ret are closed)
        let fn_ty = build_pi(&sorts, ret_ty);
        let lam = build_lam(&sorts, body_t);
        define(&mut self.env, &name, fn_ty, lam)?;
        Ok(())
    }

    /// `(declare-datatype Name (ctor …))` → a kernel **inductive** (its own
    /// singleton group; recursion on `Name` is admitted via the kernel's
    /// positivity check). A nested container field (`(List Name)`) routes
    /// through the monomorphizer like the `declare-datatypes` path.
    fn declare_datatype(&mut self, xs: &[Sexpr]) -> Result<(), FaceError> {
        let name = sym(xs, 1, "declare-datatype")?.to_string();
        let ctor_list = xs.get(2).ok_or_else(|| unsupported("declare-datatype: missing constructors"))?;
        self.admit_datatypes(&[name], &[ctor_list])
    }

    /// `(declare-datatypes ((N₀ a₀) …) (cls₀ …))` → a kernel inductive (one
    /// type) or a **mutual** group (cross-referencing types).
    ///
    /// A member with arity `> 0` is **parametric**: its constructor list is the
    /// SMT-LIB `(par (T …) (ctor-decls))` form. It is *stored* as a [`ParamDt`]
    /// template (not admitted) and used only when a non-parametric member nests
    /// a specialization of it (`(List Tree)`). The arity-0 members plus every
    /// reached specialization are admitted as one kernel group (see
    /// [`Elaborator::admit_datatypes`]). Selectors/testers are a later slice.
    fn declare_datatypes(&mut self, xs: &[Sexpr]) -> Result<(), FaceError> {
        let sort_decls = xs.get(1).and_then(Sexpr::as_list)
            .ok_or_else(|| unsupported("declare-datatypes: sort-declaration list"))?;
        let ctor_lists = xs.get(2).and_then(Sexpr::as_list)
            .ok_or_else(|| unsupported("declare-datatypes: constructor-list list"))?;
        if sort_decls.len() != ctor_lists.len() {
            return Err(unsupported("declare-datatypes: #sorts ≠ #constructor-lists"));
        }
        // Partition into parametric (arity > 0, stored) and non-parametric
        // (arity 0, admitted-with-monomorphization) members.
        let mut nonparam_names = Vec::new();
        let mut nonparam_ctor_lists: Vec<&Sexpr> = Vec::new();
        for (sd, cl) in sort_decls.iter().zip(ctor_lists) {
            let parts = sd.as_list().ok_or_else(|| unsupported("sort decl `(Name arity)`"))?;
            let nm = parts.first().and_then(Sexpr::as_atom)
                .ok_or_else(|| unsupported("datatype name"))?;
            let ar = parts.get(1).and_then(Sexpr::as_atom).unwrap_or("0");
            if ar == "0" {
                nonparam_names.push(nm.to_string());
                nonparam_ctor_lists.push(cl);
            } else {
                self.store_param_dt(nm, ar, cl)?;
            }
        }
        if nonparam_names.is_empty() {
            // a purely-parametric declaration: nothing to admit yet (the
            // templates are stored, monomorphized on first nested use).
            return Ok(());
        }
        self.admit_datatypes(&nonparam_names, &nonparam_ctor_lists)
    }

    /// Store a parametric datatype `(declare-datatypes ((N a) …) ((par (T …)
    /// (ctor-decls)) …))` member as a [`ParamDt`] template — **not** admitted
    /// to the kernel (the kernel has no parametric/nested-container admission;
    /// the face monomorphizes instead, [`Elaborator::specialize`]).
    fn store_param_dt(&mut self, name: &str, arity: &str, cl: &Sexpr) -> Result<(), FaceError> {
        // the `(par (T1 … Tn) (ctor-decls))` wrapper.
        let parts = cl.as_list().ok_or_else(|| {
            unsupported(format!("parametric datatype `{name}`: expected `(par (T …) (ctors))`"))
        })?;
        if parts.first().and_then(Sexpr::as_atom) != Some("par") {
            return Err(unsupported(format!(
                "parametric datatype `{name}` (arity {arity}): expected the `(par …)` form"
            )));
        }
        let params: Vec<String> = parts
            .get(1)
            .and_then(Sexpr::as_list)
            .ok_or_else(|| unsupported(format!("`{name}`: `(par (T …) …)` parameter list")))?
            .iter()
            .map(|p| p.as_atom().map(str::to_string).ok_or_else(|| unsupported("type-parameter name")))
            .collect::<Result<_, _>>()?;
        if params.len().to_string() != arity {
            return Err(unsupported(format!(
                "parametric datatype `{name}`: declared arity {arity} ≠ {} `par` parameters",
                params.len()
            )));
        }
        let ctor_decls = parts
            .get(2)
            .and_then(Sexpr::as_list)
            .ok_or_else(|| unsupported(format!("`{name}`: `(par … (ctor-decls))` list")))?;
        let mut ctors = Vec::new();
        for cd in ctor_decls {
            let cparts = cd.as_list()
                .ok_or_else(|| unsupported("constructor decl `(name (sel sort) …)`"))?;
            let cname = cparts.first().and_then(Sexpr::as_atom)
                .ok_or_else(|| unsupported("constructor name"))?;
            let mut fields = Vec::new();
            for fd in &cparts[1..] {
                let fp = fd.as_list().ok_or_else(|| unsupported("field `(selector sort)`"))?;
                let fsort = fp.get(1).ok_or_else(|| unsupported("field sort"))?;
                fields.push(fsort.clone()); // raw, substituted per specialization
            }
            ctors.push((cname.to_string(), fields));
        }
        if self.param_dts.insert(name.to_string(), ParamDt { params, ctors }).is_some()
            || self.env.lookup(name).is_some()
        {
            return Err(unsupported(format!("datatype `{name}` is already declared")));
        }
        Ok(())
    }

    /// Admit the non-parametric datatypes `names`/`ctor_lists` as ONE kernel
    /// group, monomorphizing every nested container-application field
    /// (`(List Tree)`) into a fresh dedicated member. The output group =
    /// `{output datatypes} ∪ {all reached specializations}`, emitted through the
    /// kernel's checked `declare_mutual` / `declare_inductive_indexed` — whose
    /// positivity gate re-checks every member (the soundness backstop).
    fn admit_datatypes(
        &mut self,
        names: &[String],
        ctor_lists: &[&Sexpr],
    ) -> Result<(), FaceError> {
        // The set of group-member names: the output datatypes (in scope in every
        // constructor) PLUS specializations (added as the worklist saturates).
        let mut mono = Mono::new(names.to_vec());
        let mut members = Vec::new();
        // 1. the output (arity-0) datatypes themselves.
        for (nm, cl) in names.iter().zip(ctor_lists) {
            let ctors = self.parse_ctors_mono(cl, &mut mono)?;
            members.push(MutualMember {
                name: nm.clone(),
                params: vec![],
                indices: vec![],
                sort: Univ::Type(0),
                ctors,
            });
        }
        // 2. drain the specialization worklist to saturation (bounded).
        while let Some(site) = mono.pop() {
            let member = self.specialize(&site, &mut mono)?;
            members.push(member);
        }
        // 3. admit the whole group through the kernel's checked admitters.
        //    (A singleton group with no cross-refs takes the inductive path.)
        if members.len() == 1 {
            let m = members.pop().unwrap();
            declare_inductive_indexed(&mut self.env, &m.name, m.params, m.indices, m.sort, m.ctors)?;
        } else {
            declare_mutual(&mut self.env, members)?;
        }
        Ok(())
    }

    /// Parse a datatype's constructor list into the kernel's `(ctor name,
    /// field-sort telescope, indices = [])` shape, elaborating each field sort
    /// through the monomorphizer (so a nested `(List Tree)` enqueues a
    /// specialization and resolves to `cnst("List#Tree")`). Selectors are
    /// dropped (no selectors/testers yet).
    fn parse_ctors_mono(&self, ctor_list: &Sexpr, mono: &mut Mono) -> Result<CtorSpecs, FaceError> {
        let ctors = ctor_list.as_list().ok_or_else(|| unsupported("constructor list"))?;
        let mut out = Vec::new();
        for cd in ctors {
            let parts = cd.as_list()
                .ok_or_else(|| unsupported("constructor decl `(name (sel sort) …)`"))?;
            let cname = parts.first().and_then(Sexpr::as_atom)
                .ok_or_else(|| unsupported("constructor name"))?;
            let mut fields = Vec::new();
            for fd in &parts[1..] {
                let fp = fd.as_list().ok_or_else(|| unsupported("field `(selector sort)`"))?;
                let fsort = fp.get(1).ok_or_else(|| unsupported("field sort"))?;
                fields.push(self.elab_dt_sort_mono(fsort, mono)?);
            }
            out.push((cname.to_string(), fields, Vec::new()));
        }
        Ok(out)
    }

    /// Specialize the parametric datatype at `site` (`F` applied to `args`) into
    /// a fresh non-parametric kernel member named `mangle(site)`. The formal
    /// params are substituted by the arg S-exprs in each constructor field sort,
    /// then each field is elaborated (recursively enqueueing further nestings);
    /// constructor names are mangled with the site suffix so distinct
    /// specializations don't collide.
    fn specialize(&self, site: &MonoSite, mono: &mut Mono) -> Result<MutualMember, FaceError> {
        let template = self.param_dts.get(&site.head).expect("site head is a stored param dt");
        if template.params.len() != site.args.len() {
            return Err(unsupported(format!(
                "`{}` applied to {} args but has {} parameters",
                site.head, site.args.len(), template.params.len()
            )));
        }
        let subst: HashMap<&str, &Sexpr> =
            template.params.iter().map(String::as_str).zip(&site.args).collect();
        let suffix = mangle(&site.head, &site.args);
        let mut ctors = Vec::new();
        for (cname, fields) in &template.ctors {
            let mut tele = Vec::new();
            for f in fields {
                let substituted = subst_sexpr(f, &subst);
                tele.push(self.elab_dt_sort_mono(&substituted, mono)?);
            }
            // mangle the ctor name so distinct specializations are disjoint
            // (else the kernel's DuplicateConst rejects the second `cons`).
            ctors.push((format!("{cname}#{suffix}"), tele, Vec::new()));
        }
        Ok(MutualMember {
            name: suffix,
            params: vec![],
            indices: vec![],
            sort: Univ::Type(0),
            ctors,
        })
    }

    /// A datatype field sort, monomorphizing:
    /// * a group-member name (an output datatype or an already-named
    ///   specialization) → `cnst(name)` (usable before it is in the env);
    /// * a container application `(F a …)` where `F` is a stored parametric
    ///   datatype → enqueue the specialization and resolve to its mangled name;
    /// * otherwise a normal sort (a declared sort / `Bool`).
    fn elab_dt_sort_mono(&self, s: &Sexpr, mono: &mut Mono) -> Result<Term, FaceError> {
        match s {
            Sexpr::Atom(name) if mono.is_member(name) => Ok(Term::cnst(name.clone())),
            Sexpr::Atom(_) => self.elab_sort(s),
            Sexpr::List(xs) => {
                let head = xs.first().and_then(Sexpr::as_atom);
                match head {
                    Some(h) if self.param_dts.contains_key(h) => {
                        let args: Vec<Sexpr> = xs[1..].to_vec();
                        if args.is_empty() {
                            return Err(unsupported(format!(
                                "parametric datatype `{h}` used with no arguments"
                            )));
                        }
                        let name = mono.enqueue(h.to_string(), args)?;
                        Ok(Term::cnst(name))
                    }
                    _ => self.elab_sort(s),
                }
            }
        }
    }

    /// `(assert φ)` → elaborate `φ`, **check it is a `Prop`** (the kernel
    /// gate), and record it as a goal.
    fn assert(&mut self, xs: &[Sexpr]) -> Result<(), FaceError> {
        let phi = xs.get(1).ok_or_else(|| unsupported("assert: missing formula"))?;
        self.intern_numerals(phi)?;
        let mut ctx: Vec<(String, Term)> = Vec::new();
        let t = self.elab_term(&mut ctx, phi)?;
        // the kernel re-checks: the formula must be a closed Prop.
        let ty = infer(&self.env, &Ctx::new(), &t)?;
        if !is_def_eq(&self.env, &ty, &Term::prop()) {
            return Err(unsupported(format!("asserted term has sort `{ty}`, expected Bool/Prop")));
        }
        self.goals.push(t);
        Ok(())
    }

    /// A sort to a kernel type. `Bool → Prop`; a declared sort `S → S`.
    fn elab_sort(&self, s: &Sexpr) -> Result<Term, FaceError> {
        match s {
            Sexpr::Atom(name) if name == "Bool" => Ok(Term::prop()),
            Sexpr::Atom(name) => {
                match self.env.lookup(name) {
                    // a previously declared sort `S : Type(0)`.
                    Some(d) if is_type0(&d.ty) => Ok(Term::cnst(name.clone())),
                    Some(_) => Err(unsupported(format!("`{name}` is not a sort"))),
                    // `Int`/`Real` are now declared by the arithmetic prelude
                    // (handled by the `is_type0` arm above); these remain later
                    // slices.
                    None if matches!(
                        name.as_str(),
                        "String" | "RoundingMode" | "RegLan"
                    ) =>
                    {
                        Err(unsupported(format!("the `{name}` theory is a later slice")))
                    }
                    None => Err(unsupported(format!("unknown sort `{name}`"))),
                }
            }
            Sexpr::List(_) => Err(unsupported(format!(
                "parametric / theory sort `{s}` (Int/Real/Array/BitVec/… are a later slice)"
            ))),
        }
    }

    /// A term, in the local quantifier context `ctx` (outermost binder first,
    /// matching the kernel's de Bruijn convention). Returns a kernel term.
    fn elab_term(&self, ctx: &mut Vec<(String, Term)>, e: &Sexpr) -> Result<Term, FaceError> {
        match e {
            Sexpr::Atom(name) => {
                // a bound variable shadows globals (innermost-first).
                if let Some(pos) = ctx.iter().rposition(|(n, _)| n == name) {
                    return Ok(Term::bound(ctx.len() - 1 - pos));
                }
                if self.env.lookup(name).is_some() {
                    return Ok(Term::cnst(name.clone()));
                }
                if name.starts_with('"') || name.bytes().next().is_some_and(|b| b.is_ascii_digit()) {
                    return Err(unsupported(format!("literal `{name}` (no theory in slice 1)")));
                }
                Err(unsupported(format!("unknown symbol `{name}`")))
            }
            Sexpr::List(xs) => {
                let head = xs.first().ok_or_else(|| unsupported("empty application"))?;
                let h = head.as_atom().ok_or_else(|| {
                    unsupported(format!("higher-order application head `{head}` (later slice)"))
                })?;
                let args = &xs[1..];
                match h {
                    "and" => self.fold_binop(ctx, "and", args, "true"),
                    "or" => self.fold_binop(ctx, "or", args, "false"),
                    "not" => {
                        let a = one(args, "not")?;
                        Ok(Term::app(Term::cnst("not"), self.elab_term(ctx, a)?))
                    }
                    "=>" => self.elab_implies(ctx, args),
                    "=" => self.elab_eq(ctx, args),
                    "distinct" => self.elab_distinct(ctx, args),
                    "forall" => self.elab_quant(ctx, args, true),
                    "exists" => self.elab_quant(ctx, args, false),
                    "ite" => self.elab_ite(ctx, args),
                    "let" => self.elab_let(ctx, args),
                    // arithmetic (Int/Real), dispatched by operand sort.
                    "+" | "-" | "*" | "div" | "mod" | "abs" | "/" | "<" | "<=" | ">" | ">="
                    | "to_real" => self.elab_arith(ctx, h, args),
                    // an applied (declared) function symbol.
                    _ => {
                        if self.env.lookup(h).is_none() && !ctx.iter().any(|(n, _)| n == h) {
                            return Err(unsupported(format!("unknown function symbol `{h}`")));
                        }
                        let f = self.elab_term(ctx, head)?;
                        let mut t = f;
                        for a in args {
                            t = Term::app(t, self.elab_term(ctx, a)?);
                        }
                        Ok(t)
                    }
                }
            }
        }
    }

    /// Variadic `(op a1 … an)` right-folded onto the binary `op`; the empty
    /// case is `unit` (`true` for `and`, `false` for `or`).
    fn fold_binop(
        &self,
        ctx: &mut Vec<(String, Term)>,
        op: &str,
        args: &[Sexpr],
        unit: &str,
    ) -> Result<Term, FaceError> {
        if args.is_empty() {
            return Ok(Term::cnst(unit.to_string()));
        }
        let mut acc = self.elab_term(ctx, &args[args.len() - 1])?;
        for a in args[..args.len() - 1].iter().rev() {
            let ta = self.elab_term(ctx, a)?;
            acc = Term::apps(Term::cnst(op.to_string()), [ta, acc]);
        }
        Ok(acc)
    }

    /// `(=> a b … z)` → `a → b → … → z` (the kernel arrow; right-associative).
    fn elab_implies(&self, ctx: &mut Vec<(String, Term)>, args: &[Sexpr]) -> Result<Term, FaceError> {
        if args.len() < 2 {
            return Err(unsupported("`=>` needs at least 2 arguments"));
        }
        let mut acc = self.elab_term(ctx, &args[args.len() - 1])?;
        for a in args[..args.len() - 1].iter().rev() {
            let ta = self.elab_term(ctx, a)?;
            acc = Term::arrow(ta, acc);
        }
        Ok(acc)
    }

    /// Elaborate `args`, infer each term's sort, and require they all share one
    /// sort — returns `(the common sort, the terms)`.
    fn elab_same_sorted(
        &self,
        ctx: &mut Vec<(String, Term)>,
        args: &[Sexpr],
        what: &str,
    ) -> Result<(Term, Vec<Term>), FaceError> {
        let mut terms = Vec::with_capacity(args.len());
        let mut sort: Option<Term> = None;
        for a in args {
            let t = self.elab_term(ctx, a)?;
            let s = infer(&self.env, &kernel_ctx(ctx), &t)?;
            match &sort {
                None => sort = Some(s),
                Some(s0) if !is_def_eq(&self.env, s0, &s) => {
                    return Err(unsupported(format!("`{what}` of differing sorts `{s0}` and `{s}`")));
                }
                _ => {}
            }
            terms.push(t);
        }
        Ok((sort.expect("at least one argument"), terms))
    }

    /// Arithmetic (`+ - * div mod abs / < <= > >= to_real`), dispatched by the
    /// operand sort (`Int` vs `Real`) inferred from the arguments. `to_real` is
    /// the explicit `Int → Real` injection; comparisons return `Prop` and chain
    /// (`(< a b c)` ≡ `a<b ∧ b<c`); the binary ops fold n-ary left-associatively
    /// (matching SMT-LIB).
    fn elab_arith(
        &self,
        ctx: &mut Vec<(String, Term)>,
        op: &str,
        args: &[Sexpr],
    ) -> Result<Term, FaceError> {
        use adsmt_ir::theory as th;
        // `to_real`: the Int→Real injection (unary).
        if op == "to_real" {
            let a = self.elab_term(ctx, one(args, "to_real")?)?;
            return Ok(Term::app(Term::cnst(th::INT2REAL), a));
        }
        // unary minus: `(- x)`.
        if op == "-" && args.len() == 1 {
            let t = self.elab_term(ctx, &args[0])?;
            let s = infer(&self.env, &kernel_ctx(ctx), &t)?;
            let neg = if is_int(&self.env, &s) {
                th::INT_NEG
            } else if is_real(&self.env, &s) {
                th::REAL_NEG
            } else {
                return Err(unsupported(format!("unary `-` on non-numeric sort `{s}`")));
            };
            return Ok(Term::app(Term::cnst(neg), t));
        }
        let (sort, terms) = self.elab_same_sorted(ctx, args, op)?;
        let int = is_int(&self.env, &sort);
        let real = is_real(&self.env, &sort);
        if !int && !real {
            return Err(unsupported(format!("`{op}` on non-numeric sort `{sort}`")));
        }
        let need = |k: usize| -> Result<(), FaceError> {
            if terms.len() < k {
                Err(unsupported(format!("`{op}` needs ≥{k} arguments, got {}", terms.len())))
            } else {
                Ok(())
            }
        };
        match op {
            "+" => Ok(fold_left(&terms, if int { th::INT_ADD } else { th::REAL_ADD })),
            "*" => Ok(fold_left(&terms, if int { th::INT_MUL } else { th::REAL_MUL })),
            "-" => {
                need(2)?;
                Ok(fold_left(&terms, if int { th::INT_SUB } else { th::REAL_SUB }))
            }
            "div" => {
                need(2)?;
                if !int {
                    return Err(unsupported("`div` is Int-only (use `/` for Real)"));
                }
                Ok(fold_left(&terms, th::INT_DIV))
            }
            "mod" => {
                if terms.len() != 2 || !int {
                    return Err(unsupported("`mod` is binary Int `mod`"));
                }
                Ok(Term::apps(Term::cnst(th::INT_MOD), [terms[0].clone(), terms[1].clone()]))
            }
            "abs" => {
                if terms.len() != 1 || !int {
                    return Err(unsupported("`abs` is unary Int `abs`"));
                }
                Ok(Term::app(Term::cnst(th::INT_ABS), terms[0].clone()))
            }
            "/" => {
                need(2)?;
                if !real {
                    return Err(unsupported("`/` is Real-only (use `div` for Int)"));
                }
                Ok(fold_left(&terms, th::REAL_DIV))
            }
            "<" | "<=" | ">" | ">=" => {
                need(2)?;
                let rel = match op {
                    "<" => if int { th::INT_LT } else { th::REAL_LT },
                    "<=" => if int { th::INT_LE } else { th::REAL_LE },
                    ">" => if int { th::INT_GT } else { th::REAL_GT },
                    _ => if int { th::INT_GE } else { th::REAL_GE }, // ">="
                };
                let conj: Vec<Term> = terms
                    .windows(2)
                    .map(|w| Term::apps(Term::cnst(rel), [w[0].clone(), w[1].clone()]))
                    .collect();
                Ok(and_chain(conj))
            }
            _ => unreachable!("elab_arith dispatched on a non-arith head `{op}`"),
        }
    }

    /// Pre-pass over a term s-expr: idempotently postulate every integer/decimal
    /// numeral as an opaque literal constant ([`adsmt_ir::theory::int_literal`] /
    /// [`adsmt_ir::theory::real_literal`]), so the (`&self`) term elaborator then
    /// resolves it from the env. Needed because elaboration borrows `&self` but
    /// literal interning needs `&mut env`.
    fn intern_numerals(&mut self, e: &Sexpr) -> Result<(), FaceError> {
        match e {
            Sexpr::Atom(a) => {
                if let Some(c) = canonical_int(a) {
                    adsmt_ir::theory::int_literal(&mut self.env, &c)?;
                } else if let Some(c) = canonical_real(a) {
                    adsmt_ir::theory::real_literal(&mut self.env, &c)?;
                }
                Ok(())
            }
            Sexpr::List(xs) => {
                for x in xs {
                    self.intern_numerals(x)?;
                }
                Ok(())
            }
        }
    }

    /// `(= a b …)` → the conjunction of consecutive `Eq`s (`a=b ∧ b=c ∧ …`).
    fn elab_eq(&self, ctx: &mut Vec<(String, Term)>, args: &[Sexpr]) -> Result<Term, FaceError> {
        if args.len() < 2 {
            return Err(unsupported("`=` needs at least 2 arguments"));
        }
        let (sort, terms) = self.elab_same_sorted(ctx, args, "=")?;
        let conj: Vec<Term> = terms
            .windows(2)
            .map(|w| Term::apps(Term::cnst("="), [sort.clone(), w[0].clone(), w[1].clone()]))
            .collect();
        Ok(and_chain(conj))
    }

    /// `(distinct a b …)` → the conjunction of `not (= aᵢ aⱼ)` for all `i<j`.
    fn elab_distinct(
        &self,
        ctx: &mut Vec<(String, Term)>,
        args: &[Sexpr],
    ) -> Result<Term, FaceError> {
        if args.len() < 2 {
            return Err(unsupported("`distinct` needs at least 2 arguments"));
        }
        let (sort, terms) = self.elab_same_sorted(ctx, args, "distinct")?;
        let mut conj = Vec::new();
        for i in 0..terms.len() {
            for j in (i + 1)..terms.len() {
                let eq =
                    Term::apps(Term::cnst("="), [sort.clone(), terms[i].clone(), terms[j].clone()]);
                conj.push(Term::app(Term::cnst("not"), eq));
            }
        }
        Ok(and_chain(conj))
    }

    /// `(ite c a b)` → `ite A c a b` (`A` = the common branch sort; the kernel
    /// enforces `c : Prop` via `ite`'s type).
    fn elab_ite(&self, ctx: &mut Vec<(String, Term)>, args: &[Sexpr]) -> Result<Term, FaceError> {
        if args.len() != 3 {
            return Err(unsupported("`ite` needs exactly 3 arguments"));
        }
        let c = self.elab_term(ctx, &args[0])?;
        let (sort, branches) = self.elab_same_sorted(ctx, &args[1..], "ite branches")?;
        Ok(Term::apps(Term::cnst("ite"), [sort, c, branches[0].clone(), branches[1].clone()]))
    }

    /// `(let ((x e) …) body)` → the β-redex `(λ(x)…. body) e …`. SMT `let` is
    /// **parallel**: each `e` is elaborated in the OUTER scope, then applied as
    /// an argument — so it is correctly outer-scoped while the body sees all the
    /// bindings (de Bruijn).
    fn elab_let(&self, ctx: &mut Vec<(String, Term)>, args: &[Sexpr]) -> Result<Term, FaceError> {
        if args.len() != 2 {
            return Err(unsupported("`let` needs a binding list and a body"));
        }
        let bindings = args[0].as_list().ok_or_else(|| unsupported("let binding list"))?;
        if bindings.is_empty() {
            return Err(unsupported("`let` with no bindings"));
        }
        let mut names = Vec::new();
        let mut exprs = Vec::new();
        let mut sorts = Vec::new();
        for b in bindings {
            let pair = b.as_list().ok_or_else(|| unsupported("let binding `(x e)`"))?;
            let name =
                pair.first().and_then(Sexpr::as_atom).ok_or_else(|| unsupported("let var"))?;
            let expr = pair.get(1).ok_or_else(|| unsupported("let value"))?;
            let e = self.elab_term(ctx, expr)?; // OUTER scope (parallel let)
            let ty = infer(&self.env, &kernel_ctx(ctx), &e)?;
            names.push(name.to_string());
            exprs.push(e);
            sorts.push(ty);
        }
        let depth0 = ctx.len();
        for (n, ty) in names.iter().zip(&sorts) {
            ctx.push((n.clone(), ty.clone()));
        }
        let body = self.elab_term(ctx, &args[1])?;
        ctx.truncate(depth0);
        Ok(Term::apps(build_lam(&sorts, body), exprs))
    }

    /// `(forall ((x A) …) φ)` → `Π(x:A). … φ`; `exists` → `Exists A (λx:A. …)`.
    fn elab_quant(
        &self,
        ctx: &mut Vec<(String, Term)>,
        args: &[Sexpr],
        forall: bool,
    ) -> Result<Term, FaceError> {
        if args.len() != 2 {
            return Err(unsupported("quantifier needs a binder list and a body"));
        }
        let binders = args[0].as_list().ok_or_else(|| unsupported("quantifier binder list"))?;
        if binders.is_empty() {
            return Err(unsupported("quantifier with no binders"));
        }
        // push each (name, sort) onto the context, recording the sorts.
        let depth0 = ctx.len();
        let mut sorts = Vec::new();
        for bv in binders {
            let pair = bv.as_list().ok_or_else(|| unsupported("binder must be `(x Sort)`"))?;
            let name = pair.first().and_then(Sexpr::as_atom)
                .ok_or_else(|| unsupported("binder name"))?;
            let sort = pair.get(1).ok_or_else(|| unsupported("binder sort"))?;
            let ty = self.elab_sort(sort)?;
            sorts.push(ty.clone());
            ctx.push((name.to_string(), ty));
        }
        let body = self.elab_term(ctx, &args[1])?;
        ctx.truncate(depth0);

        if forall {
            // Π(sorts). body
            Ok(adsmt_ir::build_pi(&sorts, body))
        } else {
            // Exists A0 (λA0. Exists A1 (λA1. … body)) — nest right-to-left.
            let mut acc = body;
            for ty in sorts.into_iter().rev() {
                let lam = Term::lam(ty.clone(), acc);
                acc = Term::apps(Term::cnst("exists"), [ty, lam]);
            }
            Ok(acc)
        }
    }
}

/// A monomorphization site: a parametric datatype `head` applied to the
/// concrete argument S-exprs `args` (`(List Tree)` → `{head:"List",
/// args:[Tree]}`). Its [`mangle`]d name is the fresh kernel member's name.
#[derive(Clone)]
struct MonoSite {
    head: String,
    args: Vec<Sexpr>,
}

/// The monomorphization driver: a **bounded, dedup'd worklist** of container
/// specializations plus the set of all group-member names (output datatypes +
/// every reached specialization). Drives [`Elaborator::admit_datatypes`] to
/// saturation; on budget overflow the whole declaration is rejected.
struct Mono {
    /// Names already claimed as group members (output datatypes + mangled
    /// specialization names) — used both for resolution (`is_member`) and to
    /// dedup the worklist (a site is enqueued at most once).
    members: std::collections::HashSet<String>,
    /// Pending specializations to process. Pushed when first reached, popped to
    /// saturation; `members` already contains every pushed/processed name.
    queue: Vec<MonoSite>,
    /// How many specializations have been enqueued (the budget counter — never
    /// reset, so a non-saturating nesting trips it).
    count: usize,
}

impl Mono {
    /// A fresh driver seeded with the output datatype names (the arity-0
    /// members of this declaration), which are in scope in every constructor.
    fn new(output_names: Vec<String>) -> Self {
        Mono {
            members: output_names.into_iter().collect(),
            queue: Vec::new(),
            count: 0,
        }
    }

    /// Whether `name` is a group member (an output datatype or a specialization
    /// already named) — resolved to `cnst(name)` directly, no enqueue.
    fn is_member(&self, name: &str) -> bool {
        self.members.contains(name)
    }

    /// Reach a specialization `head(args)`: return its canonical mangled name,
    /// enqueueing it (once) if first seen. Rejects the declaration (sound by
    /// omission) on a non-regular nesting — either via the **argument-shape
    /// depth** cap (checked *first*, before the potentially-huge mangle, so an
    /// exponentially-deepening site can't blow up) or the **count** budget.
    fn enqueue(&mut self, head: String, args: Vec<Sexpr>) -> Result<String, FaceError> {
        // depth guard FIRST: a non-regular nesting deepens (and can double in
        // size) per level, so cap the shape depth before doing any O(size) work.
        let depth = args.iter().map(sexpr_depth).max().unwrap_or(0) + 1;
        if depth > MONO_MAX_SITE_DEPTH {
            return Err(unsupported(format!(
                "datatype monomorphization did not saturate: container-application nesting \
                 at `{head}` exceeds depth {MONO_MAX_SITE_DEPTH} (polymorphic-recursive / \
                 non-regular nesting)"
            )));
        }
        let name = mangle(&head, &args);
        if self.members.insert(name.clone()) {
            // a genuinely new specialization.
            self.count += 1;
            if self.count > MONO_BUDGET {
                return Err(unsupported(format!(
                    "datatype monomorphization did not saturate within {MONO_BUDGET} \
                     specializations (polymorphic-recursive / non-regular nesting at `{name}`)"
                )));
            }
            self.queue.push(MonoSite { head, args });
        }
        Ok(name)
    }

    /// The next pending specialization, if any.
    fn pop(&mut self) -> Option<MonoSite> {
        self.queue.pop()
    }
}

/// The canonical mangled name of a container application:
/// `mangle(F a₁ … aₙ) = F ++ "#" ++ map(mangle, args).join("#")`, where an atom
/// mangles to itself and a nested application recurses. `(List Tree)` →
/// `List#Tree`; `(List (List Tree))` → `List#List#Tree`.
///
/// The `#` sigil is *not* a standard SMT-LIB simple-symbol character (it is
/// reserved for `#b`/`#x` literal prefixes), so for well-formed standard input a
/// mangled name never collides with a user symbol — and because every head's
/// parametric-vs-sort role is fixed per program, this scheme is injective on
/// such input. A user *can* still smuggle a `#` in via a `|quoted|` symbol; that
/// is **not** a soundness hole — every member is emitted through the kernel's
/// checked `declare_mutual`, whose `DuplicateConst` gate refuses any collision as
/// a clean [`FaceError::Kernel`] (see the `slice3a_mangle_collision_*` test),
/// never a trusted ill-typed term.
fn mangle(head: &str, args: &[Sexpr]) -> String {
    let mut s = head.to_string();
    for a in args {
        s.push('#');
        s.push_str(&mangle_sexpr(a));
    }
    s
}

/// The mangled form of one argument S-expr (an atom verbatim, an application
/// `(F a …)` recursively mangled).
fn mangle_sexpr(s: &Sexpr) -> String {
    match s {
        Sexpr::Atom(a) => a.clone(),
        Sexpr::List(xs) => {
            let head = xs.first().and_then(Sexpr::as_atom).unwrap_or("");
            mangle(head, &xs[1..])
        }
    }
}

/// The nesting depth of an S-expr argument shape: an atom is depth 0, a list is
/// `1 + max(child depths)`. Bounds a monomorphization site so a non-regular
/// nesting (whose argument shape deepens per level) is caught early.
fn sexpr_depth(s: &Sexpr) -> usize {
    match s {
        Sexpr::Atom(_) => 0,
        Sexpr::List(xs) => 1 + xs.iter().map(sexpr_depth).max().unwrap_or(0),
    }
}

/// Capture-free S-expression substitution: replace every `Atom(p)` for which
/// `subst[p]` is set with that argument S-expr, recursing into lists. (Datatype
/// type-parameters are simple atoms with no binders inside the constructor
/// field sorts, so a plain structural replacement is correct.)
fn subst_sexpr(s: &Sexpr, subst: &HashMap<&str, &Sexpr>) -> Sexpr {
    match s {
        Sexpr::Atom(a) => match subst.get(a.as_str()) {
            Some(&replacement) => replacement.clone(),
            None => s.clone(),
        },
        Sexpr::List(xs) => Sexpr::List(xs.iter().map(|x| subst_sexpr(x, subst)).collect()),
    }
}

/// `λ tele[0]. … λ tele[m-1]. body` — the λ analogue of `build_pi`.
fn build_lam(tele: &[Term], body: Term) -> Term {
    tele.iter().rev().fold(body, |acc, dom| Term::lam(dom.clone(), acc))
}

/// Right-fold a list of `Prop`s under the binary `and`: `[]` → `true`, a
/// singleton → itself, else `and c₀ (and c₁ …)`.
fn and_chain(mut cs: Vec<Term>) -> Term {
    match cs.len() {
        0 => Term::cnst("true"),
        1 => cs.pop().unwrap(),
        _ => {
            let last = cs.pop().unwrap();
            cs.into_iter().rev().fold(last, |acc, c| Term::apps(Term::cnst("and"), [c, acc]))
        }
    }
}

/// The kernel context (binder *sorts*, innermost last) from the named context.
fn kernel_ctx(ctx: &[(String, Term)]) -> Ctx {
    ctx.iter().map(|(_, t)| t.clone()).collect()
}

/// Whether a declared type is exactly `Type(0)` (i.e. the decl is a sort).
fn is_type0(ty: &Term) -> bool {
    matches!(ty.kind(), adsmt_ir::TermKind::Sort(Univ::Type(0)))
}

/// Whether `sort` is (definitionally) the `Int` sort.
fn is_int(env: &Env, sort: &Term) -> bool {
    is_def_eq(env, sort, &Term::cnst(adsmt_ir::theory::INT))
}

/// Whether `sort` is (definitionally) the `Real` sort.
fn is_real(env: &Env, sort: &Term) -> bool {
    is_def_eq(env, sort, &Term::cnst(adsmt_ir::theory::REAL))
}

/// Left-associative n-ary fold of a binary operator `op` over `terms`
/// (`op(op(t0, t1), t2)…`); a single term is returned unchanged. Panics on an
/// empty slice — callers guarantee ≥1.
fn fold_left(terms: &[Term], op: &str) -> Term {
    let mut it = terms.iter().cloned();
    let mut acc = it.next().expect("fold_left: ≥1 term");
    for t in it {
        acc = Term::apps(Term::cnst(op), [acc, t]);
    }
    acc
}

/// The canonical decimal spelling of an SMT-LIB integer numeral (leading zeros
/// stripped, `"0"` preserved), or `None` if `s` is not an all-digit numeral.
fn canonical_int(s: &str) -> Option<String> {
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let t = s.trim_start_matches('0');
    Some(if t.is_empty() { "0".to_string() } else { t.to_string() })
}

/// The canonical spelling of an SMT-LIB decimal `<digits>.<digits>` (integer
/// part: leading zeros stripped; fractional part: trailing zeros stripped, each
/// keeping ≥1 digit), or `None` if `s` is not a decimal.
fn canonical_real(s: &str) -> Option<String> {
    let (i, f) = s.split_once('.')?;
    if i.is_empty()
        || f.is_empty()
        || !i.bytes().all(|b| b.is_ascii_digit())
        || !f.bytes().all(|b| b.is_ascii_digit())
    {
        return None;
    }
    let ci = i.trim_start_matches('0');
    let cf = f.trim_end_matches('0');
    Some(format!(
        "{}.{}",
        if ci.is_empty() { "0" } else { ci },
        if cf.is_empty() { "0" } else { cf },
    ))
}

/// The `i`-th element of `xs` as a symbol, for command `what`.
fn sym<'a>(xs: &'a [Sexpr], i: usize, what: &str) -> Result<&'a str, FaceError> {
    xs.get(i)
        .and_then(Sexpr::as_atom)
        .ok_or_else(|| unsupported(format!("{what}: expected a symbol at position {i}")))
}

/// Exactly one argument, for unary form `what`.
fn one<'a>(args: &'a [Sexpr], what: &str) -> Result<&'a Sexpr, FaceError> {
    match args {
        [a] => Ok(a),
        _ => Err(unsupported(format!("`{what}` expects exactly one argument"))),
    }
}
