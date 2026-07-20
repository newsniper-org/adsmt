//! The MVP abstract syntax — the **ASP fragment of the lu-kb-successor surface**
//! (decision B). The current `adsmt-parser-lu-kb` grammar is close but its
//! `FactBlock` is specialized to `target -> dep` build-dependency pairs; the
//! successor generalizes facts to arbitrary typed predicate atoms. The
//! `Predicate` / `RuleDecl` / body shapes carry over (lu-kb's
//! `BodyExpr::Condition(Expr)` maps to [`Literal::Theory`]). A parser slice
//! (evolving lu-kb's lexer/parser) will produce this AST; the elaborator is
//! built against it directly, so it is testable from hand-built programs.
//!
//! This is the L0–L2 subset: definite Datalog (L0); the **theory interior**
//! (L1) — `open` comparison atoms in rule bodies, including **CanEq** typed
//! (dis)equality (`=`/`!=` routed by the operand sort: arithmetic on `Int`,
//! structural equality on enums/datatypes); and **stratified negation-as-failure**
//! (L2) — `not p` body literals ([`Literal::Neg`]), sound under the elaborator's
//! stratification check. Choice and aggregates grow this AST in later slices.

/// A typed-ASP program: a sequence of items.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub items: Vec<Item>,
}

/// A top-level item.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Item {
    /// `sort S.` — an uninterpreted domain (`open S : Type(0)`).
    Sort(String),
    /// `enum Color = { Red, Green, Blue }.` — a finite, closed domain.
    Enum(EnumDef),
    /// `data Tree = leaf | node(Tree, Int, Tree).` — an inductive datatype with
    /// argument-bearing constructors (the kernel's strict-positivity gate
    /// re-checks). Constructors are usable as terms / patterns in atoms.
    Data(DataDef),
    /// `pred edge(Node, Node).` — a typed relation. Argument sorts may be
    /// declared sorts/enums or the built-in `Int`.
    Pred(PredDecl),
    /// `edge(a, b).` — a ground fact.
    Fact(Atom),
    /// `reach(X, Z) :- reach(X, Y), edge(Y, Z).` — a definite rule.
    Rule(Rule),
    /// `?- reach(a, X).` — a (deductive) query.
    Query(Atom),
    /// `abducible needs_rebuild(File).` — declare a predicate **abducible**: its
    /// ground atoms are the hypothesis space (an `Open` atom with *no*
    /// completion clause forcing it false — the dual of a `def` atom).
    Abducible(PredDecl),
    /// `?- abduce rebuild("main.o").` — an abductive query: the ⊆-minimal sets
    /// of abducible atoms that, assumed, make the (ground) goal hold.
    Abduce(Atom),
    /// `:- B.` — an **integrity constraint**: the body `B` must *not* hold in the
    /// least model; if any ground instance does, the program is inconsistent (no
    /// answer set). A headless rule.
    Constraint(Vec<Literal>),
    /// `:~ B. [weight@level]` — a **weak constraint** (L5 first slice): unlike
    /// [`Item::Constraint`], a ground instance whose body `B` holds does *not*
    /// make the program inconsistent — it costs `weight` at optimization
    /// `level` (default `0`). The optimal answer set(s) are the ones minimizing
    /// the summed cost. Same body grammar/safety as an integrity constraint
    /// (typechecked identically — see `elab::Elaborator::check_constraint_body`).
    /// **Single-level only** this slice: a program mixing more than one
    /// distinct `level` value across its weak constraints is refused at solve
    /// time (see `solve::solve_weak_optimal`) — full lexicographic
    /// multi-level stratification is a deferred follow-up.
    WeakConstraint { body: Vec<Literal>, weight: WeightLit, level: i64 },
}

/// A weak-constraint weight literal. **Integer only this slice** — the lexer
/// has no rational/decimal numeral syntax to reuse yet (only `TokKind::Int`),
/// so `[1.5@0]`-style rational weights are a clean parse error, not a silent
/// truncation. Kept as a distinct type (rather than a bare `i64`) so a later
/// slice can add a `Rational` variant without touching every call site.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WeightLit {
    pub value: i64,
}

/// `enum Name = { C0, C1, … }` — nullary, mutually-disjoint constructors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumDef {
    pub name: String,
    pub ctors: Vec<String>,
}

/// `data Name = c0(S, …) | c1 | …` — an inductive datatype.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataDef {
    pub name: String,
    pub ctors: Vec<Ctor>,
}

/// A datatype constructor `c(arg_sort, …)` (nullary if `arg_sorts` is empty).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ctor {
    pub name: String,
    pub arg_sorts: Vec<String>,
}

/// `pred name(Sort0, Sort1, …)` — argument sorts by name (the result is `Prop`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PredDecl {
    pub name: String,
    pub arg_sorts: Vec<String>,
}

/// An atom `pred(arg0, arg1, …)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Atom {
    pub pred: String,
    pub args: Vec<Term>,
}

/// A first-order term in an atom: a variable, an object constant / enum
/// constructor, or an integer literal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// A variable (rule-universally quantified over its rule).
    Var(String),
    /// A constant: an object constant (auto-declared at its use sort) or a
    /// nullary constructor.
    Const(String),
    /// An integer literal (sort `Int`).
    Int(i64),
    /// A constructor application `c(t0, t1, …)` — a *ground term* if it contains
    /// no variables, otherwise a **pattern** (the first-order matching surface).
    App(String, Vec<Term>),
}

/// A definite rule `head :- body…`. The body is a conjunction of positive
/// `def`-atoms and `open` theory atoms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    pub head: Atom,
    pub body: Vec<Literal>,
}

/// A rule-body literal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    /// A positive `def` atom `p(args…)`.
    Pos(Atom),
    /// A **negation-as-failure** literal `not p(args…)` — the L2 rung. Holds in
    /// the perfect model iff `p(args…)` is *not* derivable. Only sound under
    /// **stratification** (no predicate depends on its own negation); the
    /// elaborator rejects a negative cycle, and the solver evaluates strata
    /// bottom-up so a `not` always reads an already-decided lower stratum.
    Neg(Atom),
    /// An `open` comparison `{ lhs op rhs }` — the L1 theory interior. For
    /// `Int`-sorted operands it is an arithmetic comparison; for any other sort
    /// the only operators are `=` / `!=`, routed by **CanEq** to that sort's
    /// equality (the cross-sort `Int = Node` mistake is an elaboration error,
    /// not a silent atom). Its variables must be bound by a positive body atom
    /// (range restriction), so after grounding it is a ground guard.
    Theory(Theory),
}

/// A comparison `lhs op rhs`. The operand sorts are inferred at elaboration; the
/// operator is checked against the (shared) operand sort — all six on `Int`,
/// only `=`/`!=` elsewhere.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Theory {
    pub op: CmpOp,
    pub lhs: Expr,
    pub rhs: Expr,
}

/// A comparison operator. `Lt`/`Le`/`Gt`/`Ge` are `Int`-only; `Eq`/`Ne` route
/// via **CanEq** to the operand sort's equality (arithmetic on `Int`, structural
/// (dis)equality on enums/datatypes).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    Lt,
    Le,
    Eq,
    Ne,
    Gt,
    Ge,
}

/// A comparison **operand**: an arithmetic expression over `Int` (`Lit`/`Add`/
/// `Sub`/`Mul`) *or* a first-order term (`Var`/`Const`/`App`). The two coincide
/// on a bare variable (`{ X = Y }` is `Int` equality or term equality depending
/// on `X`'s inferred sort) — the elaborator's CanEq pass resolves which, so the
/// surface needs no syntactic split.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// An integer literal (sort `Int`).
    Lit(i64),
    /// A variable — its sort is whatever a positive body atom bound it to.
    Var(String),
    /// A constant: an object constant or a nullary constructor (its sort is the
    /// constructor's / the constant's declared sort).
    Const(String),
    /// A constructor application `c(e0, e1, …)` — a datatype/enum term operand
    /// for structural (dis)equality.
    App(String, Vec<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}
