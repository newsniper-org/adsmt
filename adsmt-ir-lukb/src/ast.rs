//! The lu-kb-successor **surface AST** — the span-free tree the parser
//! produces and the elaborator/printer consume. Deliberately small; the term
//! grammar is the centrepiece (the obligation items wrap it).

/// A complete module: a sequence of items.
#[derive(Clone, Debug, PartialEq)]
pub struct Module {
    pub items: Vec<Item>,
}

/// A top-level item.
#[derive(Clone, Debug, PartialEq)]
pub enum Item {
    /// `sort S` — an opaque (uninterpreted) sort.
    Sort(String),
    /// `const x: T` — a free constant (e.g. a VC variable).
    Const(String, Type),
    /// `fn f(x: Int, y z: Bool): U` — an (opaque) function **signature**,
    /// postulated as `f : T1 -> … -> U` (`Bool` → `Prop`). Each parameter group
    /// `names: ty` shares a type. Function *definitions* (`= body`) are a later
    /// slice (the closed-world modality contract).
    Fn { name: String, params: Vec<(Vec<String>, Type)>, ret: Type },
    /// `axiom [name]: φ` — a trusted hypothesis (∈ H).
    Axiom(Option<String>, Term),
    /// `assume [name]: φ` — a VC path condition (∈ H).
    Assume(Option<String>, Term),
    /// `goal [name]: φ` — the obligation. The body may be a sequent
    /// `H1, …, Hk |- G`, desugared at parse time to `(H1 ∧ … ∧ Hk) ==> G`.
    Goal(Option<String>, Term),
}

/// A type expression: a named sort or a parametric application.
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// `Int`, `Real`, `Bool`, `Nat`, `WNat`, or a declared sort `S`.
    Name(String),
    /// `F(T, …)` — a parametric/theory sort (a later slice; carried for
    /// round-tripping).
    App(String, Vec<Type>),
}

/// A binder group: one or more names sharing a type (`x y: Int`), optionally
/// carrying an inline **refinement constraint** that narrows the quantification
/// *domain* (`(n: Nat) > 5`, `(a b c: Nat) >= 2`). The constraint is a
/// typing-level concept — distinct from a body antecedent — and applies to
/// *each* name in the group (desugared to `name op rhs` guards at elaboration).
#[derive(Clone, Debug, PartialEq)]
pub struct Binder {
    pub names: Vec<String>,
    pub ty: Type,
    /// `Some((op, rhs))` for a parenthesised group with an inline constraint
    /// `(names: T) op rhs`; `None` for a plain binder.
    pub constraint: Option<(BinOp, Box<Term>)>,
    /// `Some((lo, hi))` for a **bounded range** binder `x in lo..hi` — sugar for
    /// `x: Int` with the domain guard `lo <= x and x < hi` (half-open). When
    /// present, `ty` is the implicit `Int` and `constraint` is `None`.
    pub range: Option<(Box<Term>, Box<Term>)>,
}

/// A term (proposition or value).
#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    /// A variable or 0-ary symbol.
    Var(String),
    /// An integer numeral (canonical decimal text).
    IntLit(String),
    /// A real/decimal numeral (canonical text).
    RealLit(String),
    /// `true` / `false`.
    Bool(bool),
    /// `not φ`.
    Not(Box<Term>),
    /// Unary minus `-x`.
    Neg(Box<Term>),
    /// An infix binary operation.
    Bin(BinOp, Box<Term>, Box<Term>),
    /// Application `f(a, …)`.
    Call(String, Vec<Term>),
    /// `forall <binders> . body <triggers>`. Each trigger is a multi-pattern
    /// (`trigger f(x)` → `[f(x)]`; `trigger { p1, p2 }` → `[p1, p2]`); a
    /// quantifier may carry several. Triggers are MBQI matching control — a
    /// surface/solver-layer annotation that the kernel `Π` cannot hold, so the
    /// elaborator carries them out-of-band (currently dropped; see [`crate::elab`]).
    Forall(Vec<Binder>, Box<Term>, Vec<Vec<Term>>),
    /// `exists <binders> . body <triggers>`.
    Exists(Vec<Binder>, Box<Term>, Vec<Vec<Term>>),
    /// `let x = e in body`.
    Let(String, Box<Term>, Box<Term>),
}

/// An infix binary operator (precedence is in the parser, not here).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    // logical
    Iff,     // <==>
    Implies, // ==>
    Or,      // or
    And,     // and
    // (dis)equality + comparison
    Eq, // =
    Ne, // !=
    Lt, // <
    Le, // <=
    Gt, // >
    Ge, // >=
    // arithmetic
    Add, // +
    Sub, // -
    Mul, // *
    Div, // /
}
