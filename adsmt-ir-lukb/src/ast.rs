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
    /// `fn f(x: Int, y z: Bool): U [= body]` — a function. With **no** `= body`
    /// it is an opaque (`open`) **signature** postulated as `f : T1 -> … -> U`
    /// (`Bool` → `Prop`); with a `= body` it is a **non-recursive definition**
    /// (`define`, `Modality::Def`) — `f := λ(params). body`, δ-unfolded at the
    /// solver lowering. (A *recursive* body — one mentioning `f` — needs the
    /// kernel `fix`; a later slice.) Each parameter group `names: ty` shares a
    /// type.
    Fn { name: String, params: Vec<(Vec<String>, Type)>, ret: Type, body: Option<Term> },
    /// `data Nat = zero | succ(Nat)` / `data List = nil | cons(head: Int, tail:
    /// List)` — a non-parametric inductive **datatype**, elaborated to a kernel
    /// `declare_inductive`. Each constructor carries its field list; a field may
    /// name its selector (`head: Int`) or be positional (`Int`) — the selector
    /// names are surface sugar (round-tripped; the kernel + solver lowering
    /// synthesize positional selectors). Constructors are usable as terms; case
    /// analysis (`match`) is a later surface slice.
    Data { name: String, ctors: Vec<Ctor> },
    /// `axiom [name]: φ` — a trusted hypothesis (∈ H).
    Axiom(Option<String>, Term),
    /// `assume [name]: φ` — a VC path condition (∈ H).
    Assume(Option<String>, Term),
    /// `goal [name]: φ` — the obligation. The body may be a sequent
    /// `H1, …, Hk |- G`, desugared at parse time to `(H1 ∧ … ∧ Hk) ==> G`.
    Goal(Option<String>, Term),
}

/// One datatype constructor: its name + field list (each field = an optional
/// selector name and a type) — the payload of a [`Item::Data`].
pub type Ctor = (String, Vec<(Option<String>, Type)>);

/// A type expression: a named sort, a parametric application, or a refinement
/// type carving a base sort down by a predicate.
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// `Int`, `Real`, `Bool`, `Nat`, `WNat`, or a declared sort `S`.
    Name(String),
    /// `F(T, …)` — a parametric/theory sort (a later slice; carried for
    /// round-tripping).
    App(String, Vec<Type>),
    /// `{v: T | φ}` — a **refinement type**: the base sort `T` carved down to
    /// the values `v` satisfying the predicate `φ` (over `v`). In a `const`
    /// type it postulates the value plus the trusted fact `φ`; in a `fn`
    /// signature the predicate `φ` may mention **generic predicate parameters**
    /// `'p` (predicate-polymorphic — bound implicitly at the `fn`, see
    /// [`crate::lexer::is_tick_ident`]). The proof is `Prop`-irrelevant +
    /// lowering-erased; the type's *sort* is just `T`.
    Refine { var: String, base: Box<Type>, pred: Box<Term> },
    /// `T -> U` — a **function type** (right-associative). A *refined* arrow
    /// `{u:A|'p} -> {v:A|'q}` carries the precondition `'p` on its domain and
    /// the postcondition `'q` on its codomain; the type's *value sort* is the
    /// plain `A -> A` (refinements `Prop`-irrelevant + lowering-erased), and an
    /// argument supplied at this type provides its postcondition as a usable
    /// fact (see `docs/design/SOLVE_BY_PROOF_TERMS.md` §2).
    Arrow(Box<Type>, Box<Type>),
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
    /// `Some(φ)` for a **refinement-type** binder `{names : T | φ}` — a general
    /// domain restriction by an arbitrary predicate `φ` (over each name), the
    /// generalisation of `constraint` (a single comparison `(n:T) op rhs` is the
    /// special case `{n:T | n op rhs}`). Elaborated identically: `∀ → ⟹`,
    /// `∃ → ∧` (the pre-verified relativization guard).
    pub refinement: Option<Box<Term>>,
    /// `Some((e, c))` for an **image binder** `{y = e | c}` — a heavily
    /// type-inference-driven abbreviation. `names = [y]` is the *image* var, `e`
    /// (of the form `f(x)`) the image expression, and `c` the constraint on the
    /// *preimage* `x`. It desugars to `∀ x:{dom(f) | c}. body[y := e]` — the
    /// quantifier ranges over the inferred preimage `x` (type = `f`'s domain),
    /// guarded by `c`, with `y` unfolded to `e` in the body. See
    /// `docs/design/SOLVE_BY_PROOF_TERMS.md` §5 (pre-verified `image_quantifier_desugar`).
    pub image: Option<(Box<Term>, Box<Term>)>,
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
    /// `solve G by L` — an in-language **proof term** of the proposition `G`,
    /// justified by the lemma `L` (the structured-proof *cut*). `G` and `L` are
    /// each a block (a term, possibly a `let`-chain). Elaborates (semantics B) to
    /// the leaf obligation `L` + the bridge obligation `L ⟹ G`, both closed over
    /// the ambient context and emitted as goals, with the value a proof of `G`.
    /// See `docs/design/SOLVE_BY_PROOF_TERMS.md`.
    SolveBy(Box<Term>, Box<Term>),
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
