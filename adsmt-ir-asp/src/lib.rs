//! # adsmt-ir-asp — the typed-ASP face for [`adsmt_ir`]
//!
//! The **closed-world / least-model / stable-model** sibling of the SMT-LIB
//! face (`adsmt-ir-smtlib`). A typed-ASP program (typed predicates over kernel
//! sorts/datatypes; `head :- body` rules; facts; abducibles; integrity
//! constraints) elaborates to the *same* typed CIC kernel ([`adsmt_ir`]) — the
//! kernel's `def` (closed-world) vs `open` (classical/theory) modality is the
//! hook. Rules become `def` atoms; SMT theory atoms are `open`; they cooperate.
//!
//! This crate is a **frontend, not the trusted core**: everything it elaborates
//! is re-checked by the kernel admitters, and every claimed answer is
//! independently re-verified by recomputing the least-fixpoint, so a face/solver
//! bug can only ever yield a [`FaceError`] or `Unknown` — never a trusted
//! ill-typed term or a manufactured entailment. See `DESIGN.md` for the full
//! design (the negation ladder, the abductive merge, and the closed-world
//! generate-and-check firewall).
//!
//! ## Status — L0–L2 landed; L3 first slice (bounded stable models)
//!
//! The runtime core is [`GroundProgram`]'s **forward Horn least-fixpoint
//! evaluator** ([`program`]) — the solver for the definite fragment, the answer
//! re-check gate, and the abductive forward-chainer in one. On top of it the
//! face now covers, end to end (surface → checked kernel → finite grounder →
//! `lfp`/perfect model → answer):
//!
//! - **L0** — typed sorts / enums / datatypes / predicates, facts, definite
//!   rules, ground + variable ("find-all") queries; first-order **datatype
//!   matching** (destructuring patterns over a subterm-closed term universe).
//! - **L1** — the **theory interior**: `open` integer comparisons in rule
//!   bodies, plus **CanEq** typed (dis)equality (`=`/`!=` routed by the operand
//!   sort: arithmetic on `Int`, structural equality on enums/datatypes).
//! - **L2** — **stratified negation-as-failure** (`not p`) over the perfect
//!   model, and **integrity constraints** `:- B`.
//! - **L3 (first slice)** — **stable-model semantics** for *non-stratified*
//!   programs (a negative cycle now elaborates and routes here instead of being
//!   refused): the [Gelfond–Lifschitz reduct] gate ([`GroundNProgram::is_stable`])
//!   — `M` is stable iff `least_model(reduct(P, M)) == M`, reusing the trusted
//!   `lfp` verbatim — driven by a **bounded guess-and-check** bracketed by the
//!   **well-founded model** `L* ⊆ M ⊆ U*` (van Gelder's alternating fixpoint of
//!   the antitone reduct least-model operator; `B \ U*` is the greatest unfounded
//!   set — the unfounded-set propagator, computed as a fixpoint). The well-founded
//!   bracket forces the maximal set of atoms in/out in polynomial time, so only
//!   the *undefined* atoms remain to guess — strictly tighter than the one-step
//!   reduct envelope (which is just the first fixpoint iteration), deciding more
//!   programs within budget. Over the work budget it still abstains loudly
//!   ([`FaceError::Unsupported`]); the **loop-formula certificate** + conflict
//!   learning (so programs whose *undefined* fragment also exceeds budget get a
//!   verdict, not an abstain) are the remaining full-L3 slice. Queries are
//!   answered **cautiously** (`∩` over the stable models); [`Solution::stable`]
//!   carries the answer sets.
//! - **Abduction** — `declare`-`abducible` / `?- abduce G`: the ⊆-minimal
//!   hypotheses that entail a goal (deduction = empty-abducible abduction), found
//!   by **native backward-SLD relevance grounding** (the abducibles reachable
//!   from the goal) re-verified by the forward gate. The goal may be ground
//!   (`?- abduce p(c)`) or carry variables (`?- abduce p(X)`, abduced per
//!   enumerated binding).
//! - **Surface sugar** — anonymous `_`; pooling `;` and integer intervals `..`
//!   that expand a whole fact / rule / constraint over their cartesian product;
//!   and body `let V = t` that names a subterm and substitutes it into the rule
//!   (all [`parse`]-time desugarings).
//! - **Advisory linter** ([`lint`] / [`lint_source`]) — a pure OBSERVER behind
//!   the firewall (no write path to a verdict) that pre-catches
//!   unsoundness-hygiene issues: an unsafe variable, a negative cycle
//!   (stable-model semantics), and **vacuity** (no answer set — the dual of the
//!   SMT-LIB face's vacuous-context lint). All `Info`/soft (intentional vacuity
//!   is common). [`lint_source`] adds **precise source locations** ([`SourceLoc`])
//!   for an IDE squiggle (via the parser's span side-channel,
//!   [`parse_with_spans`]). Default-off in a driver.
//!
//! Pending: the remaining full-L3 slice (a loop-formula certificate checker +
//! conflict learning, so the bounded guess-and-check over the *undefined* atoms
//! is replaced by a clasp-style search when even that fragment is large — the
//! well-founded unfounded-set propagation already landed); brave queries; choice
//! / disjunction (L4); aggregates + weak constraints (L5). See `DESIGN.md` for
//! the full ladder + build order.
//!
//! [Gelfond–Lifschitz reduct]: https://en.wikipedia.org/wiki/Stable_model_semantics

pub mod ast;
pub mod elab;
pub mod error;
pub mod lexer;
pub mod lint;
pub mod parser;
pub mod program;
pub mod solve;

pub use elab::{Elaborated, Stratification, elaborate};
pub use error::FaceError;
pub use lint::{AspDiagnostic, Severity, SourceLoc, lint, lint_source};
pub use parser::{parse, parse_with_spans};
pub use program::{Atom, GroundNProgram, GroundNRule, GroundProgram, GroundRule};
pub use solve::{AbduceAnswer, Entailment, QueryAnswer, Solution, StableModels, solve};
