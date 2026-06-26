//! The advisory **unsoundness / vacuity linter** for the typed-ASP face — a
//! pure OBSERVER behind the soundness firewall (it is the exact dual of the
//! abductive surface: abduction finds hypotheses that *make* a goal hold; the
//! linter finds when the existing program is self-defeating). It reads only the
//! already-trusted outputs of the `elaborate → solve` pipeline and emits
//! side-channel [`AspDiagnostic`]s; it has **no write path to a verdict**, so a
//! lint bug can only ever yield a missing or spurious advisory line, never a
//! flipped answer set. A driver runs it *alongside* (not instead of) `solve`,
//! default-off.
//!
//! MVP rules — all [`Severity::Info`] (advisory): intentional vacuity
//! (`requires false`-style dead branches, over-tight constraints) is common, so
//! the keystone is a soft note, never a hard "your program is broken" claim.
//!
//! - **`asp-unsafe`** — an unsafe variable (the elaborator's
//!   [`FaceError::Unsafe`](crate::FaceError::Unsafe), surfaced as a diagnostic):
//!   a head / `not` / comparison variable not bound by a positive body atom
//!   makes grounding silently drop instances (soundness-fatal — the elaborator
//!   already refuses it; this explains *why*).
//! - **`asp-nonstratified`** — a negative cycle: the program is decided by the
//!   L3 stable-model gate, not the perfect model (an FYI on the semantics).
//! - **`asp-vacuity`** — the dual of the SMT-LIB face's vacuous-context lint:
//!   the program has **no answer set** ([`Solution::consistent`] is `false`); an
//!   integrity constraint or an odd negative loop eliminated every candidate.

use crate::ast::Program;
use crate::elab::{Stratification, elaborate};
use crate::error::FaceError;
use crate::solve::solve;

/// Diagnostic severity. The MVP rules are all `Info` (advisory); `Warning` is
/// reserved for a future opt-in `--strict` tier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Info,
    Warning,
}

/// A 1-based source location (line, column) for an editor squiggle. Populated by
/// [`lint_source`] (which has the source text + the parser's span side-channel);
/// `None` from [`lint`] (which is handed a span-free [`Program`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceLoc {
    pub line: u32,
    pub column: u32,
}

/// One advisory lint finding. `rule` is a stable identifier (e.g. `"asp-vacuity"`)
/// so a downstream LSP / CI consumer can filter by rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AspDiagnostic {
    pub severity: Severity,
    pub rule: &'static str,
    pub message: String,
    /// The source location, when known (see [`lint_source`]).
    pub source_loc: Option<SourceLoc>,
}

impl AspDiagnostic {
    fn info(rule: &'static str, message: impl Into<String>) -> Self {
        AspDiagnostic { severity: Severity::Info, rule, message: message.into(), source_loc: None }
    }
}

/// Lint a typed-ASP program: an ADVISORY pass over the trusted
/// `elaborate → solve` pipeline that reports unsoundness-hygiene observations.
/// It **never changes a verdict** — a caller uses the diagnostics alongside the
/// real [`solve`] result (a real driver would reuse an existing [`Solution`]
/// rather than re-solving here).
pub fn lint(program: &Program) -> Vec<AspDiagnostic> {
    let mut out = Vec::new();

    let elab = match elaborate(program) {
        Ok(e) => e,
        // an UNSAFE variable is surfaced as a diagnostic (the elaborator stops at
        // the first occurrence; this pre-flights it). Other errors (Parse /
        // Kernel / Unsupported) are not unsoundness lints — stay silent.
        Err(FaceError::Unsafe(m)) => {
            out.push(AspDiagnostic::info(
                "asp-unsafe",
                format!(
                    "unsafe variable — {m}; a variable not bound by a positive body atom makes \
                     grounding drop instances (soundness-fatal, so the elaborator refuses it)"
                ),
            ));
            return out;
        }
        Err(_) => return out,
    };

    // asp-nonstratified: a negative cycle is decided by the L3 stable-model gate.
    if let Stratification::NonStratified(reason) = &elab.stratify {
        out.push(AspDiagnostic::info(
            "asp-nonstratified",
            format!(
                "negative cycle — {reason}; decided by stable-model semantics (the L3 gate), \
                 not the perfect model"
            ),
        ));
    }

    // asp-vacuity (the dual of LINT-VAC): no answer set. Info/soft — vacuity (an
    // over-tight constraint, an odd loop, an unreachable design) is often
    // intentional, so this is a neutral note, never a hard defect claim. A
    // solving abstain (Err) makes no vacuity claim.
    if let Ok(sol) = solve(&elab)
        && !sol.consistent
    {
        out.push(AspDiagnostic::info(
            "asp-vacuity",
            "no answer set — the facts, rules, and integrity constraints admit no model; \
             if a model was expected, a constraint or a negative cycle eliminated every candidate",
        ));
    }

    out
}

/// Lint a typed-ASP **source string** — like [`lint`], but with **precise source
/// locations** (an IDE squiggle). It parses with the span side-channel
/// ([`crate::parser::parse_with_spans`]) and attaches a [`SourceLoc`] to each
/// per-item finding (currently `asp-unsafe`, which points at the offending rule;
/// the whole-program `asp-nonstratified` / `asp-vacuity` notes stay file-level).
/// A parse error is not an unsoundness lint, so it yields no diagnostics.
pub fn lint_source(src: &str) -> Vec<AspDiagnostic> {
    let (program, spans) = match crate::parser::parse_with_spans(src) {
        Ok(ps) => ps,
        Err(_) => return Vec::new(),
    };
    let mut out = lint(&program);
    for d in &mut out {
        // attach a precise location to the per-item findings.
        if d.rule == "asp-unsafe"
            && let Some(byte) = unsafe_item_offset(&program, &spans)
        {
            d.source_loc = Some(line_col(src, byte));
        }
    }
    out
}

/// The source byte offset of the rule/constraint that triggers `FaceError::Unsafe`.
/// The elaborator reports the FIRST error in item order, so the **smallest
/// prefix that fails to elaborate** isolates the offending item (everything
/// before it elaborated cleanly). `O(n²)` re-elaborations, but the linter is cold
/// and `asp-unsafe` is rare.
fn unsafe_item_offset(program: &Program, spans: &[usize]) -> Option<usize> {
    for i in 1..=program.items.len() {
        let prefix = Program { items: program.items[..i].to_vec() };
        if elaborate(&prefix).is_err() {
            return spans.get(i - 1).copied();
        }
    }
    None
}

/// Map a byte offset into `src` to a 1-based (line, column) — counting columns
/// in `char`s so multi-byte UTF-8 stays correctly positioned.
fn line_col(src: &str, byte: usize) -> SourceLoc {
    let byte = byte.min(src.len());
    let (mut line, mut column) = (1u32, 1u32);
    for (i, ch) in src.char_indices() {
        if i >= byte {
            break;
        }
        if ch == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    SourceLoc { line, column }
}
