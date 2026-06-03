# adsmt SMT-LIB / lu-kb dialect policy

**Status**: **v0.23 phase 1 freeze candidate** (v1.0 RC
pre-commit). Per `lsp_roadmap.md` phase 1 / task 23A.2. The
parser surface enumerated below is intended as the v1.0.0
dialect; any addition / removal / shape change after v0.23
sign-off requires either a deliberate v1.x major bump or a
re-opening of the freeze decision.

## SMT-LIB v2 commands (frozen surface)

The parser entry points are:

- `parse_smtlib(&str) -> Result<Vec<Command>, SmtLibError>`
- `parse_smtlib_positioned(&str) -> Result<Vec<(Command, Position)>, SmtLibError>`

`Command` enum (`src/smtlib.rs`) — 21 frozen variants. Adding
new variants in v1.x minor bumps is allowed; removing or
renaming variants requires a major bump.

| Variant | Form |
|---|---|
| `SetLogic` | `(set-logic <name>)` |
| `SetOption` | `(set-option :<keyword> <value>)` |
| `SetInfo` | `(set-info :<keyword> <value>)` |
| `DeclareSort` | `(declare-sort <name> <arity>)` |
| `DeclareDatatype` | `(declare-datatype <name> ((<ctor>) ...))` (nullary ctors v0.3+) |
| `DeclareConst` | `(declare-const <name> <sort>)` |
| `DeclareFun` | `(declare-fun <name> (<param-sort>...) <result-sort>)` |
| `DefineFun` | `(define-fun <name> ((<param> <sort>)...) <result-sort> <body>)` |
| `Assert` | `(assert <formula>)` |
| `CheckSat` | `(check-sat)` |
| `CheckSatAssuming` | `(check-sat-assuming (<lit>...))` |
| `GetModel` | `(get-model)` |
| `GetUnsatCore` | `(get-unsat-core)` |
| `GetProof` | `(get-proof)` |
| `Push` | `(push <n>)` |
| `Pop` | `(pop <n>)` |
| `Reset` | `(reset)` |
| `ResetAssertions` | `(reset-assertions)` |
| `Exit` | `(exit)` |
| `Echo` | `(echo "<string>")` — SMT-LIB v2.6 § 4.2.4; verbatim line to stdout |
| `Raw` | escape hatch for adsmt-specific dialect + unrecognised standard commands |

### Error surface

`SmtLibError`:
- `Parse(ParseError)` — S-expression structural failure.
- `NotACommand(String)` — top-level non-list.
- `UnknownCommand(String)` — recognised structure but unknown keyword.
- `Malformed { cmd, message }` — recognised keyword but
  arity / shape mismatch.

These four shapes are frozen; new variants additive only.

## lu-kb surface (frozen via lu-common submodule)

The lu-kb language is parsed by `lu_common::kb::parse` and its
AST shapes live in `lu_common::kb::ast`. Phase 1 freeze applies
transitively — any kb syntax change between v0.23 and v1.0
must follow the immediate-sync rule
(`logicutils_version_rule.md` §2) AND get its own freeze entry
here.

Frozen top-level forms (`Item` enum):
- `kind <name> <expr>` declarations
- `fn <name>(<args>) [: <ret>] = <body>` declarations
- `relation <name> { <members> }` blocks
- `instance <name> { <members> }` blocks
- `axiom <name>: <body>` declarations
- `rule <name>: <pattern> => <conclusion>` declarations
- `directive <name>(<args>)`

Frozen expression forms (`Expr` enum + `BodyExpr` enum +
`TypeExpr` enum + `KindExpr` enum): see
`external/logicutils/lu-common/src/kb/ast.rs`. The lu-kb AST is
the v1.0 kb surface; the v1.0 absorption (`21E.2` option 2-A')
relocates the source path but does not change the AST.

## Classical-axiom marker syntax (frozen via adsmt-cert)

Per `prover_emit_policy.md` § "Classical axiom imports
(on-demand)". The two markers — `should_import_classical` and
`allow_to_import_classical` — plus the `(lazy, scan)` truth
table arms + the closed-enum `StepPattern` + the hierarchical
classical-module family enum + the four-layer additive
attachment + the parent-inheritance rule are all considered
**phase 1 frozen surface** for v1.0.

Adding new classical modules (e.g. `Classical.Strong` /
`Classical.Choice.Hilbert` etc.) to the family enum is allowed
in v1.x minor bumps (additive). Changing the truth table arms
or the attachment-layer count requires a major bump.

## Pre-publication checklist (v1.0 entry)

Phase 1 (v0.23) freeze candidate sign-off status:

1. **Command variant audit** — ✅ enforced by
   `tests/dialect_surface.rs::command_variant_set_is_frozen`.
2. **Round-trip smoke** — ✅ existing parser tests cover the
   21 variants over ~50 SMT-LIB snippets.
3. **lu-kb AST audit** — pending. The audit cross-walks
   `lu-common/src/kb/ast.rs` enum cardinalities against this
   document.
4. **Classical-marker policy audit** — ✅ already pinned by
   `adsmt-cert`'s canonical AST tests + `prover_emit_policy.md`
   alignment.
5. **`#![breaking_changes_semver("1.0.0")]`** — ✅ promoted to
   a real outer attribute on `_BREAKING_MARKER_1_0_0` in
   `adsmt-parser/src/lib.rs` by v1.0.0-rc.1 RC1.3.
6. **Error message stability** — TBD; phase 2 (LSP) will start
   surfacing these errors to users so wording becomes
   user-facing.

Sign-off threshold: items 1, 2, 4 mandatory for phase 1;
items 3, 5, 6 mandatory for phase 3 RC.

## How to amend this document

- Additive changes (new Command variant, new lu-kb form, new
  classical-module family entry): append below the relevant
  table with a `[since vX.Y]` annotation; no freeze
  re-opening required.
- Subtractive or shape-changing edits: out of scope for v0.x →
  v1.0 transition. Stage them as v2.x candidates in a
  separate post-merge audit.
