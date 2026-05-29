# adsmt-lints

Runtime audit library for adsmt certificate hygiene checks. Pure
stable Rust, no nightly toolchain or compiler-plugin dependencies.

## Why runtime, not compile-time?

The cert is a dynamic object built by the solver in response to
the SMT problem submitted. Compile-time tools (rustc, clippy,
cargo-dylint) have access to the source code where
[`PatternMarker`]s are *declared* but not to the cert they're
evaluated against. Dead-pattern detection — "did this declared
pattern match any step in the cert?" — fundamentally requires
both, and only runtime entities hold both.

Earlier scaffolds attempted a cargo-dylint plugin (cdylib +
`LateLintPass`) for this check. That approach was scrapped in
v0.18 because the cert-availability mismatch made the plugin
unable to actually answer the question. The runtime audit
library replaces it.

## What it does

```rust
use adsmt_cert::{CertBuilder, /* ... */};
use adsmt_lints::{dead_pattern_audit, audit_to_json};

let cert = build_cert_somehow();
let diagnostics = dead_pattern_audit(&cert);
for diag in &diagnostics {
    eprintln!("{}", diag.message);
}

// IDE-friendly JSON output
let json = audit_to_json(&cert).expect("serialise");
std::fs::write("audit.json", json).unwrap();
```

## Subjects (who calls this)

| Subject | When | How |
|---|---|---|
| Cert producer code | Right after building the cert | Call `dead_pattern_audit(&cert)` and `eprintln!` / log |
| Cert consumer / emitter | Inside `emit_lean / emit_rocq / emit_isabelle` (or sibling pre-emit step) | Same |
| Test code | In `#[test]` functions that exercise specific cert shapes | Assert `dead_pattern_audit(&cert).is_empty()` |
| Separate audit binary | E.g., `adsmt-cli audit foo.smt2` | `audit_to_json` and print to stdout |
| IDE extension | Out-of-band runner kicked by the editor | Spawn the audit binary, parse the JSON document |

## JSON schema

The JSON document version is `1`; bump on backwards-incompatible
additions and have consumers reject unknown versions.

```json
{
  "schema_version": 1,
  "generator": "adsmt-lints v0.18.0",
  "diagnostics": [
    {
      "marker_index": 2,
      "marker_name": "drat_marker",
      "severity": "warning",
      "message": "pattern marker #2 (`drat_marker`) matched 0 of 14 cert steps",
      "source_loc": { "line": 42, "column": 10 },
      "cert_step_count": 14,
      "steps_matched_by_siblings": [{ "id": 7 }, { "id": 11 }]
    }
  ]
}
```

Per-field notes:

- `marker_index` — zero-based index into the cert's
  `pattern_markers` array. Stable across the same audit run.
- `marker_name` — optional, copied from `PatternMarker.name`.
  When `null` the marker was declared without a label.
- `severity` — `"warning"` for v0.18 (only level used);
  `"info"` and `"error"` are reserved.
- `message` — preformatted, ready for direct display.
- `source_loc` — `null` when the marker was declared without
  position info; when present, holds `{ line, column }`.
  IDE extensions render this as a squiggle.
- `cert_step_count` — total steps in the cert; lets consumers
  confirm the cert wasn't trivially empty.
- `steps_matched_by_siblings` — steps that other markers
  matched. A non-empty list answers "why didn't mine match
  while others did?" at a glance.

## VS Code integration sketch

A minimal VS Code extension consumes this JSON as follows:

```jsonc
// package.json (snippet)
{
  "contributes": {
    "languages": [{ "id": "adsmt-audit-json", "extensions": [".audit.json"] }],
    "problemMatchers": [
      {
        "name": "adsmt-audit",
        "owner": "adsmt",
        "fileLocation": "absolute",
        "pattern": [{
          "regexp": "^.*\"line\":\\s*(\\d+).*\"column\":\\s*(\\d+).*\"message\":\\s*\"([^\"]+)\".*$",
          "line": 1, "column": 2, "message": 3
        }]
      }
    ]
  }
}
```

The richer route is a custom diagnostic provider that reads the
versioned document and emits `vscode.Diagnostic` entries
directly — left as an exercise for the extension author.

## Future audits

`adsmt-lints` is also intended to host runtime audits over
lu-kb usage patterns (dead-predicate detection over a parsed
`KbModule`, unused-rule detection, …). Those audits share the
same `Severity` / `DiagnosticsDocument` shape, so a single IDE
extension can consume both surfaces uniformly.
