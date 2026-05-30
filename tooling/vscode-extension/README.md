# adsmt Lints — VS Code extension

Renders dead-pattern diagnostics from the `adsmt-lints` JSON
audit document as VS Code Problems entries + editor squiggles,
and hosts the adsmt LSP client (v0.25 25EXT.1 split).

## Architecture (v0.25)

This extension is split along the editor-agnostic vs
VSCode-specific axis per `lsp_roadmap.md` phase 2 / task
25EXT.1:

- `src/audit.ts` — **editor-agnostic** JSON parsing + types
  for the `adsmt-lints` audit document. Reusable by any
  TypeScript editor integration.
- `src/extension.ts` — **VSCode-specific** glue: command
  palette wiring, `DiagnosticCollection` ↔ `audit.ts`
  conversion, file-watcher, and the LSP client that spawns
  the `adsmt-lsp` server binary (`adsmt-lints.lspBinary`
  setting points at the executable; defaults to `adsmt-lsp`
  on PATH).

## Usage

### One-shot load

1. Run `lu-smt --audit-json < your-script.smt2 2> audit.json`
   (or equivalent) to produce an audit JSON document.
2. Open the Command Palette (`Ctrl+Shift+P`) and run **adsmt:
   Load audit JSON**.
3. The extension prompts for a file path (defaulting to the
   configured `adsmt-lints.auditPath`), parses the document, and
   populates the Problems view.

### Auto-reload

Set `adsmt-lints.auditPath` to the JSON path your tooling
emits to, and the extension will watch the file and re-render
on every change. Useful for tight save-recompile-rerender
loops.

### Clearing

Run **adsmt: Clear lints diagnostics** to remove every
diagnostic the extension has added without disabling the
extension.

## Configuration

| Setting | Default | Description |
|---|---|---|
| `adsmt-lints.auditPath` | `""` | Default audit JSON path. Used by the load command when no path is provided interactively. |
| `adsmt-lints.autoReload` | `true` | Watch `auditPath` for changes and re-render on every file-system event. |

## JSON schema

The extension consumes the `adsmt_lints::DiagnosticsDocument`
shape (schema version 1):

```json
{
  "schema_version": 1,
  "generator": "adsmt-lints v0.19.0",
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

Unknown schema versions are rejected with a notification rather
than partially parsed — protects against silently-corrupt
behaviour on future schema bumps.

## Build / develop

```bash
cd tooling/vscode-extension
npm install
npm run compile
# Open this folder in VS Code and press F5 to launch a
# development host.
```

## Known limitations (v0.19 F.1 scaffold)

- Source-loc files are not yet populated by adsmt-lints (the
  JSON's `source_loc` has line + column only). Diagnostics
  currently land on the audit JSON file itself; once cert
  producers populate `PatternMarker.source_loc` with an actual
  file path, the diagnostic placement will follow.
- Workspace-level configuration (per-folder `auditPath`)
  works but the auto-reload watcher is global. Multi-root
  workspaces with distinct audit paths per root land in v0.19+.
- LSP integration is a separate exploration (F.3) — this
  extension is a problem-matcher style consumer, not an LSP
  client.

## License

Tri-licensed under BSD-2-Clause OR Apache-2.0 OR
LGPL-2.1-or-later — matches the adsmt main project's triple.
