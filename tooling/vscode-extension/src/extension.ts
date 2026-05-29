/*
 * adsmt-lints VS Code extension.
 *
 * Consumes the JSON document produced by
 * `adsmt_lints::audit_to_json` (or by `lu-smt --audit-json`)
 * and renders each diagnostic as a VS Code Problems entry +
 * editor squiggle.
 *
 * v0.19 F.1 scaffold. The minimum-viable shape:
 *   - "adsmt: Load audit JSON" command — pick a file via the
 *     quick-open or use the configured `adsmt-lints.auditPath`,
 *     parse it as JSON, populate the diagnostics collection.
 *   - "adsmt: Clear lints diagnostics" command — remove every
 *     diagnostic the extension has added.
 *   - File-watcher on `adsmt-lints.auditPath` when
 *     `adsmt-lints.autoReload` is true — re-renders on every
 *     file-system change.
 *
 * JSON schema consumed: `adsmt_lints::DiagnosticsDocument`
 * (schema_version 1). Unknown schema versions are rejected
 * with a notification.
 */

import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';

interface SourceLocPayload {
  line: number;
  column: number;
}

interface StepIdPayload {
  id: number;
}

interface DeadPatternDiagnostic {
  marker_index: number;
  marker_name: string | null;
  severity: 'info' | 'warning' | 'error';
  message: string;
  source_loc: SourceLocPayload | null;
  cert_step_count: number;
  steps_matched_by_siblings: StepIdPayload[];
}

interface DiagnosticsDocument {
  schema_version: number;
  generator: string;
  diagnostics: DeadPatternDiagnostic[];
}

const SUPPORTED_SCHEMA_VERSION = 1;

let diagnosticCollection: vscode.DiagnosticCollection | null = null;
let watcher: fs.FSWatcher | null = null;

export function activate(context: vscode.ExtensionContext): void {
  diagnosticCollection =
    vscode.languages.createDiagnosticCollection('adsmt-lints');
  context.subscriptions.push(diagnosticCollection);

  context.subscriptions.push(
    vscode.commands.registerCommand('adsmt-lints.loadAudit', () =>
      loadAuditCommand(context),
    ),
  );

  context.subscriptions.push(
    vscode.commands.registerCommand('adsmt-lints.clearDiagnostics', () => {
      diagnosticCollection?.clear();
    }),
  );

  // Configuration-driven auto-reload watcher.
  const config = vscode.workspace.getConfiguration('adsmt-lints');
  const auditPath = config.get<string>('auditPath') ?? '';
  const autoReload = config.get<boolean>('autoReload') ?? true;
  if (auditPath && autoReload) {
    startWatching(auditPath);
  }
}

export function deactivate(): void {
  stopWatching();
  diagnosticCollection?.dispose();
  diagnosticCollection = null;
}

async function loadAuditCommand(
  _context: vscode.ExtensionContext,
): Promise<void> {
  const config = vscode.workspace.getConfiguration('adsmt-lints');
  const configured = config.get<string>('auditPath') ?? '';
  const picked = configured
    ? configured
    : await pickAuditPath();
  if (!picked) {
    return;
  }
  await renderFromPath(picked);
}

async function pickAuditPath(): Promise<string | undefined> {
  const uris = await vscode.window.showOpenDialog({
    canSelectFolders: false,
    canSelectFiles: true,
    canSelectMany: false,
    filters: { 'adsmt-lints JSON': ['json'] },
    title: 'Select adsmt-lints audit JSON',
  });
  return uris?.[0]?.fsPath;
}

async function renderFromPath(p: string): Promise<void> {
  let body: string;
  try {
    body = await fs.promises.readFile(p, 'utf8');
  } catch (err) {
    vscode.window.showErrorMessage(
      `adsmt-lints: cannot read ${p}: ${(err as Error).message}`,
    );
    return;
  }
  let doc: DiagnosticsDocument;
  try {
    doc = JSON.parse(body);
  } catch (err) {
    vscode.window.showErrorMessage(
      `adsmt-lints: JSON parse error in ${p}: ${(err as Error).message}`,
    );
    return;
  }
  if (doc.schema_version !== SUPPORTED_SCHEMA_VERSION) {
    vscode.window.showWarningMessage(
      `adsmt-lints: unsupported audit schema version ${doc.schema_version}. ` +
        `This extension build supports v${SUPPORTED_SCHEMA_VERSION} only.`,
    );
    return;
  }
  applyDiagnostics(p, doc);
}

function applyDiagnostics(
  auditPath: string,
  doc: DiagnosticsDocument,
): void {
  if (!diagnosticCollection) {
    return;
  }
  diagnosticCollection.clear();
  if (doc.diagnostics.length === 0) {
    vscode.window.setStatusBarMessage(
      `adsmt-lints: 0 diagnostics from ${path.basename(auditPath)}`,
      3000,
    );
    return;
  }
  // Group by source-loc file path. Markers with source_loc =
  // null land on the audit file itself as a "file-level"
  // diagnostic.
  const auditUri = vscode.Uri.file(auditPath);
  const byUri = new Map<string, vscode.Diagnostic[]>();
  for (const d of doc.diagnostics) {
    const loc = d.source_loc;
    const uri = auditUri.toString(); // v0.19 ships file-name-less diagnostics
    const line = loc ? Math.max(0, loc.line - 1) : 0;
    const col = loc ? Math.max(0, loc.column - 1) : 0;
    const range = new vscode.Range(line, col, line, col + 1);
    const sev = severityFromString(d.severity);
    const diag = new vscode.Diagnostic(range, d.message, sev);
    diag.source = 'adsmt-lints';
    if (d.marker_name) {
      diag.code = `pattern #${d.marker_index} (${d.marker_name})`;
    } else {
      diag.code = `pattern #${d.marker_index}`;
    }
    const arr = byUri.get(uri) ?? [];
    arr.push(diag);
    byUri.set(uri, arr);
  }
  for (const [uri, arr] of byUri.entries()) {
    diagnosticCollection.set(vscode.Uri.parse(uri), arr);
  }
  vscode.window.setStatusBarMessage(
    `adsmt-lints: ${doc.diagnostics.length} diagnostic(s) from ${path.basename(auditPath)}`,
    3000,
  );
}

function severityFromString(s: string): vscode.DiagnosticSeverity {
  switch (s) {
    case 'error':
      return vscode.DiagnosticSeverity.Error;
    case 'warning':
      return vscode.DiagnosticSeverity.Warning;
    case 'info':
      return vscode.DiagnosticSeverity.Information;
    default:
      return vscode.DiagnosticSeverity.Hint;
  }
}

function startWatching(auditPath: string): void {
  stopWatching();
  if (!fs.existsSync(auditPath)) {
    return;
  }
  try {
    watcher = fs.watch(auditPath, { persistent: false }, async () => {
      // Debounce by re-reading the file directly. fs.watch can
      // fire multiple events for a single save; the parsing
      // path is idempotent so we just re-render.
      await renderFromPath(auditPath);
    });
  } catch (err) {
    vscode.window.showWarningMessage(
      `adsmt-lints: auto-reload watcher failed for ${auditPath}: ${(err as Error).message}`,
    );
  }
}

function stopWatching(): void {
  watcher?.close();
  watcher = null;
}
