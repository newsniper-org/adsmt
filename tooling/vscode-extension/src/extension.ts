/*
 * adsmt-lints VS Code extension — vscode-specific layer.
 *
 * v0.25 EXT.1 split per `lsp_roadmap.md`. The editor-agnostic
 * JSON parsing + types live in `audit.ts`; this file holds the
 * vscode-API consumers (commands, diagnostic collection,
 * file-watcher) and the LSP client glue for the v0.25 25LSP.*
 * server.
 */

import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from 'vscode-languageclient/node';

import {
  DeadPatternDiagnostic,
  DiagnosticsDocument,
  diagnosticCode,
  loc0,
  parseAuditJson,
  ParseResult,
} from './audit';

let diagnosticCollection: vscode.DiagnosticCollection | null = null;
let watcher: fs.FSWatcher | null = null;
let lspClient: LanguageClient | null = null;

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

  // v0.25 EXT.1 — start the adsmt-lsp language server.
  const lspBinary =
    config.get<string>('lspBinary') ?? 'adsmt-lsp';
  startLspClient(context, lspBinary);
}

function startLspClient(
  context: vscode.ExtensionContext,
  binary: string,
): void {
  const serverOptions: ServerOptions = {
    command: binary,
    args: [],
    transport: TransportKind.stdio,
  };
  const clientOptions: LanguageClientOptions = {
    documentSelector: [
      { scheme: 'file', language: 'smt-lib' },
      { scheme: 'file', language: 'smt2' },
      { scheme: 'file', language: 'lu-kb' },
    ],
    synchronize: {
      configurationSection: 'adsmt-lints',
    },
  };
  lspClient = new LanguageClient(
    'adsmt-lsp',
    'adsmt LSP',
    serverOptions,
    clientOptions,
  );
  lspClient.start();
  context.subscriptions.push({
    dispose: () => {
      lspClient?.stop();
    },
  });
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
  const picked = configured ? configured : await pickAuditPath();
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
  const result: ParseResult = parseAuditJson(body);
  switch (result.kind) {
    case 'parse-error':
      vscode.window.showErrorMessage(
        `adsmt-lints: JSON parse error in ${p}: ${result.message}`,
      );
      return;
    case 'schema-mismatch':
      vscode.window.showWarningMessage(
        `adsmt-lints: unsupported audit schema version ${result.got}. ` +
          `This extension build supports v${result.expected} only.`,
      );
      return;
    case 'ok':
      applyDiagnostics(p, result.doc);
      return;
  }
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
    const { line, col } = loc0(d.source_loc);
    const uri = auditUri.toString();
    const range = new vscode.Range(line, col, line, col + 1);
    const sev = severityFromString(d.severity);
    const diag = new vscode.Diagnostic(range, d.message, sev);
    diag.source = 'adsmt-lints';
    diag.code = diagnosticCode(d);
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

// Re-export for tests that want to consume the parsing layer
// without spinning up a full vscode extension host.
export { parseAuditJson, diagnosticCode, loc0 } from './audit';
export type { DeadPatternDiagnostic, DiagnosticsDocument } from './audit';
