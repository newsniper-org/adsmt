/*
 * adsmt-lints audit JSON consumer — editor-agnostic core.
 *
 * v0.25 EXT.1 split per `lsp_roadmap.md`. The JSON schema +
 * parsing live here so non-vscode editors (or unit tests) can
 * reuse the logic without pulling in the `vscode` module.
 *
 * Editor-specific glue (vscode.Diagnostic, vscode.Range,
 * vscode.window, …) lives in `extension.ts`.
 */

export interface SourceLocPayload {
  line: number;
  column: number;
}

export interface StepIdPayload {
  id: number;
}

export interface DeadPatternDiagnostic {
  marker_index: number;
  marker_name: string | null;
  severity: 'info' | 'warning' | 'error';
  message: string;
  source_loc: SourceLocPayload | null;
  cert_step_count: number;
  steps_matched_by_siblings: StepIdPayload[];
}

export interface DiagnosticsDocument {
  schema_version: number;
  generator: string;
  diagnostics: DeadPatternDiagnostic[];
}

export const SUPPORTED_SCHEMA_VERSION = 1;

export type ParseResult =
  | { kind: 'ok'; doc: DiagnosticsDocument }
  | { kind: 'parse-error'; message: string }
  | { kind: 'schema-mismatch'; got: number; expected: number };

/**
 * Parse a JSON document body. Returns a discriminated union so
 * callers can dispatch on success / parse failure / unsupported
 * schema without throwing.
 */
export function parseAuditJson(body: string): ParseResult {
  let parsed: unknown;
  try {
    parsed = JSON.parse(body);
  } catch (err) {
    return { kind: 'parse-error', message: (err as Error).message };
  }
  const doc = parsed as DiagnosticsDocument;
  if (doc.schema_version !== SUPPORTED_SCHEMA_VERSION) {
    return {
      kind: 'schema-mismatch',
      got: doc.schema_version,
      expected: SUPPORTED_SCHEMA_VERSION,
    };
  }
  return { kind: 'ok', doc };
}

/**
 * 1-based line/column from the JSON payload → 0-based for LSP /
 * vscode consumption. Mirrors the v0.25 LSP.4 fix in adsmt-lsp.
 */
export function loc0(loc: SourceLocPayload | null): { line: number; col: number } {
  if (!loc) return { line: 0, col: 0 };
  return {
    line: Math.max(0, loc.line - 1),
    col: Math.max(0, loc.column - 1),
  };
}

/**
 * Compute the diagnostic code string for a marker. Used by both
 * the vscode-specific layer and any other consumer that needs a
 * stable label.
 */
export function diagnosticCode(d: DeadPatternDiagnostic): string {
  if (d.marker_name) {
    return `pattern #${d.marker_index} (${d.marker_name})`;
  }
  return `pattern #${d.marker_index}`;
}
