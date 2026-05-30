//! adsmt LSP server library — v0.25 phase 2 scaffold.
//!
//! Public surface: the [`Backend`] type implements
//! [`tower_lsp::LanguageServer`] and is what the
//! `adsmt-lsp` binary wraps. The split keeps the binary itself
//! tiny (just `tokio::main` + `Server::serve`) so integration
//! tests can construct a `Backend` directly without going
//! through stdio.
//!
//! Scaffold capability set (this commit, 25LSP.1):
//!   - `initialize` / `initialized` / `shutdown` lifecycle
//!   - `textDocument/didOpen` + `didChange` + `didClose` sync
//!   - empty capability bitmap (every other capability lands in
//!     subsequent 25LSP.* tasks).
//!
//! Each subsequent task (25LSP.2 publishDiagnostics, 25LSP.3
//! definition, …) extends this same `Backend` type without
//! restructuring the lifecycle.

use std::collections::HashMap;
use std::sync::Arc;

use tokio::sync::RwLock;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer};

/// Re-export the LSP types-side `Position` under a less ambiguous
/// alias so call sites that also touch `adsmt_parser::sexpr::Position`
/// don't have to deal with name collisions.
pub use tower_lsp::lsp_types::Position as LspPosition;

/// Per-document state. Kept tiny on purpose; capabilities like
/// hover / definition / completion read from this and from any
/// derived index they care to build on top.
#[derive(Clone, Debug)]
pub struct Document {
    pub uri: Url,
    pub language_id: String,
    pub version: i32,
    pub text: String,
    /// v0.25 25LSP.3 — symbol → declaration range index, built
    /// at did_open / did_change time. Used by
    /// `textDocument/definition` to resolve identifiers back to
    /// their `declare-*` / `define-fun` site.
    pub symbols: HashMap<String, Range>,
}

#[derive(Default)]
struct State {
    documents: HashMap<Url, Document>,
}

/// The LSP backend. Holds the `Client` handle (for sending
/// `publishDiagnostics` / `logMessage` / `showMessage`) plus the
/// shared per-document state.
pub struct Backend {
    client: Client,
    state: Arc<RwLock<State>>,
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Self {
            client,
            state: Arc::new(RwLock::new(State::default())),
        }
    }

    /// Public accessor for testing — yields a snapshot of the
    /// currently-tracked documents.
    pub async fn documents_snapshot(&self) -> Vec<Document> {
        self.state.read().await.documents.values().cloned().collect()
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(
        &self,
        _params: InitializeParams,
    ) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                // v0.25 25LSP.2 — publish-side diagnostics:
                // no client opt-in needed (push model), but
                // advertise that we *will* push.
                diagnostic_provider: Some(
                    DiagnosticServerCapabilities::Options(
                        DiagnosticOptions {
                            identifier: Some("adsmt".to_string()),
                            inter_file_dependencies: false,
                            workspace_diagnostics: false,
                            work_done_progress_options: Default::default(),
                        },
                    ),
                ),
                // v0.25 25LSP.3 — go-to-definition for SMT-LIB
                // declarations + define-fun bodies.
                definition_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "adsmt-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _params: InitializedParams) {
        self.client
            .log_message(
                MessageType::INFO,
                format!(
                    "adsmt-lsp v{} ready (25LSP.1 scaffold)",
                    env!("CARGO_PKG_VERSION")
                ),
            )
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let symbols = build_symbol_index(&params.text_document.text);
        let doc = Document {
            uri: params.text_document.uri.clone(),
            language_id: params.text_document.language_id,
            version: params.text_document.version,
            text: params.text_document.text,
            symbols,
        };
        let uri = doc.uri.clone();
        let text = doc.text.clone();
        let version = doc.version;
        self.state.write().await.documents.insert(uri.clone(), doc);
        self.publish_smtlib_diagnostics(uri, &text, Some(version)).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        let version = params.text_document.version;
        let mut state = self.state.write().await;
        if let Some(doc) = state.documents.get_mut(&uri) {
            if let Some(change) = params.content_changes.into_iter().last() {
                doc.text = change.text;
            }
            doc.version = version;
            doc.symbols = build_symbol_index(&doc.text);
            let text = doc.text.clone();
            drop(state);
            self.publish_smtlib_diagnostics(uri, &text, Some(version)).await;
        }
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri.clone();
        let position = params.text_document_position_params.position;
        let state = self.state.read().await;
        let Some(doc) = state.documents.get(&uri) else {
            return Ok(None);
        };
        let Some(ident) = identifier_at_position(&doc.text, position) else {
            return Ok(None);
        };
        let Some(range) = doc.symbols.get(&ident).copied() else {
            return Ok(None);
        };
        Ok(Some(GotoDefinitionResponse::Scalar(Location { uri, range })))
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        self.state.write().await.documents.remove(&uri);
        // Clear any diagnostics on the closed document.
        self.client.publish_diagnostics(uri, vec![], None).await;
    }
}

impl Backend {
    /// v0.25 25LSP.2 — run the SMT-LIB parser over the
    /// document text and surface any errors as LSP Diagnostics.
    ///
    /// Initial scope: parser-level errors only. Solver-level
    /// audit (dead-pattern via `adsmt-lints::dead_pattern_audit`)
    /// requires the full check-sat pipeline and will land as a
    /// separate background pass in 25LSP.2 follow-up.
    async fn publish_smtlib_diagnostics(
        &self,
        uri: Url,
        text: &str,
        version: Option<i32>,
    ) {
        let diagnostics = parse_diagnostics(text);
        self.client.publish_diagnostics(uri, diagnostics, version).await;
    }
}

/// v0.25 25LSP.3 — build the symbol → declaration range
/// index for a document.
///
/// Walks `parse_smtlib_positioned` results and records the
/// position of each `declare-const` / `declare-fun` /
/// `define-fun` / `declare-sort` / `declare-datatype` /
/// `set-logic` form. The recorded range is the position of the
/// leading paren on the command, which is what
/// `goto_definition` jumps to.
///
/// Returns an empty map if the input fails to parse — callers
/// already get a diagnostic via `parse_diagnostics` in that
/// case.
pub fn build_symbol_index(text: &str) -> HashMap<String, Range> {
    use adsmt_parser::smtlib::{parse_smtlib_positioned, Command};
    let mut out = HashMap::new();
    let Ok(positioned) = parse_smtlib_positioned(text) else {
        return out;
    };
    for (cmd, pos) in positioned {
        let name = match &cmd {
            Command::DeclareSort { name, .. } => Some(name.clone()),
            Command::DeclareDatatype { name, .. } => Some(name.clone()),
            Command::DeclareConst { name, .. } => Some(name.clone()),
            Command::DeclareFun { name, .. } => Some(name.clone()),
            Command::DefineFun { name, .. } => Some(name.clone()),
            _ => None,
        };
        if let Some(name) = name {
            // `pos` is `Position { line, column }` 0-indexed
            // from `adsmt_parser::sexpr::byte_offset_to_position`.
            let lsp_pos = LspPosition::new(pos.line as u32, pos.column as u32);
            let range = Range {
                start: lsp_pos,
                end: LspPosition::new(
                    pos.line as u32,
                    pos.column as u32 + name.len() as u32,
                ),
            };
            out.insert(name, range);
        }
    }
    out
}

/// v0.25 25LSP.3 — extract the identifier under `position` in
/// `text`. Word boundary is the standard SMT-LIB lexical
/// alphabet (`A-Za-z0-9_!?-.*+/`).
pub fn identifier_at_position(text: &str, position: LspPosition) -> Option<String> {
    let mut line_iter = text.lines();
    let line = line_iter.nth(position.line as usize)?;
    let col = position.character as usize;
    let chars: Vec<char> = line.chars().collect();
    if col > chars.len() { return None; }
    let is_ident = |c: char| {
        c.is_ascii_alphanumeric()
            || matches!(c, '_' | '!' | '?' | '-' | '.' | '*' | '+' | '/')
    };
    // Find start of identifier at col.
    let mut start = col;
    while start > 0 && is_ident(chars[start - 1]) {
        start -= 1;
    }
    let mut end = col;
    while end < chars.len() && is_ident(chars[end]) {
        end += 1;
    }
    if start == end { return None; }
    Some(chars[start..end].iter().collect())
}

/// Convert a SMT-LIB parser run on `text` into LSP Diagnostics.
/// Exposed at module scope so the integration tests can call it
/// without constructing a `Backend`.
pub fn parse_diagnostics(text: &str) -> Vec<Diagnostic> {
    use adsmt_parser::smtlib::parse_smtlib;
    match parse_smtlib(text) {
        Ok(_) => Vec::new(),
        Err(e) => {
            // We don't have byte offsets out of the error type
            // today (SmtLibError holds messages, not positions),
            // so anchor the diagnostic at the document head and
            // include the full message body. Position-aware
            // diagnostics land in 25LSP.6 once the symbol index
            // can resolve identifiers back to ranges.
            let range = Range {
                start: Position::new(0, 0),
                end: Position::new(0, 0),
            };
            vec![Diagnostic {
                range,
                severity: Some(DiagnosticSeverity::ERROR),
                source: Some("adsmt-parser".to_string()),
                message: format!("{e}"),
                ..Default::default()
            }]
        }
    }
}
