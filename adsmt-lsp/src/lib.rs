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

/// Per-document state. Kept tiny on purpose; capabilities like
/// hover / definition / completion read from this and from any
/// derived index they care to build on top.
#[derive(Clone, Debug)]
pub struct Document {
    pub uri: Url,
    pub language_id: String,
    pub version: i32,
    pub text: String,
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
                // Capability bitmap empty for the 25LSP.1 scaffold.
                // 25LSP.2 fills in diagnostic, 25LSP.3 definition, …
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
        let doc = Document {
            uri: params.text_document.uri.clone(),
            language_id: params.text_document.language_id,
            version: params.text_document.version,
            text: params.text_document.text,
        };
        self.state.write().await.documents.insert(doc.uri.clone(), doc);
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let mut state = self.state.write().await;
        if let Some(doc) = state.documents.get_mut(&params.text_document.uri) {
            // FULL sync mode: replace the text with the last
            // content change.
            if let Some(change) = params.content_changes.into_iter().last() {
                doc.text = change.text;
            }
            doc.version = params.text_document.version;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.state.write().await.documents.remove(&params.text_document.uri);
    }
}
