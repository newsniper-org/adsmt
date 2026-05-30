//! adsmt LSP server — v0.25 phase 2 scaffold.
//!
//! Connects to editor-agnostic LSP clients (vscode-extension,
//! neovim, emacs) via stdin/stdout JSON-RPC. The capability
//! surface lands incrementally across 25LSP.2 … 25LSP.7.

use tokio::io::{stdin, stdout};
use tower_lsp::{LspService, Server};

#[tokio::main]
async fn main() {
    let stdin = stdin();
    let stdout = stdout();
    let (service, socket) = LspService::new(adsmt_lsp::Backend::new);
    Server::new(stdin, stdout, socket).serve(service).await;
}
