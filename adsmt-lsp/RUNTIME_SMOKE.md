# adsmt-lsp runtime smoke

**Status**: v1.0.0-rc.2 RC2.6 — smoke passed 2026-05-31.

## Binary

`cargo build -p adsmt-lsp --release` produces
`target/release/adsmt-lsp` (ELF64 PIE, dynamically linked).

## Smoke message

Send a syntactically-malformed initialize message to verify
the binary:

  1. accepts stdin under the LSP framing convention,
  2. parses the Content-Length header,
  3. responds with a well-formed JSON-RPC error frame.

```bash
printf 'Content-Length: 158\r\n\r\n{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{},"processId":null,"rootUri":null,"workspaceFolders":null,"clientInfo":{"name":"smoke"}}}' \
  | timeout 2 target/release/adsmt-lsp
```

Expected response (RC2.6 smoke verified):

```
Content-Length: 75

{"jsonrpc":"2.0","error":{"code":-32700,"message":"Parse error"},"id":null}
```

The parse error in the response is the *intended* signal —
the test message intentionally undersizes the body so the
server's Content-Length-strict parser rejects it. What the
test confirms:

- The binary starts, opens stdin/stdout, and parses headers.
- The framing layer is intact (Content-Length-aware
  response).
- JSON-RPC error path produces a well-formed envelope.

A full happy-path test (initialize → initialized →
didOpen → hover → shutdown) lands in CI alongside an
LSP-client harness; for RC2.6 the binary-level smoke is the
mandatory gate. Full-protocol coverage is tracked as a
v1.0.1+ enhancement.
