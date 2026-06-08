//! Reference Lean 4 emitter, built as a `wasm32-wasip1` command.
//!
//! The host↔emitter protocol (shared by every adsmt emitter,
//! whatever its tier): the serialized certificate arrives on
//! **stdin**, the prover source goes to **stdout**, and the exit
//! code is `0` ok / `2` unsupported / `3` malformed-cert / else
//! internal. This wrapper decodes the certificate (CBOR — the
//! default wire it declares) and re-states it as Lean via
//! `adsmt_cert::emit_lean`.
//!
//! The same shape ports any `&Certificate -> String` emitter (Rocq,
//! Isabelle, …) to a wasm package: decode, call the emit function,
//! write stdout.

use std::io::{Read, Write};
use std::process::ExitCode;

use adsmt_emit_contract::Wire;

fn main() -> ExitCode {
    let mut bytes = Vec::new();
    if let Err(e) = std::io::stdin().read_to_end(&mut bytes) {
        eprintln!("lean-emitter: reading stdin: {e}");
        return ExitCode::from(1);
    }

    // This emitter declares `wire = "cbor"`, so the certificate
    // arrives CBOR-encoded.
    let cert: adsmt_cert::Certificate = match adsmt_emit_contract::decode(&bytes, Wire::Cbor) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("lean-emitter: {e}");
            return ExitCode::from(3);
        }
    };

    let text = adsmt_cert::emit_lean(&cert);
    if std::io::stdout().write_all(text.as_bytes()).is_err() {
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
}
