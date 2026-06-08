//! Native test of the reference Lean emitter: a CBOR certificate on
//! stdin produces Lean source on stdout. (The binary runs identically
//! as a native command and as a wasip1 wasm module; this exercises the
//! emit logic without a wasm build.)

use std::io::Write;
use std::process::{Command, Stdio};

use adsmt_cert::{CertBuilder, Sequent, StepBody};
use adsmt_core::{Term, Type};
use adsmt_emit_contract::{encode, Wire};

fn lean_bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_lean"))
}

fn sample_cert_cbor() -> Vec<u8> {
    let mut b = CertBuilder::new();
    let x = Term::var("x", Type::bool_());
    let s0 = b.add(
        StepBody::Refl(x.clone()),
        Sequent { hyps: vec![], concl: Term::mk_eq(x.clone(), x).unwrap() },
    );
    let cert = b.finalize(s0);
    encode(&cert, Wire::Cbor)
}

#[test]
fn emits_lean_from_cbor_cert() {
    let cbor = sample_cert_cbor();
    let mut child = lean_bin().stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(&cbor).unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let lean = String::from_utf8_lossy(&out.stdout);
    assert!(!lean.trim().is_empty(), "expected non-empty Lean output");
}

/// End-to-end through the real runtime: load the *built* `lean.wasm`
/// and emit a CBOR certificate under wasmi. Ignored by default (needs
/// the wasm artifact); run with:
///   cargo build --release --target wasm32-wasip1 --bin lean
///   cargo test -p adsmt-emit-lean -- --ignored
#[test]
#[ignore = "requires a prebuilt target/wasm32-wasip1/release/lean.wasm"]
fn wasm_emitter_emits_lean_via_runtime() {
    use adsmt_emit_pm::{Lockfile, LockedPackage, Store, Wire};
    use adsmt_emit_runtime::Runtime;

    let wasm = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/wasm32-wasip1/release/lean.wasm");
    assert!(
        wasm.is_file(),
        "build it first: cargo build --release --target wasm32-wasip1 --bin lean"
    );

    let tmp = tempfile::tempdir().unwrap();
    let staged = tmp.path().join("contents");
    std::fs::create_dir_all(&staged).unwrap();
    std::fs::copy(&wasm, staged.join("lean.wasm")).unwrap();

    let store = Store::at(tmp.path().join("store"));
    let sha = store.add_tree(&staged).unwrap();
    let pkg = LockedPackage {
        name: "lean".into(),
        target: "lean".into(),
        version: "0.0.0".into(),
        source: "path+file:///lean".into(),
        contents_sha256: sha,
        main: "lean.wasm".into(),
        wire: Wire::Cbor,
    };
    let rt = Runtime::new(Lockfile::new(vec![pkg]), store);

    let cbor = sample_cert_cbor();
    let out = rt.emit("lean", &cbor).unwrap().unwrap();
    assert!(!out.text.trim().is_empty(), "expected Lean output from wasm");
    eprintln!("--- Lean from wasm ---\n{}", out.text);
}

#[test]
fn malformed_cert_exits_3() {
    let mut child = lean_bin()
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(b"\xff\xff not cbor at all").unwrap();
    let out = child.wait_with_output().unwrap();
    assert_eq!(out.status.code(), Some(3));
}
