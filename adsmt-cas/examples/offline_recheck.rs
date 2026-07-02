//! Offline re-check of a serialized [`adsmt_cas::CasProof`] — the §7 offline-replay
//! design in a single command.
//!
//! A CAS-delegated `unsat` certificate embeds, in its `TheoryWitness::Cas`, the
//! `proof_json`: a self-contained `CasProof` (the algebraic obligation plus the
//! witness a backend produced). This example deserializes that JSON and re-runs the
//! SAME trusted [`admit`](adsmt_cas::admit) re-checker — WITHOUT the CAS binary
//! (Singular / MathHook) or the SMT solver in the loop. A tampered or stale proof
//! re-checks to `Unknown`, never to a wrong verdict, so the re-check is the trust
//! anchor: you believe the CAS-delegated verdict iff this program prints `Verdict`.
//!
//! Usage:
//! ```text
//! # 1. Extract the proof_json out of an emitted JSON certificate:
//! jq -r '..|.Cas?|select(.)|.proof_json' exp1.cert.json > exp1.proof.json
//! # 2. Re-check it offline (reads the CasProof JSON from a path arg or stdin):
//! cargo run -p adsmt-cas --example offline_recheck -- exp1.proof.json
//! ```
//!
//! Exit code is `0` on a re-derived `Verdict`, `1` otherwise (so it composes into a
//! CI gate).

use std::io::Read;

use adsmt_cas::{CasProof, Disposition};

fn main() {
    // Read the serialized CasProof from the first CLI arg (a path) or from stdin.
    let raw = match std::env::args().nth(1) {
        Some(path) => std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("cannot read {path}: {e}")),
        None => {
            let mut s = String::new();
            std::io::stdin()
                .read_to_string(&mut s)
                .expect("cannot read CasProof JSON from stdin");
            s
        }
    };

    let proof: CasProof =
        serde_json::from_str(&raw).expect("input is not a serialized adsmt_cas::CasProof");

    // The trust anchor: the ONE re-checker shared by online dispatch and offline
    // replay. No CAS, no solver — just exact BigRational / BigInt arithmetic.
    let disposition = proof.recheck();

    match disposition {
        Disposition::Verdict(v) => {
            println!("offline recheck: VERDICT {v:?} (obligation re-derived from the witness)");
            if let Some(prov) = &proof.provenance {
                println!("advisory provenance (does NOT affect the verdict):\n{prov}");
            }
            std::process::exit(0);
        }
        Disposition::Unknown => {
            eprintln!(
                "offline recheck: UNKNOWN — the witness does not re-derive the obligation \
                 (tampered / stale proof, or a backend soundness bug). No verdict is trusted."
            );
            std::process::exit(1);
        }
    }
}
