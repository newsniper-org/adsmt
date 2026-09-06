//! Re-check a certificate off disk: the offline path a consumer takes
//! before trusting an artifact it did not produce.
//!
//! usage: cargo run -p adsmt-cert --example recheck_cert -- <cert.json>

fn main() -> std::process::ExitCode {
    let Some(path) = std::env::args().nth(1) else {
        eprintln!("usage: recheck_cert <cert.json>");
        return std::process::ExitCode::from(2);
    };
    let src = std::fs::read_to_string(&path).expect("read cert");
    let cert: adsmt_cert::Certificate = serde_json::from_str(&src).expect("parse cert");
    match cert.recheck() {
        Ok(rep) => {
            let (theory, instance, assumed) = rep.trust_counts();
            println!("re-check PASSED");
            println!("  structural steps re-derived: {}", rep.structural_steps);
            println!("  theory steps:                {theory} \
({} witness re-verified, {} taken on faith)",
                     rep.verified_witnesses(), rep.unverified_witnesses());
            println!("  instance steps:              {instance}");
            println!("  assumed (user/abduced):      {assumed}");
            println!("  conclusion: {}", rep.conclusion.concl);
            std::process::ExitCode::SUCCESS
        }
        Err(e) => {
            println!("re-check FAILED: {e}");
            std::process::ExitCode::FAILURE
        }
    }
}
