//! Build a certificate carrying constraint (3)(A) mappings and (3)(B)
//! tactic hints, to check that both actually reach the emitted output.
//!
//! usage: annotated_cert <out.json> [--bad-tactic]

use adsmt_cert::canonical::{CertBuilder, TacticHint, TargetMapping};
use adsmt_cert::recorder::recorder as r;
use adsmt_cert::witness::TheoryWitness;
use adsmt_core::{Term, Type};

fn main() {
    let out = std::env::args().nth(1).expect("usage: annotated_cert <out.json>");
    let bad = std::env::args().any(|a| a == "--bad-tactic");
    let mut b = CertBuilder::default();

    // (A) The user tells us what a name means in each target. `Coin` is
    // a sort adsmt knows nothing about; the mapping is what lets the
    // emitted theory typecheck at all.
    b.declare_sort("Coin", 0);
    b.add_mapping(TargetMapping {
        from: "Coin".into(),
        target: Some("lean".into()),
        to: "Bool".into(),
        requires: None,
    });
    b.add_mapping(TargetMapping {
        from: "Coin".into(),
        target: Some("isabelle".into()),
        to: "bool".into(),
        requires: None,
    });
    b.add_mapping(TargetMapping {
        from: "Coin".into(),
        target: Some("rocq".into()),
        to: "bool".into(),
        requires: None,
    });

    // (B) The user picks the tactic for this theory's steps. A tactic
    // that does not close the goal must break the build.
    for (target, good, bad_tac) in [
        ("lean", "trivial", "rfl"),
        ("isabelle", "simp", "(rule refl)"),
        ("rocq", "exact I.", "assumption."),
    ] {
        b.signature_mut().tactics.push(TacticHint {
            step: None,
            theory: Some("LinArith".into()),
            target: Some(target.into()),
            tactic: if bad { bad_tac.into() } else { good.into() },
        });
    }

    // A theory step whose conclusion is `True` — provable by the good
    // tactic in every target, and not by the bad one.
    let concl = Term::const_("true", Type::bool_());
    let th = r::theory(
        &mut b,
        "LinArith",
        TheoryWitness::Opaque { kind: "LIA".into(), notes: "demo".into() },
        Vec::new(),
        Vec::new(),
        concl,
    );
    let cert = b.snapshot(th);
    std::fs::write(&out, serde_json::to_string_pretty(&cert).unwrap()).unwrap();
    println!("wrote {out}{}", if bad { " (with a tactic that must FAIL)" } else { "" });
}
