//! Build a certificate that rests on a USER-SUPPLIED assumption, to
//! check that the assumption shows up as a SECOND trust source in each
//! emitted theory (constraint (3)(C) rule 1).
//!
//! usage: cargo run -p adsmt-cert --example assumed_cert -- <out.json>

use adsmt_cert::canonical::CertBuilder;
use adsmt_cert::recorder::recorder as r;
use adsmt_cert::witness::TheoryWitness;
use adsmt_core::{Term, Type};

fn main() {
    let out = std::env::args().nth(1).expect("usage: assumed_cert <out.json>");
    let mut b = CertBuilder::default();

    let p = Term::var("p", Type::bool_());
    let q = Term::var("q", Type::bool_());

    // The user says "assume q holds" — not proved, and everything below
    // is conditional on it.
    let assumed = r::assumed(&mut b, q.clone(), Some("assumed CryptHOL fact".into()))
        .expect("assumed");
    // A hypothesis the problem actually carries.
    let hyp = r::assume(&mut b, p.clone()).expect("assume");
    // A theory step that uses both.
    let concl = Term::const_("false", Type::bool_());
    let th = r::theory(
        &mut b,
        "EUF",
        TheoryWitness::Opaque { kind: "EUF".into(), notes: "demo".into() },
        vec![assumed.step(), hyp.step()],
        vec![p.clone()],
        concl,
    );
    let cert = b.snapshot(th);
    std::fs::write(&out, serde_json::to_string_pretty(&cert).unwrap()).unwrap();
    println!("wrote {out}");
}
