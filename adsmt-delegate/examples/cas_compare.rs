//! MathHook vs Singular head-to-head on their SHARED class (`Factorization`)
//! plus the Singular-only live class (`IdealMembership`) — a scratch
//! measurement harness (run: `cargo run -p adsmt-delegate --example
//! cas_compare --features cas`). Every backend reply is admit-re-checked by
//! `adsmt_cas::admit` exactly as the live dispatcher does, so a "verdict"
//! here is a REAL, trusted verdict; `Unknown` = declined / witness rejected.

#[cfg(feature = "cas")]
fn main() {
    use adsmt_cas::poly::MPoly;
    use adsmt_cas::{CasBackend, CasReply, Disposition, Obligation, Ring, admit};
    use num_bigint::BigInt;
    use std::time::Instant;

    let c = |n: i64| MPoly::from_int(BigInt::from(n));
    let x = || MPoly::var(0);
    let y = || MPoly::var(1);

    let singular = cas_backend_singular::SingularBackend::new(
        std::env::var("ADSMT_SINGULAR_PATH").unwrap_or_else(|_| "Singular".into()),
    );
    let mathhook = cas_backend_mathhook::MathhookBackend::new();
    let backends: [(&str, &dyn CasBackend); 2] = [("singular", &singular), ("mathhook", &mathhook)];

    // ── the shared class: Factorization (both Sat-witnessed) ────────────────
    let facts: Vec<(&str, MPoly)> = vec![
        ("x^2 - 1", x().mul(&x()).sub(&c(1))),
        ("x^2 + 2x + 1", x().mul(&x()).add(&c(2).mul(&x())).add(&c(1))),
        ("2x^2 - 2", c(2).mul(&x()).mul(&x()).sub(&c(2))),
        ("x^3 - x", x().mul(&x()).mul(&x()).sub(&x())),
        ("x^2 + 1 (irreducible/Q)", x().mul(&x()).add(&c(1))),
        ("x^4 - 1", x().mul(&x()).mul(&x()).mul(&x()).sub(&c(1))),
        ("6x^2 + 5x + 1 (non-monic)", c(6).mul(&x()).mul(&x()).add(&c(5).mul(&x())).add(&c(1))),
        ("x^2 - y^2 (multivariate)", x().mul(&x()).sub(&y().mul(&y()))),
        (
            "x^8 - 1",
            {
                let mut p = x();
                for _ in 0..7 {
                    p = p.mul(&x());
                }
                p.sub(&c(1))
            },
        ),
    ];
    println!("── Factorization (ring Q) — the SHARED class ──");
    println!("{:<28} {:>22} {:>22}", "target", "singular", "mathhook");
    for (name, target) in &facts {
        let ob = Obligation::Factorization { ring: Ring::Q, target: target.clone() };
        let mut cells = Vec::new();
        for (_, b) in &backends {
            let t0 = Instant::now();
            let reply = b.decide(&ob);
            let disp = match reply {
                CasReply::Witnessed(w) => admit(&ob, &w),
                _ => Disposition::Unknown,
            };
            let us = t0.elapsed().as_micros();
            cells.push(format!(
                "{} {:>8}µs",
                match disp {
                    Disposition::Verdict(v) => format!("{v:?}"),
                    Disposition::Unknown => "Unknown".into(),
                },
                us
            ));
        }
        println!("{:<28} {:>22} {:>22}", name, cells[0], cells[1]);
    }

    // ── the Singular-only LIVE class: IdealMembership ───────────────────────
    // f ∈ ⟨g₁, g₂⟩ over ℤ: (x−1) ∈ ⟨x²−1, x+1⟩? x²−1 = (x−1)(x+1) so
    // x−1 = (x²−1) − (x−1)·... — take simple certain members instead:
    // f = x²−1 with generators {x−1} — f = (x+1)(x−1) ⇒ member.
    let members: Vec<(&str, MPoly, Vec<MPoly>)> = vec![
        ("x^2-1 ∈ <x-1>", x().mul(&x()).sub(&c(1)), vec![x().sub(&c(1))]),
        ("x^2-y^2 ∈ <x-y>", x().mul(&x()).sub(&y().mul(&y())), vec![x().sub(&y())]),
        ("x ∈ <x^2> (NOT member)", x(), vec![x().mul(&x())]),
    ];
    println!("\n── IdealMembership (ring Z) — Singular-only at the live boundary ──");
    println!("{:<28} {:>22} {:>22}", "obligation", "singular", "mathhook");
    for (name, f, generators) in &members {
        let ob = Obligation::IdealMembership {
            ring: Ring::Z,
            f: f.clone(),
            generators: generators.clone(),
        };
        let mut cells = Vec::new();
        for (_, b) in &backends {
            let t0 = Instant::now();
            let reply = b.decide(&ob);
            let disp = match reply {
                CasReply::Witnessed(w) => admit(&ob, &w),
                _ => Disposition::Unknown,
            };
            let us = t0.elapsed().as_micros();
            cells.push(format!(
                "{} {:>8}µs",
                match disp {
                    Disposition::Verdict(v) => format!("{v:?}"),
                    Disposition::Unknown => "Unknown".into(),
                },
                us
            ));
        }
        println!("{:<28} {:>22} {:>22}", name, cells[0], cells[1]);
    }
}

#[cfg(not(feature = "cas"))]
fn main() {
    eprintln!("build with --features cas");
}
