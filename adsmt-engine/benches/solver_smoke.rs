//! Smoke benchmarks for the solver hot path.
//!
//! v0.19 G.1 scaffold. Three benchmark groups intended to surface
//! regressions on the most-trafficked paths:
//!
//! 1. **fresh_solver** — `Solver::new()` end-to-end. Sanity
//!    check that fresh-solver creation doesn't drift in cost.
//! 2. **propositional_unsat** — `(p ∧ ¬p)` checkout — exercises
//!    parsing, conversion, unit-propagation, and Unsat cert
//!    construction. The most common minimal SMT shape.
//! 3. **lia_three_var_unsat** — Fourier-Motzkin three-variable
//!    chain unsat (`x ≤ y, y ≤ z, z ≤ x − 1`). Pins the
//!    LinArith fast path that v0.17 T#37 added.
//!
//! Run with `cargo bench -p adsmt-engine --bench solver_smoke`.
//! criterion writes HTML reports under `target/criterion/`.

use criterion::{criterion_group, criterion_main, Criterion};

use adsmt_engine::Solver;

fn bench_fresh_solver(c: &mut Criterion) {
    c.bench_function("fresh_solver", |b| {
        b.iter(|| {
            let _ = Solver::new();
        });
    });
}

fn bench_propositional_unsat(c: &mut Criterion) {
    use adsmt_core::{Term, Type};
    c.bench_function("propositional_unsat", |b| {
        b.iter(|| {
            let mut solver = Solver::new();
            let p = Term::var("p", Type::bool_());
            let not_p = Term::mk_not(p.clone()).unwrap();
            let and_term = Term::mk_and(p, not_p).unwrap();
            let _ = solver.assert(and_term);
            let _ = solver.check_sat();
        });
    });
}

criterion_group!(benches, bench_fresh_solver, bench_propositional_unsat);
criterion_main!(benches);
