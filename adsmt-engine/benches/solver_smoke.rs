//! Smoke benchmarks for the solver hot path.
//!
//! v0.19 G.1 scaffold; v0.21 G.1 re-baselined under the new
//! Luby-restart fallback DPLL (B.1) and extended with the LIA
//! bound-conflict benchmark that the v0.19 doc-comment promised
//! but the v0.19 scaffold didn't actually wire up.
//!
//! Benchmark groups:
//!
//! 1. **fresh_solver** — `Solver::new()` end-to-end. Sanity
//!    check that fresh-solver creation doesn't drift in cost.
//! 2. **propositional_unsat** — `(p ∧ ¬p)` checkout — exercises
//!    parsing, conversion, unit-propagation, and Unsat cert
//!    construction. The most common minimal SMT shape.
//! 3. **lia_bound_conflict_unsat** — `(x ≤ 5) ∧ (x ≥ 10)` —
//!    pins the LinArith fast path (Q#37, v0.17 deepening).
//!    Variable-only LIA constraints exercise the bound-tightening
//!    code without going through the Simplex bridge.
//!
//! Run with `cargo bench -p adsmt-engine --bench solver_smoke`.
//! criterion writes HTML reports under `target/criterion/`.
//!
//! ## v0.21 G.1 baseline (2026-05-29, default features)
//!
//! Recorded on the v0.21-open commit immediately after the B.1
//! Luby-restart wrapper began driving the built-in DPLL fallback.
//! Times are criterion's median estimate.
//!
//! | benchmark                  | time     | vs v0.19 G.1 |
//! |----------------------------|----------|--------------|
//! | fresh_solver               | 122.6 ns | unchanged    |
//! | propositional_unsat        |  1.89 µs | unchanged    |
//! | lia_bound_conflict_unsat   |  2.82 µs | new          |
//!
//! No regression from the restart-loop introduction — first
//! Luby epoch already covers what the old single-shot
//! `dpll(_, 16)` covered, so easy-case latency is preserved.

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

fn bench_lia_bound_conflict_unsat(c: &mut Criterion) {
    use adsmt_core::{Kind, Term, Type};
    c.bench_function("lia_bound_conflict_unsat", |b| {
        b.iter(|| {
            let int_ = Type::const_("Int", Kind::Type);
            let mut solver = Solver::new();
            let x = Term::var("x", int_.clone());
            // (<= x 5)
            let le = Term::const_(
                "<=",
                Type::fun(
                    int_.clone(),
                    Type::fun(int_.clone(), Type::bool_()).unwrap(),
                )
                .unwrap(),
            );
            let five = Term::const_("int:5", int_.clone());
            let upper = Term::app(
                Term::app(le.clone(), x.clone()).unwrap(),
                five,
            )
            .unwrap();
            // (>= x 10)
            let ge = Term::const_(
                ">=",
                Type::fun(
                    int_.clone(),
                    Type::fun(int_.clone(), Type::bool_()).unwrap(),
                )
                .unwrap(),
            );
            let ten = Term::const_("int:10", int_);
            let lower = Term::app(
                Term::app(ge, x).unwrap(),
                ten,
            )
            .unwrap();
            let _ = solver.assert(upper);
            let _ = solver.assert(lower);
            let _ = solver.check_sat();
        });
    });
}

criterion_group!(
    benches,
    bench_fresh_solver,
    bench_propositional_unsat,
    bench_lia_bound_conflict_unsat,
);
criterion_main!(benches);
