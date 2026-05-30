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
//! ## Baseline history (default features)
//!
//! Times are criterion's median estimate; all measurements use
//! `--warm-up-time 1 --measurement-time 3`.
//!
//! | benchmark                | v0.21 G.1 | CDCL fallback | +phase/act |
//! |--------------------------|-----------|---------------|------------|
//! | fresh_solver             | 122.6 ns  | 121.6 ns      |  124.8 ns  |
//! | propositional_unsat      |  1.89 µs  |  2.06 µs      |   2.10 µs  |
//! | lia_bound_conflict_unsat |  2.82 µs  |  3.01 µs      |   3.11 µs  |
//!
//! The first column → second column step paid the one-time
//! CDCL bookkeeping cost (trail entries, VSIDS activity bumps,
//! learnt-clause storage). The third column adds phase saving
//! + per-learnt-clause activity tracking introduced after the
//! initial CDCL wiring; the additional ~2–3% is the
//! `saved_phase` HashMap + `learnt_activity` Vec, and is
//! expected to amortise away on harder instances where phase
//! saving prevents re-traversing already-known-bad branches.
//!
//! The `oxiz` / `cadical` feature paths (production default)
//! are unaffected by either step.

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
