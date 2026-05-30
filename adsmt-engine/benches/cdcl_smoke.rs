//! v0.21 G.1 follow-up — direct CDCL benches.
//!
//! `solver_smoke.rs` measures the full solver pipeline (CNF
//! flatten → SAT → theory routing → cert build). This file
//! drops a level lower and times `cdcl::cdcl_solve` /
//! `cdcl::cdcl_with_restarts` against
//! `bool_solver::dpll_with_restarts` on the same clause sets,
//! so the CDCL deepening landed in v0.21 B.1 can be tracked
//! independently of solver-level overhead.
//!
//! ## Initial baseline (2026-05-30, default features)
//!
//! Run with `cargo bench -p adsmt-engine --bench cdcl_smoke`.
//!
//! | benchmark            | DPLL+Luby | CDCL+Luby | Δ      |
//! |----------------------|-----------|-----------|--------|
//! | pigeonhole_2var      |  888 ns   |  1.80 µs  | +103%  |
//! | pigeonhole_3var      | 5.08 µs   | 10.37 µs  | +104%  |
//! | unit_chain_5         |  344 ns   |   473 ns  | +37%   |
//!
//! On these tiny instances CDCL pays for its bookkeeping
//! without earning its keep — there are not enough conflicts
//! for learnt-clause reuse and VSIDS reordering to amortise
//! the per-conflict cost. The cross-over point on harder
//! instances is the real target; see the v0.23 cycle's
//! roadmap for synthetic harder benches once we have a
//! proper instance generator.
//!
//! For now these numbers serve as a regression guardrail:
//! either side getting >20% slower at the same complexity
//! is a signal worth chasing.

use criterion::{criterion_group, criterion_main, Criterion};

use adsmt_core::{Term, Type};
use adsmt_engine::bool_solver::{dpll_with_restarts, BoolResult};
use adsmt_engine::cdcl::cdcl_with_restarts;
use adsmt_engine::cnf::{Clause, Lit};

fn p() -> Term { Term::var("p", Type::bool_()) }
fn q() -> Term { Term::var("q", Type::bool_()) }
fn r() -> Term { Term::var("r", Type::bool_()) }

fn pigeonhole_2var() -> Vec<Clause> {
    vec![
        vec![Lit::pos(p()), Lit::pos(q())],
        vec![Lit::neg(p()), Lit::pos(q())],
        vec![Lit::pos(p()), Lit::neg(q())],
        vec![Lit::neg(p()), Lit::neg(q())],
    ]
}

fn pigeonhole_3var() -> Vec<Clause> {
    vec![
        vec![Lit::pos(p()), Lit::pos(q()), Lit::pos(r())],
        vec![Lit::neg(p()), Lit::pos(q()), Lit::pos(r())],
        vec![Lit::pos(p()), Lit::neg(q()), Lit::pos(r())],
        vec![Lit::neg(p()), Lit::neg(q()), Lit::pos(r())],
        vec![Lit::pos(p()), Lit::pos(q()), Lit::neg(r())],
        vec![Lit::neg(p()), Lit::pos(q()), Lit::neg(r())],
        vec![Lit::pos(p()), Lit::neg(q()), Lit::neg(r())],
        vec![Lit::neg(p()), Lit::neg(q()), Lit::neg(r())],
    ]
}

/// Implication chain `p, p → q, q → r, ¬r` — pure unit
/// propagation, no decisions, no learning. Catches solver
/// overhead on the easy path.
fn unit_chain_5() -> Vec<Clause> {
    vec![
        vec![Lit::pos(p())],
        vec![Lit::neg(p()), Lit::pos(q())],
        vec![Lit::neg(q()), Lit::pos(r())],
        vec![Lit::neg(r())],
    ]
}

fn bench_dpll_vs_cdcl_pigeonhole_2var(c: &mut Criterion) {
    let cs = pigeonhole_2var();
    let cs_dpll = cs.clone();
    let cs_cdcl = cs;
    c.bench_function("pigeonhole_2var/dpll", |b| {
        b.iter(|| {
            let r = dpll_with_restarts(&cs_dpll, 8, 12);
            assert_eq!(r, BoolResult::Unsat);
        });
    });
    c.bench_function("pigeonhole_2var/cdcl", |b| {
        b.iter(|| {
            let r = cdcl_with_restarts(&cs_cdcl, 64, 12);
            assert_eq!(r, BoolResult::Unsat);
        });
    });
}

fn bench_dpll_vs_cdcl_pigeonhole_3var(c: &mut Criterion) {
    let cs = pigeonhole_3var();
    let cs_dpll = cs.clone();
    let cs_cdcl = cs;
    c.bench_function("pigeonhole_3var/dpll", |b| {
        b.iter(|| {
            let r = dpll_with_restarts(&cs_dpll, 8, 12);
            assert_eq!(r, BoolResult::Unsat);
        });
    });
    c.bench_function("pigeonhole_3var/cdcl", |b| {
        b.iter(|| {
            let r = cdcl_with_restarts(&cs_cdcl, 64, 12);
            assert_eq!(r, BoolResult::Unsat);
        });
    });
}

fn bench_dpll_vs_cdcl_unit_chain(c: &mut Criterion) {
    let cs = unit_chain_5();
    let cs_dpll = cs.clone();
    let cs_cdcl = cs;
    c.bench_function("unit_chain_5/dpll", |b| {
        b.iter(|| {
            let r = dpll_with_restarts(&cs_dpll, 8, 12);
            assert_eq!(r, BoolResult::Unsat);
        });
    });
    c.bench_function("unit_chain_5/cdcl", |b| {
        b.iter(|| {
            let r = cdcl_with_restarts(&cs_cdcl, 64, 12);
            assert_eq!(r, BoolResult::Unsat);
        });
    });
}

criterion_group!(
    benches,
    bench_dpll_vs_cdcl_pigeonhole_2var,
    bench_dpll_vs_cdcl_pigeonhole_3var,
    bench_dpll_vs_cdcl_unit_chain,
);
criterion_main!(benches);
