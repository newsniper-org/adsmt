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
//! | benchmark       | DPLL+Luby | CDCL+Luby (RC2.5) | Δ      |
//! |-----------------|-----------|-------------------|--------|
//! | pigeonhole_2var |  947 ns   |  2.21 µs          | +134%  |
//! | pigeonhole_3var | 5.36 µs   |  9.64 µs          | +80%   |
//! | unit_chain_5    |  380 ns   |  1.05 µs          | +177%  |
//!
//! **RC2.5 baseline, 2026-05-31** — post the RC1.2
//! two-watched-literals propagator. CDCL still pays for its
//! bookkeeping on these tiny instances; the unit-chain case
//! got noticeably slower than the v0.23 baseline (473 ns →
//! 1.05 µs) because two-watched needs to register watches on
//! every clause even when propagation never visits them. The
//! 3var pigeonhole improved relative to its v0.23 number
//! (10.37 µs → 9.64 µs, the expected 2WL win on
//! conflict-heavy instances).
//!
//! For now these numbers serve as a regression guardrail:
//! either side getting >30% slower at the same complexity
//! beyond this baseline is a signal worth chasing.

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
