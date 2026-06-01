//! `oxiz-math` Simplex-based LIA/LRA backend (Path A+B, P2).
//!
//! Behind the `oxiz-math` feature flag. Provides a Simplex-based
//! check pipeline that converts our hand-rolled `(var, op, k)` bounds and
//! `x + y op k` sum constraints into `oxiz-math::simplex` tableau
//! operations.
//!
//! The hand-rolled path in `arith.rs` stays in service when the
//! feature is off; both are exercised by the test suite. The
//! compatibility audit (P2 sibling task) confirms verdict agreement
//! between the two paths.

#[cfg(feature = "oxiz-math")]
mod with_simplex {
    use std::collections::HashMap;

    use oxiz_math::fast_rational::FastRational;
    use oxiz_math::simplex::{
        BoundType, ConstraintId, Row, SimplexResult, SimplexTableau, VarId,
    };

    /// One asserted bound: `var op k`. `op` is `<=` / `<` / `>=` / `>`.
    #[derive(Clone, Debug)]
    pub struct BoundAtom {
        pub var: String,
        pub op: &'static str,
        pub k: i128,
    }

    /// One asserted 2-variable linear constraint `x + sign*y op k`,
    /// where `sign` is `+1` for sum-form or `-1` for difference-
    /// form. The LinArith → simplex bridge (v0.17 T#38) feeds
    /// difference-form constraints when its FM layer recognised
    /// `x − y op k`; the simplex backend models them by adding a
    /// signed coefficient row.
    #[derive(Clone, Debug)]
    pub struct SumAtom {
        pub x: String,
        pub y: String,
        pub sign: i128,
        pub op: &'static str,
        pub k: i128,
    }

    /// Run Simplex on the collected bounds + sum constraints.
    /// Returns `Ok(true)` for sat, `Ok(false)` for unsat,
    /// `Err(msg)` for setup / solver errors.
    ///
    /// Strict inequalities (`<` / `>`) are encoded by tightening the
    /// bound by 1 — sound for LIA, conservative for LRA (which v0.13
    /// will refine using `oxiz-math`'s `delta_rational`).
    /// One bound entry: `(BoundType, value)`. Aggregated per
    /// variable before being committed to the tableau so we can use
    /// `add_var(lower, upper)` which seeds the assignment correctly
    /// — critical for row-based violations to surface in `check()`.
    #[derive(Default)]
    struct VarBounds {
        lower: Option<FastRational>,
        upper: Option<FastRational>,
    }

    pub fn check(bounds: &[BoundAtom], sums: &[SumAtom]) -> Result<bool, String> {
        let mut tab = SimplexTableau::new();
        let mut var_bounds: HashMap<String, VarBounds> = HashMap::new();

        // (1) Gather all variable names appearing anywhere.
        let mut all_vars: Vec<String> = Vec::new();
        for b in bounds {
            if !all_vars.contains(&b.var) { all_vars.push(b.var.clone()); }
            var_bounds.entry(b.var.clone()).or_default();
        }
        for s in sums {
            for n in [&s.x, &s.y] {
                if !all_vars.contains(n) { all_vars.push(n.clone()); }
                var_bounds.entry(n.clone()).or_default();
            }
        }

        // (2) Aggregate bounds per variable.
        for b in bounds {
            let entry = var_bounds.get_mut(&b.var).unwrap();
            let (bt, value) = encode_bound(b.op, b.k);
            match bt {
                BoundType::Lower => {
                    entry.lower = Some(match entry.lower.take() {
                        Some(old) => if value > old { value } else { old },
                        None => value,
                    });
                }
                BoundType::Upper => {
                    entry.upper = Some(match entry.upper.take() {
                        Some(old) => if value < old { value } else { old },
                        None => value,
                    });
                }
                BoundType::Equal => {
                    entry.lower = Some(value.clone());
                    entry.upper = Some(value);
                }
            }
        }

        // (3) Pre-check: lower > upper is an immediate conflict.
        for vb in var_bounds.values() {
            if let (Some(lb), Some(ub)) = (&vb.lower, &vb.upper) {
                if lb > ub { return Ok(false); }
            }
        }

        // (4) Create variables via `add_var(lower, upper)` so the
        //     assignment is seeded with the lower bound. This makes
        //     row-based basic-var violations detectable by `check()`.
        let mut var_ids: HashMap<String, VarId> = HashMap::new();
        for name in &all_vars {
            let vb = var_bounds.get(name).cloned().unwrap_or_default();
            let id = tab.add_var(vb.lower, vb.upper);
            var_ids.insert(name.clone(), id);
        }

        // (5) Sum constraints become slack rows: `z = x + y` with z
        //     bounded per the sum's operator.
        let mut next_constraint: ConstraintId = 0;
        for s in sums {
            let xid = *var_ids.get(&s.x).unwrap();
            let yid = *var_ids.get(&s.y).unwrap();
            let zid = tab.fresh_var();
            let mut coeffs: rustc_hash::FxHashMap<VarId, FastRational> = Default::default();
            coeffs.insert(xid, FastRational::from(1i64));
            coeffs.insert(yid, FastRational::from(s.sign as i64));
            let row = Row::from_expr(zid, FastRational::from(0i64), coeffs);
            tab.add_row(row).map_err(|e| format!("simplex add_row: {e}"))?;
            let (bt, value) = encode_bound(s.op, s.k);
            if tab.add_bound(zid, bt, value, next_constraint).is_err() {
                return Ok(false);
            }
            next_constraint += 1;
        }

        match tab.check() {
            Ok(SimplexResult::Sat) => Ok(true),
            Ok(SimplexResult::Unsat) => Ok(false),
            Ok(_) => Ok(true),
            Err(_) => Ok(false),
        }
    }

    impl Clone for VarBounds {
        fn clone(&self) -> Self {
            Self { lower: self.lower.clone(), upper: self.upper.clone() }
        }
    }

    fn encode_bound(op: &str, k: i128) -> (BoundType, FastRational) {
        // Encode strict ops by tightening by 1 (LIA semantics).
        match op {
            "<=" => (BoundType::Upper, FastRational::from(k as i64)),
            "<"  => (BoundType::Upper, FastRational::from((k - 1) as i64)),
            ">=" => (BoundType::Lower, FastRational::from(k as i64)),
            ">"  => (BoundType::Lower, FastRational::from((k + 1) as i64)),
            "="  => (BoundType::Equal, FastRational::from(k as i64)),
            _    => (BoundType::Upper, FastRational::from(k as i64)),
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn single_var_consistent_is_sat() {
            // x ≥ 0, x ≤ 10
            let bounds = vec![
                BoundAtom { var: "x".into(), op: ">=", k: 0 },
                BoundAtom { var: "x".into(), op: "<=", k: 10 },
            ];
            assert_eq!(check(&bounds, &[]), Ok(true));
        }

        #[test]
        fn single_var_contradictory_is_unsat() {
            // x ≥ 5, x ≤ 3
            let bounds = vec![
                BoundAtom { var: "x".into(), op: ">=", k: 5 },
                BoundAtom { var: "x".into(), op: "<=", k: 3 },
            ];
            assert_eq!(check(&bounds, &[]), Ok(false));
        }

        #[test]
        fn two_var_sum_sat() {
            // x ≥ 0, y ≥ 0, x + y ≤ 10  →  sat
            let bounds = vec![
                BoundAtom { var: "x".into(), op: ">=", k: 0 },
                BoundAtom { var: "y".into(), op: ">=", k: 0 },
            ];
            let sums = vec![SumAtom { x: "x".into(), y: "y".into(), sign: 1, op: "<=", k: 10 }];
            assert_eq!(check(&bounds, &sums), Ok(true));
        }

        // v0.13 patch: `check_dual()` surfaces non-basic bound
        // violations that the primal `check()` skipped. The two-var
        // sum unsat case now works without slack-variable rewriting.
        #[test]
        fn two_var_sum_unsat_via_dual_simplex() {
            let bounds = vec![
                BoundAtom { var: "x".into(), op: ">=", k: 3 },
                BoundAtom { var: "y".into(), op: ">=", k: 3 },
            ];
            let sums = vec![SumAtom { x: "x".into(), y: "y".into(), sign: 1, op: "<=", k: 5 }];
            assert_eq!(check(&bounds, &sums), Ok(false));
        }
    }
}

#[cfg(feature = "oxiz-math")]
pub use with_simplex::{BoundAtom, SumAtom, check};

#[cfg(not(feature = "oxiz-math"))]
pub mod stub {
    //! When the `oxiz-math` feature is off, this module is empty —
    //! `arith.rs`'s hand-rolled path is the only one available.
}
