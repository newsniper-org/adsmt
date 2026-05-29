//! Bit-vector theory.
//!
//! Three-layer strategy:
//!
//! 1. **Literal evaluation** — concrete-operand binops fold to a
//!    literal at assert time (`bvand(0b1100, 0b1010) → 0b1000`).
//!    Identity / absorption rules also fire here.
//! 2. **Variable bindings** — `(= x literal)` records the value
//!    binding; conflict if a second, different literal is asserted
//!    against the same variable.
//! 3. **Bit-level fact propagation (bit-blasting v0.17)** — when one
//!    operand of a binop is a literal but the other is a variable,
//!    derive partial bit knowledge on the variable:
//!    - `(= (bvand x lit_m) lit_r)` ⇒ for each bit `i` where
//!      `lit_m[i] = 1`, x's bit `i` is fixed to `lit_r[i]`; where
//!      `lit_m[i] = 0`, the constraint requires `lit_r[i] = 0`
//!      (else conflict).
//!    - `(= (bvor  x lit_m) lit_r)` ⇒ symmetric: bits where
//!      `lit_m[i] = 0` fix `x[i] = lit_r[i]`; bits where
//!      `lit_m[i] = 1` require `lit_r[i] = 1`.
//!    - `(= (bvxor x lit_m) lit_r)` ⇒ XOR is bijective: every bit
//!      of `x` is fully determined by `x[i] = lit_m[i] ⊕ lit_r[i]`.
//!    Bit facts merge cumulatively; a fact conflicts when its
//!    known bits disagree with the stored fact at the same
//!    positions. Once `mask` covers every bit of the variable's
//!    width, the fact promotes itself into a full variable
//!    binding so downstream checks see it uniformly.
//!
//! Polite witness: `2^width` per BV sort.

use std::collections::HashMap;

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::{Term, Type};

use crate::trait_::{AssertResult, CheckResult, Literal, Theory};

/// Per-variable bit-level knowledge.
///
/// `mask` has bit `i` set when the corresponding bit of the
/// variable is known; `value` holds the known bit value (bits
/// outside `mask` are zero).
#[derive(Clone, Debug, Default)]
struct BitFacts {
    width: u32,
    mask: u128,
    value: u128,
}

#[derive(Default)]
pub struct Bv {
    /// Per-variable concrete BV value bindings observed via
    /// `(= x literal)` assertions.
    bindings: HashMap<String, (u128, u32)>,
    /// Per-variable accumulated bit-level facts from partial-literal
    /// binop constraints (the v0.17 bit-blasting layer).
    bit_facts: HashMap<String, BitFacts>,
    conflict: Option<TheoryWitness>,
    scope_stack: Vec<BvScope>,
}

#[derive(Clone, Debug, Default)]
struct BvScope {
    bindings: HashMap<String, (u128, u32)>,
    bit_facts: HashMap<String, BitFacts>,
}

impl Bv {
    pub fn new() -> Self { Self::default() }

    /// All-ones mask at `width`. Saturates at `u128::MAX` once
    /// `width >= 128`.
    fn width_mask(width: u32) -> u128 {
        if width >= 128 { u128::MAX } else { (1u128 << width) - 1 }
    }

    /// Merge a `(mask, value)` bit-fact into the variable's record.
    /// Returns a witness when the new fact disagrees with the
    /// previously known bits, or when promoting a fully-known
    /// variable to a binding contradicts an existing binding.
    fn record_bit_facts(
        &mut self,
        var: &str,
        width: u32,
        mask: u128,
        value: u128,
    ) -> Option<TheoryWitness> {
        let mask = mask & Self::width_mask(width);
        let value = value & mask;
        if mask == 0 { return None; }

        // Cross-check against an existing full binding first.
        if let Some(&(bound_v, bound_w)) = self.bindings.get(var) {
            if bound_w != width {
                return Some(TheoryWitness::Opaque {
                    kind: "BV".into(),
                    notes: format!(
                        "width mismatch on {var}: bit-fact at w={width} vs binding at w={bound_w}"
                    ),
                });
            }
            let bound_at_mask = bound_v & mask;
            if bound_at_mask != value {
                return Some(TheoryWitness::Opaque {
                    kind: "BV".into(),
                    notes: format!(
                        "bit-fact conflict on {var}: existing binding bv:{bound_v}:{bound_w} disagrees with mask=0x{mask:x} value=0x{value:x}"
                    ),
                });
            }
        }

        let entry = self.bit_facts.entry(var.to_string())
            .or_insert(BitFacts { width, mask: 0, value: 0 });
        if entry.width != width {
            return Some(TheoryWitness::Opaque {
                kind: "BV".into(),
                notes: format!(
                    "width mismatch on {var}: bit-fact at w={width} vs prior facts at w={}",
                    entry.width
                ),
            });
        }
        // Disagreement on already-known bits.
        let overlap = entry.mask & mask;
        if overlap != 0 && (entry.value & overlap) != (value & overlap) {
            return Some(TheoryWitness::Opaque {
                kind: "BV".into(),
                notes: format!(
                    "bit-fact conflict on {var}: prior 0x{:x} vs new 0x{value:x} on overlap mask 0x{overlap:x}",
                    entry.value
                ),
            });
        }
        entry.mask |= mask;
        entry.value = (entry.value & !mask) | (value & mask);

        // Promote to a full binding once every bit is known.
        if entry.mask == Self::width_mask(width) {
            let final_value = entry.value;
            if let Some(&(bound_v, bound_w)) = self.bindings.get(var) {
                if bound_w != width || bound_v != final_value {
                    return Some(TheoryWitness::Opaque {
                        kind: "BV".into(),
                        notes: format!(
                            "bit-fact-driven promotion conflicts existing binding on {var}: bv:{bound_v}:{bound_w} vs derived bv:{final_value}:{width}"
                        ),
                    });
                }
            } else {
                self.bindings.insert(var.to_string(), (final_value, width));
            }
        }
        None
    }

    /// Extract bit-level facts from a binop equality where exactly
    /// one side of the binop is a variable and the other a literal,
    /// AND the right-hand side of the equality is a literal.
    /// Returns the variable name and the derived `(mask, value)`
    /// pair, plus an immediate witness if the constraint is
    /// structurally infeasible.
    fn binop_eq_facts(
        op: &str,
        width: u32,
        binop_lhs: &Term,
        binop_rhs: &Term,
        eq_rhs_lit: u128,
    ) -> Result<Option<(String, u128, u128)>, TheoryWitness> {
        let mask_all = Self::width_mask(width);
        let lhs_lit = binop_lhs.dest_bv_lit().map(|(v, _)| v);
        let rhs_lit = binop_rhs.dest_bv_lit().map(|(v, _)| v);
        let lhs_var = if let Term::Var(v) = binop_lhs { Some(v.name.clone()) } else { None };
        let rhs_var = if let Term::Var(v) = binop_rhs { Some(v.name.clone()) } else { None };

        // Resolve which side is the variable and which is the literal.
        let (var, lit_m) = match (lhs_var, rhs_lit, rhs_var, lhs_lit) {
            (Some(v), Some(m), _, _) => (v, m),
            (_, _, Some(v), Some(m)) => (v, m),
            _ => return Ok(None),
        };
        let eq_rhs_lit = eq_rhs_lit & mask_all;
        let lit_m = lit_m & mask_all;

        match op {
            "bvand" => {
                // Bits where lit_m=0 force eq_rhs bit to 0.
                let zero_mask = !lit_m & mask_all;
                if (eq_rhs_lit & zero_mask) != 0 {
                    return Err(TheoryWitness::Opaque {
                        kind: "BV".into(),
                        notes: format!(
                            "bvand contradiction: (bvand {var} 0x{lit_m:x}) = 0x{eq_rhs_lit:x} has a 1-bit where the mask is 0"
                        ),
                    });
                }
                // For bits where lit_m=1, x_bit = eq_rhs_bit.
                Ok(Some((var, lit_m, eq_rhs_lit & lit_m)))
            }
            "bvor" => {
                // Bits where lit_m=1 force eq_rhs bit to 1.
                let one_mask = lit_m;
                if (eq_rhs_lit & one_mask) != one_mask {
                    return Err(TheoryWitness::Opaque {
                        kind: "BV".into(),
                        notes: format!(
                            "bvor contradiction: (bvor {var} 0x{lit_m:x}) = 0x{eq_rhs_lit:x} has a 0-bit where the mask is 1"
                        ),
                    });
                }
                // For bits where lit_m=0, x_bit = eq_rhs_bit.
                let zero_mask = !lit_m & mask_all;
                Ok(Some((var, zero_mask, eq_rhs_lit & zero_mask)))
            }
            "bvxor" => {
                // XOR is bijective: x is fully determined by lit_m XOR eq_rhs.
                Ok(Some((var, mask_all, (lit_m ^ eq_rhs_lit) & mask_all)))
            }
            _ => Ok(None),
        }
    }

    /// If `t` is a BV binop applied to two literals, evaluate it and
    /// return the resulting literal. v0.9 also handles
    /// identity/absorption laws when one operand is a literal:
    /// `bvand x 0 = 0`, `bvand x (all-ones) = x`,
    /// `bvor  x 0 = x`, `bvor  x (all-ones) = all-ones`,
    /// `bvxor x 0 = x`,
    /// `bvadd x 0 = x`, `bvsub x 0 = x`, `bvmul x 0 = 0`, `bvmul x 1 = x`.
    fn reduce_binop(t: &Term) -> Term {
        let Some((op, w, lhs, rhs)) = t.dest_bv_binop() else { return t.clone(); };
        let mask: u128 = if w >= 128 { u128::MAX } else { (1u128 << w) - 1 };

        // Both-literal: full evaluation.
        if let (Some((va, _)), Some((vb, _))) = (lhs.dest_bv_lit(), rhs.dest_bv_lit()) {
            let result = match op.as_str() {
                "bvand" => (va & vb) & mask,
                "bvor"  => (va | vb) & mask,
                "bvxor" => (va ^ vb) & mask,
                "bvadd" => va.wrapping_add(vb) & mask,
                "bvsub" => va.wrapping_sub(vb) & mask,
                "bvmul" => va.wrapping_mul(vb) & mask,
                _ => return t.clone(),
            };
            return Term::bv_lit(result, w);
        }

        // Single-literal simplifications (v0.9 partial bit-blasting).
        let lhs_lit = lhs.dest_bv_lit().map(|(v, _)| v);
        let rhs_lit = rhs.dest_bv_lit().map(|(v, _)| v);
        let all_ones = mask;

        match (op.as_str(), lhs_lit, rhs_lit) {
            // identity / absorption with `rhs` literal
            ("bvand", _, Some(0)) | ("bvmul", _, Some(0)) => return Term::bv_lit(0, w),
            ("bvand", _, Some(v)) if v == all_ones => return lhs,
            ("bvor",  _, Some(0)) | ("bvadd", _, Some(0))
                | ("bvsub", _, Some(0)) | ("bvxor", _, Some(0)) => return lhs,
            ("bvor",  _, Some(v)) if v == all_ones => return Term::bv_lit(all_ones, w),
            ("bvmul", _, Some(1)) => return lhs,
            // identity / absorption with `lhs` literal (commutative ops only)
            ("bvand", Some(0), _) | ("bvmul", Some(0), _) => return Term::bv_lit(0, w),
            ("bvand", Some(v), _) if v == all_ones => return rhs,
            ("bvor",  Some(0), _) | ("bvadd", Some(0), _) | ("bvxor", Some(0), _) => return rhs,
            ("bvor",  Some(v), _) if v == all_ones => return Term::bv_lit(all_ones, w),
            ("bvmul", Some(1), _) => return rhs,
            _ => {}
        }
        t.clone()
    }
}

impl Theory for Bv {
    fn name(&self) -> &'static str { "BV" }

    fn handles_sort(&self, ty: &Type) -> bool {
        Term::bv_sort_width(ty).is_some()
    }

    fn assert(&mut self, lit: Literal) -> AssertResult {
        // Only equality literals matter at v0.5/v0.7 alpha.
        let Some((a, b)) = lit.term.dest_eq() else {
            return AssertResult::Ignored;
        };
        // v0.7: if one side is a BV binop applied to two literals,
        // evaluate it and rewrite to a literal equality. Both sides
        // can independently reduce.
        let a = Self::reduce_binop(&a);
        let b = Self::reduce_binop(&b);
        let lit_a = a.dest_bv_lit();
        let lit_b = b.dest_bv_lit();

        // v0.17 bit-blasting: when one side is a binop with mixed
        // var/literal operands and the other side is a literal,
        // derive partial bit-level knowledge on the variable. Only
        // fires on positive equality; the negated form would need
        // the disjunction of single-bit conflicts and is gated for
        // the SAT-backed cycle.
        if lit.polarity {
            for (bin_side, eq_other) in [(&a, &b), (&b, &a)] {
                let Some((op, w, bl, br)) = bin_side.dest_bv_binop() else { continue; };
                let Some((eq_v, eq_w)) = eq_other.dest_bv_lit() else { continue; };
                if eq_w != w { continue; }
                match Self::binop_eq_facts(&op, w, &bl, &br, eq_v) {
                    Err(witness) => {
                        self.conflict = Some(witness.clone());
                        return AssertResult::Conflict { witness };
                    }
                    Ok(Some((var, mask, value))) => {
                        if let Some(witness) =
                            self.record_bit_facts(&var, w, mask, value)
                        {
                            self.conflict = Some(witness.clone());
                            return AssertResult::Conflict { witness };
                        }
                        return AssertResult::Accepted;
                    }
                    Ok(None) => {}
                }
            }
        }

        match (lit_a, lit_b, lit.polarity) {
            // Two concrete literals, asserted equal.
            (Some((va, wa)), Some((vb, wb)), true) => {
                if wa != wb || va != vb {
                    let w = TheoryWitness::Opaque {
                        kind: "BV".into(),
                        notes: format!("distinct literals asserted equal: bv:{va}:{wa} = bv:{vb}:{wb}"),
                    };
                    self.conflict = Some(w.clone());
                    return AssertResult::Conflict { witness: w };
                }
                AssertResult::Accepted
            }
            // Two literals asserted disequal — only unsat when they're identical.
            (Some((va, wa)), Some((vb, wb)), false) => {
                if wa == wb && va == vb {
                    let w = TheoryWitness::Opaque {
                        kind: "BV".into(),
                        notes: format!("same literal asserted disequal: bv:{va}:{wa}"),
                    };
                    self.conflict = Some(w.clone());
                    return AssertResult::Conflict { witness: w };
                }
                AssertResult::Accepted
            }
            // Variable = literal: bind. Conflict if previously bound to a different value.
            (None, Some((v, w)), true) | (Some((v, w)), None, true) => {
                let var_name = if lit_a.is_none() { a.to_string() } else { b.to_string() };
                if let Some((prev_v, prev_w)) = self.bindings.get(&var_name) {
                    if *prev_w != w || *prev_v != v {
                        let cw = TheoryWitness::Opaque {
                            kind: "BV".into(),
                            notes: format!(
                                "variable {var_name} bound to bv:{prev_v}:{prev_w} and bv:{v}:{w}"
                            ),
                        };
                        self.conflict = Some(cw.clone());
                        return AssertResult::Conflict { witness: cw };
                    }
                } else {
                    self.bindings.insert(var_name, (v, w));
                }
                AssertResult::Accepted
            }
            _ => AssertResult::Ignored,
        }
    }

    fn check(&mut self) -> CheckResult {
        match &self.conflict {
            Some(w) => CheckResult::Unsat { witness: w.clone() },
            None => CheckResult::Sat,
        }
    }

    fn explain(&self) -> Option<TheoryWitness> { self.conflict.clone() }

    fn cardinality_witness(&self, sort: &Type) -> PoliteWitness {
        let width = Term::bv_sort_width(sort);
        let bound = width.and_then(|w| if w < 64 { Some(1u64 << w) } else { None });
        PoliteWitness { sort: format!("{sort}"), upper_bound: bound }
    }

    fn push(&mut self) {
        self.scope_stack.push(BvScope {
            bindings: self.bindings.clone(),
            bit_facts: self.bit_facts.clone(),
        });
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if let Some(prev) = self.scope_stack.pop() {
                self.bindings = prev.bindings;
                self.bit_facts = prev.bit_facts;
            }
        }
        self.conflict = None;
    }

    fn reset(&mut self) {
        self.bindings.clear();
        self.bit_facts.clear();
        self.conflict = None;
        self.scope_stack.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Term;

    #[test]
    fn distinct_literals_assert_equal_is_unsat() {
        let mut bv = Bv::new();
        let eq = Term::mk_eq(Term::bv_lit(5, 8), Term::bv_lit(7, 8)).unwrap();
        assert!(matches!(bv.assert(Literal::positive(eq).unwrap()), AssertResult::Conflict { .. }));
        assert!(matches!(bv.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn same_literal_assert_disequal_is_unsat() {
        let mut bv = Bv::new();
        let eq = Term::mk_eq(Term::bv_lit(5, 8), Term::bv_lit(5, 8)).unwrap();
        assert!(matches!(bv.assert(Literal::negative(eq).unwrap()), AssertResult::Conflict { .. }));
    }

    #[test]
    fn variable_bound_to_two_values_is_unsat() {
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(8));
        let eq1 = Term::mk_eq(x.clone(), Term::bv_lit(5, 8)).unwrap();
        let eq2 = Term::mk_eq(x, Term::bv_lit(7, 8)).unwrap();
        assert!(matches!(bv.assert(Literal::positive(eq1).unwrap()), AssertResult::Accepted));
        assert!(matches!(bv.assert(Literal::positive(eq2).unwrap()), AssertResult::Conflict { .. }));
    }

    #[test]
    fn cardinality_witness_is_two_to_the_width() {
        let bv = Bv::new();
        let w = bv.cardinality_witness(&Term::bv_sort(8));
        assert_eq!(w.upper_bound, Some(256));
        let w16 = bv.cardinality_witness(&Term::bv_sort(16));
        assert_eq!(w16.upper_bound, Some(65536));
    }

    #[test]
    fn bvand_literal_reduces_correctly() {
        // bvand(0b1100, 0b1010) = 0b1000 (width 4)
        let mut bv = Bv::new();
        let lhs = Term::mk_bvand(Term::bv_lit(0b1100, 4), Term::bv_lit(0b1010, 4), 4).unwrap();
        let eq = Term::mk_eq(lhs, Term::bv_lit(0b1000, 4)).unwrap();
        assert!(matches!(bv.assert(Literal::positive(eq).unwrap()), AssertResult::Accepted));
    }

    #[test]
    fn bvand_literal_wrong_result_is_unsat() {
        let mut bv = Bv::new();
        let lhs = Term::mk_bvand(Term::bv_lit(0b1100, 4), Term::bv_lit(0b1010, 4), 4).unwrap();
        let eq = Term::mk_eq(lhs, Term::bv_lit(0b1111, 4)).unwrap();
        assert!(matches!(bv.assert(Literal::positive(eq).unwrap()), AssertResult::Conflict { .. }));
    }

    #[test]
    fn bvand_absorbs_zero() {
        // bvand(x, 0) = 0 — eq with anything but 0 is unsat.
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(8));
        let conj = Term::mk_bvand(x, Term::bv_lit(0, 8), 8).unwrap();
        let eq_zero = Term::mk_eq(conj.clone(), Term::bv_lit(0, 8)).unwrap();
        assert!(matches!(bv.assert(Literal::positive(eq_zero).unwrap()), AssertResult::Accepted));
        let eq_nonzero = Term::mk_eq(conj, Term::bv_lit(5, 8)).unwrap();
        assert!(matches!(bv.assert(Literal::positive(eq_nonzero).unwrap()), AssertResult::Conflict { .. }));
    }

    #[test]
    fn bvor_with_all_ones_yields_all_ones() {
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(8));
        let disj = Term::mk_bvor(x, Term::bv_lit(0xFF, 8), 8).unwrap();
        let eq = Term::mk_eq(disj, Term::bv_lit(0xFF, 8)).unwrap();
        assert!(matches!(bv.assert(Literal::positive(eq).unwrap()), AssertResult::Accepted));
    }

    #[test]
    fn bvxor_with_zero_is_identity() {
        // bvxor(x, 0) = x, so `(bvxor x 0) = (bv 5 8)` implies x = 5.
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(8));
        let xor = Term::mk_bvxor(x.clone(), Term::bv_lit(0, 8), 8).unwrap();
        let eq = Term::mk_eq(xor, Term::bv_lit(5, 8)).unwrap();
        assert!(matches!(bv.assert(Literal::positive(eq).unwrap()), AssertResult::Accepted));
        // Conflicting binding to a different value:
        let eq2 = Term::mk_eq(x, Term::bv_lit(7, 8)).unwrap();
        assert!(matches!(bv.assert(Literal::positive(eq2).unwrap()), AssertResult::Conflict { .. }));
    }

    #[test]
    fn bvadd_with_overflow_wraps_at_width() {
        let mut bv = Bv::new();
        // 0xFF + 0x02 in width 8 = 0x01 (wraps)
        let lhs = Term::mk_bvadd(Term::bv_lit(0xFF, 8), Term::bv_lit(0x02, 8), 8).unwrap();
        let eq = Term::mk_eq(lhs, Term::bv_lit(0x01, 8)).unwrap();
        assert!(matches!(bv.assert(Literal::positive(eq).unwrap()), AssertResult::Accepted));
    }

    // === v0.17 bit-blasting tests ===

    #[test]
    fn bvand_partial_mask_fixes_some_bits_of_x() {
        // (bvand x 0b1010) = 0b1000 ⇒ x bit 3 known to 1, bit 1 known to 0.
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(8));
        let and = Term::mk_bvand(x, Term::bv_lit(0b1010, 8), 8).unwrap();
        let eq = Term::mk_eq(and, Term::bv_lit(0b1000, 8)).unwrap();
        assert!(matches!(
            bv.assert(Literal::positive(eq).unwrap()),
            AssertResult::Accepted
        ));
        // No contradiction yet — x's other bits are free.
        assert!(matches!(bv.check(), CheckResult::Sat));
    }

    #[test]
    fn bvand_partial_mask_contradicts_one_bit_outside_mask() {
        // (bvand x 0b0001) = 0b0010 ⇒ result bit 1 is 1 outside mask ⇒ unsat.
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let and = Term::mk_bvand(x, Term::bv_lit(0b0001, 4), 4).unwrap();
        let eq = Term::mk_eq(and, Term::bv_lit(0b0010, 4)).unwrap();
        assert!(matches!(
            bv.assert(Literal::positive(eq).unwrap()),
            AssertResult::Conflict { .. }
        ));
    }

    #[test]
    fn bvor_partial_mask_fixes_zero_bits_of_x() {
        // (bvor x 0b0011) = 0b1011 ⇒ x bits 2,3 = 1,0; bits 0,1 forced 1 in result (OK).
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let or = Term::mk_bvor(x, Term::bv_lit(0b0011, 4), 4).unwrap();
        let eq = Term::mk_eq(or, Term::bv_lit(0b1011, 4)).unwrap();
        assert!(matches!(
            bv.assert(Literal::positive(eq).unwrap()),
            AssertResult::Accepted
        ));
    }

    #[test]
    fn bvor_partial_mask_contradicts_required_one_bit() {
        // (bvor x 0b0001) = 0b0000 ⇒ result bit 0 must be 1 ⇒ unsat.
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let or = Term::mk_bvor(x, Term::bv_lit(0b0001, 4), 4).unwrap();
        let eq = Term::mk_eq(or, Term::bv_lit(0b0000, 4)).unwrap();
        assert!(matches!(
            bv.assert(Literal::positive(eq).unwrap()),
            AssertResult::Conflict { .. }
        ));
    }

    #[test]
    fn bvxor_fully_determines_x() {
        // (bvxor x 0b1100) = 0b1010 ⇒ x = 0b0110. Then x = 0b0101 ⇒ conflict.
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let xor = Term::mk_bvxor(x.clone(), Term::bv_lit(0b1100, 4), 4).unwrap();
        let eq1 = Term::mk_eq(xor, Term::bv_lit(0b1010, 4)).unwrap();
        assert!(matches!(
            bv.assert(Literal::positive(eq1).unwrap()),
            AssertResult::Accepted
        ));
        // Bit-blasting fully determined x; conflicting direct binding is rejected.
        let eq2 = Term::mk_eq(x, Term::bv_lit(0b0101, 4)).unwrap();
        assert!(matches!(
            bv.assert(Literal::positive(eq2).unwrap()),
            AssertResult::Conflict { .. }
        ));
    }

    #[test]
    fn bit_fact_conflict_across_two_constraints() {
        // (bvand x 0b1100) = 0b1000 ⇒ x bit 3 = 1, bit 2 = 0.
        // (bvand x 0b1000) = 0b0000 ⇒ x bit 3 = 0. Contradicts bit 3 = 1.
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let and1 = Term::mk_bvand(x.clone(), Term::bv_lit(0b1100, 4), 4).unwrap();
        let eq1 = Term::mk_eq(and1, Term::bv_lit(0b1000, 4)).unwrap();
        assert!(matches!(
            bv.assert(Literal::positive(eq1).unwrap()),
            AssertResult::Accepted
        ));
        let and2 = Term::mk_bvand(x, Term::bv_lit(0b1000, 4), 4).unwrap();
        let eq2 = Term::mk_eq(and2, Term::bv_lit(0b0000, 4)).unwrap();
        assert!(matches!(
            bv.assert(Literal::positive(eq2).unwrap()),
            AssertResult::Conflict { .. }
        ));
    }

    #[test]
    fn bit_facts_pop_restores_state() {
        // Establish a fact, push, accumulate a conflicting derived fact,
        // pop, verify state restored.
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let and = Term::mk_bvand(x.clone(), Term::bv_lit(0b1010, 4), 4).unwrap();
        let eq = Term::mk_eq(and, Term::bv_lit(0b1000, 4)).unwrap();
        assert!(matches!(
            bv.assert(Literal::positive(eq).unwrap()),
            AssertResult::Accepted
        ));
        bv.push();
        // Derive bit 3 = 0, conflicting with prior bit 3 = 1.
        let and2 = Term::mk_bvand(x.clone(), Term::bv_lit(0b1000, 4), 4).unwrap();
        let eq2 = Term::mk_eq(and2, Term::bv_lit(0b0000, 4)).unwrap();
        assert!(matches!(
            bv.assert(Literal::positive(eq2).unwrap()),
            AssertResult::Conflict { .. }
        ));
        bv.pop(1);
        // After pop: original facts still hold; bit 3 = 1 is unchanged.
        // Asserting bit 3 = 1 directly via (bvand x 0b1000) = 0b1000 is OK.
        let and3 = Term::mk_bvand(x, Term::bv_lit(0b1000, 4), 4).unwrap();
        let eq3 = Term::mk_eq(and3, Term::bv_lit(0b1000, 4)).unwrap();
        assert!(matches!(
            bv.assert(Literal::positive(eq3).unwrap()),
            AssertResult::Accepted
        ));
    }

    #[test]
    fn push_pop_restores_bindings() {
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(8));
        bv.assert(Literal::positive(Term::mk_eq(x.clone(), Term::bv_lit(5, 8)).unwrap()).unwrap());
        bv.push();
        bv.assert(Literal::positive(Term::mk_eq(x.clone(), Term::bv_lit(7, 8)).unwrap()).unwrap());
        assert!(matches!(bv.check(), CheckResult::Unsat { .. }));
        bv.pop(1);
        assert!(matches!(bv.check(), CheckResult::Sat));
    }
}
