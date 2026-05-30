//! v0.19 C.1 — bit-blasting BV expressions to SAT clauses.
//!
//! Lowers a BV equality `(= lhs rhs)` (width `w`) into a CNF set
//! over fresh boolean atoms `__bvb_<var>_<idx>` (one per bit per
//! BV variable). The resulting clauses can be solved directly by
//! [`crate::oxiz_backend::solve`] under the `oxiz` feature, or by
//! the built-in DPLL fallback.
//!
//! Supported BV constructors:
//!   • `bv<value>:<width>` literals (folded into [`Bit::Const`])
//!   • BV variables (each bit → a fresh boolean atom)
//!   • `bvand`, `bvor`, `bvxor`, `bvnot` (Tseitin-style fresh
//!     auxiliaries on mixed-atom operands; constant folds eagerly)
//!
//! `bvadd`, `bvsub`, `bvmul` are intentionally **out of scope** for
//! the first C.1 landing — ripple-carry adders need Tseitin chains
//! that interact with the engine's auxiliary-variable allocator
//! and that wiring lives in B.1 (DPLL(T) main loop). The eager
//! literal evaluator inside `Bv::reduce_binop` already handles the
//! all-constants case for those operators.
//!
//! Equality lowering ([`blast_eq_clauses`]) emits standard
//! biconditional clauses per bit pair, with constant short-circuits.
//!
//! Naming determinism: the same `(var_name, idx)` always maps to
//! the same boolean atom name — no global counter — so two
//! occurrences of the same BV variable in a single problem alias
//! correctly without an external symbol table.

use adsmt_core::{Term, Type};

use crate::cnf::{Clause, Lit};

/// A single blasted bit: either a known constant, or a boolean
/// atom (positive polarity by convention; negation lives on the
/// [`Lit`] side).
#[derive(Clone, Debug)]
pub enum Bit {
    Const(bool),
    /// Positive boolean atom. Use [`Bit::Negated`] for `¬a`.
    Atom(Term),
    /// Negation of a boolean atom.
    Negated(Term),
}

impl Bit {
    /// Convert this bit into a [`Lit`] over its atom, returning
    /// `None` when the bit is a constant (the caller decides how
    /// constants short-circuit each operator).
    pub fn into_lit(self) -> Option<Lit> {
        match self {
            Bit::Const(_) => None,
            Bit::Atom(a) => Some(Lit::pos(a)),
            Bit::Negated(a) => Some(Lit::neg(a)),
        }
    }

    fn negate(self) -> Self {
        match self {
            Bit::Const(b) => Bit::Const(!b),
            Bit::Atom(a) => Bit::Negated(a),
            Bit::Negated(a) => Bit::Atom(a),
        }
    }
}

/// Allocator for fresh Tseitin auxiliaries. The counter feeds a
/// deterministic atom name `__bva_<n>` so identical inputs
/// produce identical clause sets across runs.
#[derive(Default, Debug)]
pub struct BlastEnv {
    aux_counter: u64,
    clauses: Vec<Clause>,
}

impl BlastEnv {
    pub fn new() -> Self { Self::default() }

    fn fresh_aux(&mut self) -> Term {
        let n = self.aux_counter;
        self.aux_counter += 1;
        let name = format!("__bva_{n}");
        Term::var(name.as_str(), Type::bool_())
    }

    /// Drain the accumulated Tseitin clauses, leaving the env
    /// ready to reuse for the next equality.
    pub fn take_clauses(&mut self) -> Vec<Clause> {
        std::mem::take(&mut self.clauses)
    }

    /// Emit `out ⇔ (a ∧ b)` as three CNF clauses.
    fn tseitin_and(&mut self, a: Lit, b: Lit) -> Bit {
        let out = self.fresh_aux();
        let out_pos = Lit::pos(out.clone());
        let out_neg = Lit::neg(out.clone());
        // out → a:  (¬out ∨ a)
        self.clauses.push(vec![out_neg.clone(), a.clone()]);
        // out → b:  (¬out ∨ b)
        self.clauses.push(vec![out_neg, b.clone()]);
        // (a ∧ b) → out:  (¬a ∨ ¬b ∨ out)
        self.clauses.push(vec![a.negate(), b.negate(), out_pos]);
        Bit::Atom(out)
    }

    /// Emit `out ⇔ (a ∨ b)` as three CNF clauses.
    fn tseitin_or(&mut self, a: Lit, b: Lit) -> Bit {
        let out = self.fresh_aux();
        let out_pos = Lit::pos(out.clone());
        let out_neg = Lit::neg(out.clone());
        // a → out:  (¬a ∨ out)
        self.clauses.push(vec![a.clone().negate(), out_pos.clone()]);
        // b → out:  (¬b ∨ out)
        self.clauses.push(vec![b.clone().negate(), out_pos]);
        // out → (a ∨ b):  (¬out ∨ a ∨ b)
        self.clauses.push(vec![out_neg, a, b]);
        Bit::Atom(out)
    }

    /// Emit `out ⇔ (a ⊕ b)` as four CNF clauses.
    fn tseitin_xor(&mut self, a: Lit, b: Lit) -> Bit {
        let out = self.fresh_aux();
        let out_pos = Lit::pos(out.clone());
        let out_neg = Lit::neg(out.clone());
        // (a ∧ b) → ¬out:  (¬a ∨ ¬b ∨ ¬out)
        self.clauses
            .push(vec![a.clone().negate(), b.clone().negate(), out_neg.clone()]);
        // (¬a ∧ ¬b) → ¬out:  (a ∨ b ∨ ¬out)
        self.clauses.push(vec![a.clone(), b.clone(), out_neg]);
        // (a ∧ ¬b) → out:  (¬a ∨ b ∨ out)
        self.clauses.push(vec![a.clone().negate(), b.clone(), out_pos.clone()]);
        // (¬a ∧ b) → out:  (a ∨ ¬b ∨ out)
        self.clauses.push(vec![a, b.negate(), out_pos]);
        Bit::Atom(out)
    }

    fn and_bits(&mut self, a: Bit, b: Bit) -> Bit {
        match (a, b) {
            (Bit::Const(false), _) | (_, Bit::Const(false)) => Bit::Const(false),
            (Bit::Const(true), x) | (x, Bit::Const(true)) => x,
            (x, y) => {
                let la = x.into_lit().expect("non-const");
                let lb = y.into_lit().expect("non-const");
                self.tseitin_and(la, lb)
            }
        }
    }

    fn or_bits(&mut self, a: Bit, b: Bit) -> Bit {
        match (a, b) {
            (Bit::Const(true), _) | (_, Bit::Const(true)) => Bit::Const(true),
            (Bit::Const(false), x) | (x, Bit::Const(false)) => x,
            (x, y) => {
                let la = x.into_lit().expect("non-const");
                let lb = y.into_lit().expect("non-const");
                self.tseitin_or(la, lb)
            }
        }
    }

    fn xor_bits(&mut self, a: Bit, b: Bit) -> Bit {
        match (a, b) {
            (Bit::Const(c), x) | (x, Bit::Const(c)) => {
                if c { x.negate() } else { x }
            }
            (x, y) => {
                let la = x.into_lit().expect("non-const");
                let lb = y.into_lit().expect("non-const");
                self.tseitin_xor(la, lb)
            }
        }
    }
}

/// Bit name for the `idx`th bit of BV variable `var_name`.
/// Bit 0 is the LSB.
fn bit_var(var_name: &str, idx: u32) -> Term {
    let name = format!("__bvb_{var_name}_{idx}");
    Term::var(name.as_str(), Type::bool_())
}

/// Lower a BV [`Term`] of width `w` into a bit vector (LSB first).
/// Returns `None` if the term contains a BV operator we don't yet
/// blast (e.g. `bvadd` — kept as a `None` so callers fall back to
/// the existing partial-bit propagation in `adsmt-theory::bv`).
pub fn blast_term(t: &Term, w: u32, env: &mut BlastEnv) -> Option<Vec<Bit>> {
    if let Some((value, lit_w)) = t.dest_bv_lit() {
        if lit_w != w { return None; }
        return Some(lit_bits(value, w));
    }
    if let Term::Var(v) = t {
        return Some((0..w).map(|i| Bit::Atom(bit_var(&v.name, i))).collect());
    }
    // v0.23 C.1 — `bvnot` is a single-arg unary; handle before
    // the binop dispatch.
    if let Some((op, op_w, arg)) = t.dest_bv_unop() {
        if op_w != w { return None; }
        let arg_bits = blast_term(&arg, w, env)?;
        return match op.as_str() {
            "bvnot" => Some(arg_bits.into_iter().map(|b| b.negate()).collect()),
            _ => None,
        };
    }
    if let Some((op, op_w, lhs, rhs)) = t.dest_bv_binop() {
        if op_w != w { return None; }
        let lhs_bits = blast_term(&lhs, w, env)?;
        let rhs_bits = blast_term(&rhs, w, env)?;
        return match op.as_str() {
            "bvand" | "bvor" | "bvxor" => {
                let mut out = Vec::with_capacity(w as usize);
                for (a, b) in lhs_bits.into_iter().zip(rhs_bits) {
                    let bit = match op.as_str() {
                        "bvand" => env.and_bits(a, b),
                        "bvor"  => env.or_bits(a, b),
                        "bvxor" => env.xor_bits(a, b),
                        _ => unreachable!(),
                    };
                    out.push(bit);
                }
                Some(out)
            }
            // v0.21 C.1 — ripple-carry adder.
            //
            // s_i        = a_i ⊕ b_i ⊕ c_i
            // c_{i+1}    = maj(a_i, b_i, c_i)
            //            = (a_i ∧ b_i) ∨ (c_i ∧ (a_i ⊕ b_i))
            //
            // c_0 = false (no incoming carry); the final carry
            // c_w drops on the floor — width-modulo wraparound
            // matches the existing `Bv::reduce_binop` semantics
            // for all-literal `bvadd`.
            "bvadd" => Some(ripple_carry_add(lhs_bits, rhs_bits, env)),
            // v0.21 C.1 — subtraction via two's complement:
            //   a - b = a + (¬b) + 1
            //
            // Implemented inline: feed `¬b` into the adder and
            // set the initial carry `c_0 = true` so the `+1`
            // happens for free.
            "bvsub" => Some(ripple_carry_sub(lhs_bits, rhs_bits, env)),
            // v0.21 C.1 follow-up — shift-and-add multiplier.
            //
            // result = Σ_i (b_i ? (a << i)_masked : 0)
            //
            // Each partial product is an AND of `b_i` with the
            // appropriate `a` bit (cleared by a `Const(false)` for
            // bits below the shift). The partial products are
            // summed by reusing `ripple_carry_add`. Clause growth
            // is O(width²); on width 4 that's a handful of
            // Tseitin auxiliaries, well within what the built-in
            // CDCL fallback closes.
            "bvmul" => Some(shift_and_add_mul(lhs_bits, rhs_bits, env)),
            _ => None,
        };
    }
    None
}

/// v0.21 C.1 — ripple-carry adder.
fn ripple_carry_add(a_bits: Vec<Bit>, b_bits: Vec<Bit>, env: &mut BlastEnv) -> Vec<Bit> {
    let mut out = Vec::with_capacity(a_bits.len());
    let mut carry: Bit = Bit::Const(false);
    for (a, b) in a_bits.into_iter().zip(b_bits) {
        // s = a ⊕ b ⊕ c
        let a_xor_b = env.xor_bits(a.clone(), b.clone());
        let sum = env.xor_bits(a_xor_b.clone(), carry.clone());
        // c' = (a ∧ b) ∨ (c ∧ (a ⊕ b))
        let ab = env.and_bits(a, b);
        let c_axb = env.and_bits(carry, a_xor_b);
        let new_carry = env.or_bits(ab, c_axb);
        out.push(sum);
        carry = new_carry;
    }
    // Final carry dropped — width-modulo semantics.
    out
}

/// v0.21 C.1 follow-up — shift-and-add multiplier.
fn shift_and_add_mul(
    a_bits: Vec<Bit>,
    b_bits: Vec<Bit>,
    env: &mut BlastEnv,
) -> Vec<Bit> {
    let w = a_bits.len();
    let mut acc: Vec<Bit> = vec![Bit::Const(false); w];
    for i in 0..w {
        // Partial product i: a shifted left by i, AND'd with b[i].
        // Bits below position i are zero (shifted out).
        let mut partial: Vec<Bit> = Vec::with_capacity(w);
        for j in 0..w {
            if j < i {
                partial.push(Bit::Const(false));
            } else {
                let bit = env.and_bits(
                    b_bits[i].clone(),
                    a_bits[j - i].clone(),
                );
                partial.push(bit);
            }
        }
        acc = ripple_carry_add(acc, partial, env);
    }
    acc
}

/// v0.21 C.1 — subtraction via `a + (¬b) + 1`.
fn ripple_carry_sub(a_bits: Vec<Bit>, b_bits: Vec<Bit>, env: &mut BlastEnv) -> Vec<Bit> {
    let mut out = Vec::with_capacity(a_bits.len());
    let mut carry: Bit = Bit::Const(true); // initial +1
    for (a, b) in a_bits.into_iter().zip(b_bits) {
        // Bitwise-not on `b` becomes the second operand.
        let nb = b.negate();
        let a_xor_b = env.xor_bits(a.clone(), nb.clone());
        let diff = env.xor_bits(a_xor_b.clone(), carry.clone());
        let ab = env.and_bits(a, nb);
        let c_axb = env.and_bits(carry, a_xor_b);
        let new_carry = env.or_bits(ab, c_axb);
        out.push(diff);
        carry = new_carry;
    }
    out
}

fn lit_bits(value: u128, w: u32) -> Vec<Bit> {
    (0..w)
        .map(|i| {
            let bit = (value >> i) & 1 == 1;
            Bit::Const(bit)
        })
        .collect()
}

/// Lower `(= a b)` (both of width `w`) into CNF.
///
/// Returns the per-pair biconditional clauses plus any Tseitin
/// auxiliaries accumulated by `env`. A constant-vs-constant
/// disagreement on any bit produces a single empty clause — the
/// SAT solver will report Unsat without doing extra work.
pub fn blast_eq_clauses(
    a: &Term,
    b: &Term,
    w: u32,
    env: &mut BlastEnv,
) -> Option<Vec<Clause>> {
    let a_bits = blast_term(a, w, env)?;
    let b_bits = blast_term(b, w, env)?;
    if a_bits.len() != b_bits.len() {
        return None;
    }
    let mut out = env.take_clauses();
    for (i, (ai, bi)) in a_bits.into_iter().zip(b_bits).enumerate() {
        match (ai, bi) {
            (Bit::Const(x), Bit::Const(y)) => {
                if x != y {
                    out.push(Vec::new());
                    return Some(out);
                }
            }
            (Bit::Const(c), other) | (other, Bit::Const(c)) => {
                let other_lit = other.into_lit().expect("non-const branch");
                let unit = if c { other_lit } else { other_lit.negate() };
                out.push(vec![unit]);
            }
            (x, y) => {
                let lx = x.into_lit().expect("non-const");
                let ly = y.into_lit().expect("non-const");
                // (¬x ∨ y) ∧ (x ∨ ¬y)
                out.push(vec![lx.clone().negate(), ly.clone()]);
                out.push(vec![lx, ly.negate()]);
                let _ = i; // index unused; kept for future provenance
            }
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bool_solver::{dpll, BoolResult};

    fn solve_via_dpll(clauses: &[Clause]) -> BoolResult {
        dpll(clauses, 32)
    }

    #[test]
    fn equal_concrete_literals_yield_no_unit_unsat() {
        // bv 5:8 = bv 5:8 ⇒ all bits trivially equal ⇒ no clauses (Sat).
        let mut env = BlastEnv::new();
        let a = Term::bv_lit(5, 8);
        let b = Term::bv_lit(5, 8);
        let cs = blast_eq_clauses(&a, &b, 8, &mut env).unwrap();
        assert!(cs.is_empty(), "no constraints emitted for trivially equal literals");
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn distinct_literals_produce_empty_clause_unsat() {
        let mut env = BlastEnv::new();
        let a = Term::bv_lit(5, 8);
        let b = Term::bv_lit(7, 8);
        let cs = blast_eq_clauses(&a, &b, 8, &mut env).unwrap();
        assert_eq!(solve_via_dpll(&cs), BoolResult::Unsat);
    }

    #[test]
    fn var_equals_literal_emits_unit_per_bit() {
        // x:8 = 0b00000101 ⇒ 8 unit clauses fixing each bit.
        let mut env = BlastEnv::new();
        let x = Term::var("x", Term::bv_sort(8));
        let lit = Term::bv_lit(0b0000_0101, 8);
        let cs = blast_eq_clauses(&x, &lit, 8, &mut env).unwrap();
        assert_eq!(cs.len(), 8, "one unit per bit");
        // Bit 0 must be positive (1), bit 1 negative (0), bit 2 positive (1).
        assert!(cs[0][0].polarity);
        assert!(!cs[1][0].polarity);
        assert!(cs[2][0].polarity);
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn var_equality_emits_biconditional_per_bit() {
        // x:4 = y:4 ⇒ 4 bit-pairs × 2 implication clauses = 8 clauses.
        let mut env = BlastEnv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let y = Term::var("y", Term::bv_sort(4));
        let cs = blast_eq_clauses(&x, &y, 4, &mut env).unwrap();
        assert_eq!(cs.len(), 8);
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn bvxor_with_literal_zero_is_identity() {
        // (bvxor x 0) = lit ⇒ same constraint as x = lit.
        let mut env = BlastEnv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let xor = Term::mk_bvxor(x, Term::bv_lit(0, 4), 4).unwrap();
        let lit = Term::bv_lit(0b0011, 4);
        let cs = blast_eq_clauses(&xor, &lit, 4, &mut env).unwrap();
        // 4 bits, each Const(false) ⊕ Atom = Atom, then unit per bit.
        assert_eq!(cs.len(), 4);
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn bvand_var_var_emits_tseitin_aux() {
        // x:2 AND y:2 = 0b11:2  ⇒  forces x=11 AND y=11.
        let mut env = BlastEnv::new();
        let x = Term::var("x", Term::bv_sort(2));
        let y = Term::var("y", Term::bv_sort(2));
        let and = Term::mk_bvand(x, y, 2).unwrap();
        let lit = Term::bv_lit(0b11, 2);
        let cs = blast_eq_clauses(&and, &lit, 2, &mut env).unwrap();
        // For each bit: 3 Tseitin clauses (AND) + 1 unit fixing the
        // aux to true ⇒ 4 clauses per bit × 2 bits = 8 clauses.
        assert_eq!(cs.len(), 8);
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn bvand_var_literal_one_simplifies_to_identity() {
        // x:4 AND 0b1111:4 = 0b1010:4  ⇒  x = 0b1010
        // (all-ones AND-mask reduces each Tseitin to identity).
        let mut env = BlastEnv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let and = Term::mk_bvand(x, Term::bv_lit(0b1111, 4), 4).unwrap();
        let lit = Term::bv_lit(0b1010, 4);
        let cs = blast_eq_clauses(&and, &lit, 4, &mut env).unwrap();
        // All-ones mask short-circuits and_bits(Const(true), Atom) → Atom.
        // 4 units, no Tseitin aux.
        assert_eq!(cs.len(), 4);
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn bvor_var_literal_zero_simplifies_to_identity() {
        // x:4 OR 0:4 = 0b0101:4 ⇒ x = 0b0101 (no Tseitin).
        let mut env = BlastEnv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let or = Term::mk_bvor(x, Term::bv_lit(0, 4), 4).unwrap();
        let lit = Term::bv_lit(0b0101, 4);
        let cs = blast_eq_clauses(&or, &lit, 4, &mut env).unwrap();
        assert_eq!(cs.len(), 4);
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn bvxor_var_var_emits_tseitin_aux() {
        let mut env = BlastEnv::new();
        let x = Term::var("x", Term::bv_sort(2));
        let y = Term::var("y", Term::bv_sort(2));
        let xor = Term::mk_bvxor(x, y, 2).unwrap();
        let lit = Term::bv_lit(0b11, 2);
        let cs = blast_eq_clauses(&xor, &lit, 2, &mut env).unwrap();
        // Each bit: 4 Tseitin XOR clauses + 1 unit fixing aux=true
        // ⇒ 5 × 2 = 10 clauses.
        assert_eq!(cs.len(), 10);
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    // === v0.21 C.1 — ripple-carry arithmetic ===

    #[test]
    fn bvadd_concrete_operands_satisfiable_to_correct_sum() {
        // (3 + 5) = 8 over width 4 — all constants, no variables.
        // The blaster reduces every bit to Const, eq with the
        // expected literal emits no constraints (or trivially
        // satisfied), Sat.
        let mut env = BlastEnv::new();
        let three = Term::bv_lit(3, 4);
        let five = Term::bv_lit(5, 4);
        let add = Term::mk_bvadd(three, five, 4).unwrap();
        let lit = Term::bv_lit(8, 4);
        let cs = blast_eq_clauses(&add, &lit, 4, &mut env).unwrap();
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn bvadd_concrete_operands_wrong_sum_is_unsat() {
        let mut env = BlastEnv::new();
        let three = Term::bv_lit(3, 4);
        let five = Term::bv_lit(5, 4);
        let add = Term::mk_bvadd(three, five, 4).unwrap();
        let lit = Term::bv_lit(7, 4); // wrong
        let cs = blast_eq_clauses(&add, &lit, 4, &mut env).unwrap();
        assert_eq!(solve_via_dpll(&cs), BoolResult::Unsat);
    }

    #[test]
    fn bvadd_overflow_wraps_at_width_4() {
        // 0b1111 + 0b0010 = 0b0001 (mod 16) — high carry dropped.
        let mut env = BlastEnv::new();
        let a = Term::bv_lit(0b1111, 4);
        let b = Term::bv_lit(0b0010, 4);
        let add = Term::mk_bvadd(a, b, 4).unwrap();
        let lit = Term::bv_lit(0b0001, 4);
        let cs = blast_eq_clauses(&add, &lit, 4, &mut env).unwrap();
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn bvadd_with_variable_admits_solution() {
        // (x + 1) = 5 over width 4 — single satisfying x = 4.
        let mut env = BlastEnv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let add = Term::mk_bvadd(x, Term::bv_lit(1, 4), 4).unwrap();
        let lit = Term::bv_lit(5, 4);
        let cs = blast_eq_clauses(&add, &lit, 4, &mut env).unwrap();
        // bounded depth must be high enough to walk every bit
        // through the Tseitin chain.
        assert_eq!(crate::bool_solver::dpll(&cs, 64), BoolResult::Sat);
    }

    #[test]
    fn bvsub_concrete_operands_satisfiable_to_correct_diff() {
        // (8 - 3) = 5 over width 4.
        let mut env = BlastEnv::new();
        let a = Term::bv_lit(8, 4);
        let b = Term::bv_lit(3, 4);
        let sub = Term::mk_bvsub(a, b, 4).unwrap();
        let lit = Term::bv_lit(5, 4);
        let cs = blast_eq_clauses(&sub, &lit, 4, &mut env).unwrap();
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn bvsub_with_underflow_wraps() {
        // (3 - 8) = (3 + ¬8 + 1) = (3 + 0b0111 + 1) = 0b1011
        // over width 4. That's 11.
        let mut env = BlastEnv::new();
        let a = Term::bv_lit(3, 4);
        let b = Term::bv_lit(8, 4);
        let sub = Term::mk_bvsub(a, b, 4).unwrap();
        let lit = Term::bv_lit(11, 4);
        let cs = blast_eq_clauses(&sub, &lit, 4, &mut env).unwrap();
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn bvmul_concrete_operands_satisfiable_to_correct_product() {
        // (3 × 5) = 15 over width 4.
        let mut env = BlastEnv::new();
        let three = Term::bv_lit(3, 4);
        let five = Term::bv_lit(5, 4);
        let mul = Term::mk_bvmul(three, five, 4).unwrap();
        let lit = Term::bv_lit(15, 4);
        let cs = blast_eq_clauses(&mul, &lit, 4, &mut env).unwrap();
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn bvmul_concrete_operands_wrong_product_is_unsat() {
        let mut env = BlastEnv::new();
        let three = Term::bv_lit(3, 4);
        let five = Term::bv_lit(5, 4);
        let mul = Term::mk_bvmul(three, five, 4).unwrap();
        let lit = Term::bv_lit(7, 4);
        let cs = blast_eq_clauses(&mul, &lit, 4, &mut env).unwrap();
        assert_eq!(solve_via_dpll(&cs), BoolResult::Unsat);
    }

    #[test]
    fn bvmul_overflow_wraps_at_width_4() {
        // (7 × 3) = 21 = 0b10101 → low 4 bits = 0b0101 = 5.
        let mut env = BlastEnv::new();
        let a = Term::bv_lit(7, 4);
        let b = Term::bv_lit(3, 4);
        let mul = Term::mk_bvmul(a, b, 4).unwrap();
        let lit = Term::bv_lit(5, 4);
        let cs = blast_eq_clauses(&mul, &lit, 4, &mut env).unwrap();
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    // === v0.23 C.1 — bvnot ===

    #[test]
    fn bvnot_concrete_literal_is_bitwise_complement() {
        // (bvnot 0b0101) = 0b1010 over width 4.
        let mut env = BlastEnv::new();
        let arg = Term::bv_lit(0b0101, 4);
        let not_arg = Term::mk_bvnot(arg, 4).unwrap();
        let lit = Term::bv_lit(0b1010, 4);
        let cs = blast_eq_clauses(&not_arg, &lit, 4, &mut env).unwrap();
        assert_eq!(solve_via_dpll(&cs), BoolResult::Sat);
    }

    #[test]
    fn bvnot_wrong_complement_is_unsat() {
        let mut env = BlastEnv::new();
        let arg = Term::bv_lit(0b0101, 4);
        let not_arg = Term::mk_bvnot(arg, 4).unwrap();
        let lit = Term::bv_lit(0b1111, 4);
        let cs = blast_eq_clauses(&not_arg, &lit, 4, &mut env).unwrap();
        assert_eq!(solve_via_dpll(&cs), BoolResult::Unsat);
    }

    #[test]
    fn bvnot_with_variable_admits_solution() {
        // (bvnot x) = 0b1010 ⇒ x = 0b0101.
        let mut env = BlastEnv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let not_x = Term::mk_bvnot(x, 4).unwrap();
        let lit = Term::bv_lit(0b1010, 4);
        let cs = blast_eq_clauses(&not_x, &lit, 4, &mut env).unwrap();
        assert_eq!(crate::bool_solver::dpll(&cs, 32), BoolResult::Sat);
    }

    #[test]
    fn bvmul_with_variable_admits_solution() {
        // (x × 2) = 6 over width 4 — single satisfying x = 3.
        let mut env = BlastEnv::new();
        let x = Term::var("x", Term::bv_sort(4));
        let mul = Term::mk_bvmul(x, Term::bv_lit(2, 4), 4).unwrap();
        let lit = Term::bv_lit(6, 4);
        let cs = blast_eq_clauses(&mul, &lit, 4, &mut env).unwrap();
        // Multiplier shapes need a deeper DPLL budget than the
        // adder shapes — width 4 already creates a handful of
        // Tseitin auxiliaries per partial product.
        assert_eq!(crate::bool_solver::dpll(&cs, 128), BoolResult::Sat);
    }
}
