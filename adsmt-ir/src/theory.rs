//! The **arithmetic theory prelude** — the kernel-side `Int`/`Real`/`Nat`/`WNat`
//! sorts, their arithmetic/comparison operators, the inter-sort injections, and
//! the number-theory built-ins (`pow`/`mod`/`odd`/`prime`), all installed into an
//! [`Env`] as **`open` postulates**.
//!
//! ## Trust boundary
//!
//! Everything here is [`Modality::Open`](crate::Modality::Open) (via
//! [`postulate`](crate::postulate)) — *opaque to the kernel*. The kernel only
//! **type-checks** arithmetic terms (so `Int.add` applied to two `Int`s is an
//! `Int`, `Int.lt` is a `Prop`, …); it never *decides* arithmetic
//! (`2 + 2 = 4` is the **solver's** job, downstream of the CIC→HOL lowering).
//! So adding this prelude grows **no trusted kernel surface** — there is no new
//! `TermKind`, no new typing rule, no new conversion rule; literals are
//! face-postulated opaque constants. A bug here can only mis-type a term (caught
//! by the kernel) — never manufacture an arithmetic fact.
//!
//! ## The strict `Nat` / `WNat` distinction
//!
//! `Nat = {1, 2, 3, …}` (0 **excluded**) and `WNat = {0, 1, 2, …}` (0
//! **included**) are **distinct sorts** — NOT kernel subtypes (the kernel has no
//! subtyping). The `⊂` chain `Nat ⊂ WNat ⊂ Int ⊂ Real` is realised by the
//! **explicit total injections** [`NAT2WNAT`], [`WNAT2INT`], [`INT2REAL`] (and
//! the convenience composites [`NAT2INT`], [`WNAT2REAL`], [`NAT2REAL`]) that a
//! face inserts where a value of a wider sort is expected — there is no silent
//! coercion. This is exactly the precision a postulate library needs (choosing
//! `Nat` vs `WNat` is the soundness boundary for e.g. Fermat's Last Theorem).
//!
//! See `~/AD1/docs/design/LUKB_SUCCESSOR_SURFACE.md` (§7, §9) for the surface
//! design this backs.

use crate::{Env, Modality, Term, TypeError, postulate};

// ── sort names ──────────────────────────────────────────────────────────
pub const INT: &str = "Int";
pub const REAL: &str = "Real";
pub const NAT: &str = "Nat";
pub const WNAT: &str = "WNat";

// ── injection names (no silent coercion; a face inserts these) ───────────
pub const NAT2WNAT: &str = "nat2wnat";
pub const WNAT2INT: &str = "wnat2int";
pub const INT2REAL: &str = "int2real";
/// Composite convenience injections (postulated directly so a face need not
/// build the composition term).
pub const NAT2INT: &str = "nat2int";
pub const WNAT2REAL: &str = "wnat2real";
pub const NAT2REAL: &str = "nat2real";

// ── Int operators ───────────────────────────────────────────────────────
pub const INT_ADD: &str = "Int.add";
pub const INT_SUB: &str = "Int.sub";
pub const INT_MUL: &str = "Int.mul";
pub const INT_NEG: &str = "Int.neg";
pub const INT_DIV: &str = "Int.div"; // Euclidean (SMT-LIB `div`)
pub const INT_MOD: &str = "Int.mod"; // Euclidean (SMT-LIB `mod`)
pub const INT_ABS: &str = "Int.abs";
pub const INT_LT: &str = "Int.lt";
pub const INT_LE: &str = "Int.le";
pub const INT_GT: &str = "Int.gt";
pub const INT_GE: &str = "Int.ge";

// ── Real operators ──────────────────────────────────────────────────────
pub const REAL_ADD: &str = "Real.add";
pub const REAL_SUB: &str = "Real.sub";
pub const REAL_MUL: &str = "Real.mul";
pub const REAL_NEG: &str = "Real.neg";
pub const REAL_DIV: &str = "Real.div"; // real division `/`
pub const REAL_LT: &str = "Real.lt";
pub const REAL_LE: &str = "Real.le";
pub const REAL_GT: &str = "Real.gt";
pub const REAL_GE: &str = "Real.ge";

// ── number-theory built-ins (lu-kb-successor surface; perf primitives) ──
pub const POW: &str = "pow"; // pow : Int → Int → Int  (base^exp; domain meaning = solver's)
pub const ODD: &str = "odd"; // odd : Int → Prop
pub const PRIME: &str = "prime"; // prime : Int → Prop

// helper type constructors used across both installers.
fn binop(t: Term) -> Term {
    Term::arrow(t.clone(), Term::arrow(t.clone(), t))
}
fn rel(t: Term) -> Term {
    Term::arrow(t.clone(), Term::arrow(t, Term::prop()))
}
fn un(t: Term) -> Term {
    Term::arrow(t.clone(), t)
}

/// Install **only the SMT-LIB-standard arithmetic** — the `Int` and `Real`
/// sorts, their operators, and the `int2real` injection. This is what the
/// SMT-LIB face installs: it must NOT reserve `Nat`/`WNat`/`pow`/`odd`/`prime`,
/// which are **not** SMT-LIB sorts/symbols (a user may legitimately
/// `(declare-datatype Nat …)`). All postulates are `open`. Errors with
/// [`TypeError::DuplicateConst`] if a name is already taken.
pub fn install_int_real(env: &mut Env) -> Result<(), TypeError> {
    let int = || Term::cnst(INT);
    let real = || Term::cnst(REAL);

    postulate(env, INT, Term::type_(0))?;
    postulate(env, REAL, Term::type_(0))?;
    postulate(env, INT2REAL, Term::arrow(int(), real()))?;

    for op in [INT_ADD, INT_SUB, INT_MUL, INT_DIV, INT_MOD] {
        postulate(env, op, binop(int()))?;
    }
    postulate(env, INT_NEG, un(int()))?;
    postulate(env, INT_ABS, un(int()))?;
    for op in [INT_LT, INT_LE, INT_GT, INT_GE] {
        postulate(env, op, rel(int()))?;
    }

    for op in [REAL_ADD, REAL_SUB, REAL_MUL, REAL_DIV] {
        postulate(env, op, binop(real()))?;
    }
    postulate(env, REAL_NEG, un(real()))?;
    for op in [REAL_LT, REAL_LE, REAL_GT, REAL_GE] {
        postulate(env, op, rel(real()))?;
    }
    Ok(())
}

/// Install the **full lu-kb-successor arithmetic prelude**: the SMT-LIB core
/// ([`install_int_real`]) PLUS the strict `Nat`/`WNat` sorts, the inter-sort
/// injections, and the number-theory built-ins `pow`/`odd`/`prime`. This is
/// what the lu-kb face installs (the surface uses `Nat`/`WNat`/`pow`/… as
/// reserved built-ins). All `open`.
pub fn install_arith(env: &mut Env) -> Result<(), TypeError> {
    install_int_real(env)?;

    let int = || Term::cnst(INT);
    let real = || Term::cnst(REAL);
    let nat = || Term::cnst(NAT);
    let wnat = || Term::cnst(WNAT);

    postulate(env, NAT, Term::type_(0))?;
    postulate(env, WNAT, Term::type_(0))?;

    postulate(env, NAT2WNAT, Term::arrow(nat(), wnat()))?;
    postulate(env, WNAT2INT, Term::arrow(wnat(), int()))?;
    postulate(env, NAT2INT, Term::arrow(nat(), int()))?;
    postulate(env, WNAT2REAL, Term::arrow(wnat(), real()))?;
    postulate(env, NAT2REAL, Term::arrow(nat(), real()))?;

    postulate(env, POW, binop(int()))?;
    postulate(env, ODD, Term::arrow(int(), Term::prop()))?;
    postulate(env, PRIME, Term::arrow(int(), Term::prop()))?;

    Ok(())
}

/// Whether `env` already has the arithmetic core installed (checks the `Int`
/// sort). Lets a face install it at most once across several inputs.
pub fn arith_installed(env: &Env) -> bool {
    env.lookup(INT).is_some()
}

/// Idempotently postulate an **integer numeral** as an opaque `open` constant of
/// sort `Int`, returning the term `Const(canonical)`. `canonical` must already be
/// the canonical decimal spelling (e.g. `"42"`); the face is responsible for
/// canonicalising `#x2A` / leading-zero / sign forms before calling. SMT-LIB
/// simple symbols cannot begin with a digit, so an all-digit name never clashes
/// with a user symbol. The literal is opaque to the kernel; its numeric *value*
/// is recovered only at the CIC→HOL lowering (which reads the all-digit name).
pub fn int_literal(env: &mut Env, canonical: &str) -> Result<Term, TypeError> {
    literal(env, canonical, INT)
}

/// Idempotently postulate a **real/decimal numeral** as an opaque `open` constant
/// of sort `Real` (e.g. canonical `"3.14"`). See [`int_literal`].
pub fn real_literal(env: &mut Env, canonical: &str) -> Result<Term, TypeError> {
    literal(env, canonical, REAL)
}

fn literal(env: &mut Env, canonical: &str, sort: &str) -> Result<Term, TypeError> {
    if let Some(decl) = env.lookup(canonical) {
        // Re-use an already-postulated literal; guard the (face-level) invariant
        // that the same spelling is always the same sort.
        debug_assert!(matches!(decl.modality, Modality::Open));
        return Ok(Term::cnst(canonical));
    }
    postulate(env, canonical, Term::cnst(sort))?;
    Ok(Term::cnst(canonical))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Ctx, Term, infer, is_def_eq, postulate};

    fn env_with_arith() -> Env {
        let mut env = Env::new();
        install_arith(&mut env).expect("prelude installs cleanly");
        env
    }

    #[test]
    fn prelude_installs_and_is_detected() {
        let env = env_with_arith();
        assert!(arith_installed(&env));
        for s in [INT, REAL, NAT, WNAT, INT_ADD, REAL_DIV, POW, ODD, PRIME, NAT2INT] {
            assert!(env.lookup(s).is_some(), "missing postulate `{s}`");
        }
    }

    #[test]
    fn arith_term_type_checks_to_prop() {
        // `Int.lt (Int.add 2 2) 5` : Prop
        let mut env = env_with_arith();
        let two = int_literal(&mut env, "2").unwrap();
        let five = int_literal(&mut env, "5").unwrap();
        let sum = Term::apps(Term::cnst(INT_ADD), [two.clone(), two.clone()]);
        // the sum is an Int
        let sum_ty = infer(&env, &Ctx::new(), &sum).unwrap();
        assert!(is_def_eq(&env, &sum_ty, &Term::cnst(INT)));
        // the comparison is a Prop
        let lt = Term::apps(Term::cnst(INT_LT), [sum, five]);
        let lt_ty = infer(&env, &Ctx::new(), &lt).unwrap();
        assert!(is_def_eq(&env, &lt_ty, &Term::prop()), "got {lt_ty}");
    }

    #[test]
    fn injection_lifts_nat_into_int_arith() {
        // a Nat-sorted variable used in Int arithmetic via the explicit injection.
        let mut env = env_with_arith();
        postulate(&mut env, "n", Term::cnst(NAT)).unwrap();
        let n_as_int = Term::app(Term::cnst(NAT2INT), Term::cnst("n"));
        let one = int_literal(&mut env, "1").unwrap();
        let sum = Term::apps(Term::cnst(INT_ADD), [n_as_int, one]);
        let ty = infer(&env, &Ctx::new(), &sum).unwrap();
        assert!(is_def_eq(&env, &ty, &Term::cnst(INT)), "got {ty}");
    }

    #[test]
    fn pow_and_predicates_type_check() {
        // `prime (pow 2 n)` with n : Nat injected — a number-theory shape.
        let mut env = env_with_arith();
        postulate(&mut env, "n", Term::cnst(NAT)).unwrap();
        let two = int_literal(&mut env, "2").unwrap();
        let n_int = Term::app(Term::cnst(NAT2INT), Term::cnst("n"));
        let p = Term::apps(Term::cnst(POW), [two, n_int]);
        let prime_p = Term::app(Term::cnst(PRIME), p);
        let ty = infer(&env, &Ctx::new(), &prime_p).unwrap();
        assert!(is_def_eq(&env, &ty, &Term::prop()), "got {ty}");
    }

    #[test]
    fn literals_are_idempotent() {
        let mut env = env_with_arith();
        let a = int_literal(&mut env, "42").unwrap();
        let b = int_literal(&mut env, "42").unwrap(); // no DuplicateConst
        assert_eq!(a, b);
        // a decimal of the same digits is a DISTINCT Real literal.
        let r = real_literal(&mut env, "42.0").unwrap();
        assert_ne!(a, r);
        assert!(is_def_eq(&env, &infer(&env, &Ctx::new(), &r).unwrap(), &Term::cnst(REAL)));
    }

    #[test]
    fn mistyped_arith_is_rejected_by_the_kernel() {
        // `Int.add 3.0 2` — a Real argument to an Int operator must FAIL to
        // type-check (the kernel guards the face; soundness of the firewall).
        let mut env = env_with_arith();
        let real = real_literal(&mut env, "3.0").unwrap();
        let two = int_literal(&mut env, "2").unwrap();
        let bad = Term::apps(Term::cnst(INT_ADD), [real, two]);
        assert!(infer(&env, &Ctx::new(), &bad).is_err(), "Real arg to Int.add must be rejected");
    }
}
