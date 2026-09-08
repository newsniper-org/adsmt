// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! The kernel's numeral convention is that a numeral SPELLING *is* that number:
//! `theory::literal` re-uses an already-declared constant of the same spelling,
//! `whnf` folds arithmetic over such constants, and the CIC→HOL lowering reads
//! the value off the name. Its stated justification — "SMT-LIB simple symbols
//! cannot begin with a digit, so an all-digit name never clashes with a user
//! symbol" — holds for SMT-LIB and fails for any caller that can quote an
//! identifier. So the convention has to be an INVARIANT the kernel enforces,
//! not an assumption it makes about its callers.

use adsmt_ir::{Env, Term, postulate, theory, whnf};

fn arith_env() -> Env {
    let mut env = Env::new();
    theory::install_arith(&mut env).expect("prelude");
    env
}

/// A numeral-spelled constant may only be declared at an arithmetic sort.
/// `\`-3\` : S` for an uninterpreted `S` used to be admitted, and then `whnf`
/// declared `-3` and `-4` unequal by SPELLING — a proof about two constants
/// nothing relates.
#[test]
fn a_numeral_spelling_is_refused_at_a_non_arithmetic_sort() {
    let mut env = arith_env();
    postulate(&mut env, "S", Term::type_(0)).unwrap();
    for name in ["-3", "42", "2.5", "-2.5"] {
        let e = postulate(&mut env, name, Term::cnst("S"))
            .expect_err(&format!("`{name}` at sort S must be refused"));
        assert!(format!("{e}").contains("numeral"), "{name}: {e}");
    }
    // The arithmetic sorts stay open — this is where literals live.
    postulate(&mut env, "-3", Term::cnst(theory::INT)).expect("Int is fine");
    postulate(&mut env, "2.5", Term::cnst(theory::REAL)).expect("Real is fine");
    // And an ordinary name is untouched at any sort.
    postulate(&mut env, "a", Term::cnst("S")).expect("ordinary name");
}

/// `=` is polymorphic — `args[0]` is the type. Folding it without reading that
/// argument decided equality of two opaque constants by their spelling.
#[test]
fn the_equality_fold_reads_its_type_argument() {
    let mut env = arith_env();
    postulate(&mut env, "S", Term::type_(0)).unwrap();
    postulate(&mut env, "p", Term::cnst("S")).unwrap();
    postulate(&mut env, "q", Term::cnst("S")).unwrap();
    let at_s = Term::apps(Term::cnst("="), [Term::cnst("S"), Term::cnst("p"), Term::cnst("q")]);
    let w = whnf(&env, &at_s);
    assert_ne!(format!("{w}"), "false", "two opaque constants are not provably distinct");
    assert_ne!(format!("{w}"), "true");

    // At `Int`, over real literals, the fold is exactly what the convention licenses.
    let two = theory::int_literal(&mut env, "2").unwrap();
    let three = theory::int_literal(&mut env, "3").unwrap();
    let at_int = Term::apps(Term::cnst("="), [Term::cnst(theory::INT), two.clone(), three]);
    assert_eq!(format!("{}", whnf(&env, &at_int)), "false");
    let refl = Term::apps(Term::cnst("="), [Term::cnst(theory::INT), two.clone(), two]);
    assert_eq!(format!("{}", whnf(&env, &refl)), "true");
}
