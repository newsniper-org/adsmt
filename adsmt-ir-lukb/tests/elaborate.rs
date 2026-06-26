//! Conformance for the lu-kb-successor face (Phase 1b, first slice): real
//! source parses + elaborates into kernel-checked terms, the round-trip
//! pretty-printer recovers the parse, and the rejection paths are surfaced as
//! `FaceError`s — never a trusted ill-typed term.

use adsmt_ir::{Ctx, Term, infer, is_def_eq};
use adsmt_ir_lukb::{FaceError, elaborate, parse, print_module};

/// Every hypothesis and goal of a successfully-elaborated module is a closed
/// `Prop` (the kernel re-checked it).
fn all_props(src: &str, n_hyp: usize, n_goal: usize) -> adsmt_ir_lukb::Elaborated {
    let r = elaborate(src).expect("elaborates");
    assert_eq!(r.hypotheses.len(), n_hyp, "hypothesis count");
    assert_eq!(r.goals.len(), n_goal, "goal count");
    for t in r.hypotheses.iter().chain(r.goals.iter()) {
        let ty = infer(&r.env, &Ctx::new(), t).expect("type-checks");
        assert!(is_def_eq(&r.env, &ty, &Term::prop()), "is a Prop: {t} : {ty}");
    }
    r
}

/// Propositional + EUF: sorts, consts, axioms, a goal, with quantifiers.
#[test]
fn euf_propositional_module() {
    all_props(
        "sort S\n\
         const a: S\n\
         const b: S\n\
         axiom refl: forall x: S. x = x\n\
         assume ab: a = b\n\
         goal g: a = b or not (a = b)\n",
        2,
        1,
    );
}

/// Integer arithmetic + comparisons + the sequent turnstile.
#[test]
fn int_arithmetic_and_sequent() {
    let r = all_props(
        "const x: Int\n\
         const y: Int\n\
         axiom comm: forall a b: Int. a + b = b + a\n\
         goal sum_pos: x > 0, y > 0 |- x + y > 0\n",
        1,
        1,
    );
    // the arithmetic + lu-kb-only built-ins are installed.
    assert!(r.env.lookup("Int").is_some() && r.env.lookup("Nat").is_some());
    assert!(r.env.lookup("pow").is_some());
}

/// Real arithmetic + `/` + decimal literals + the `to_real` injection.
#[test]
fn real_arithmetic_and_builtins() {
    all_props(
        "const r: Real\n\
         const n: Int\n\
         axiom half: r / 2.0 < r\n\
         goal g: to_real(n) > r ==> r < to_real(n)\n",
        1,
        1,
    );
}

/// The number-theory built-ins `pow`/`odd`/`prime` and `Nat`/`WNat` binders
/// (the user's Fermat/Goldbach shapes — written, not solved).
#[test]
fn number_theory_shapes_elaborate() {
    all_props(
        "axiom fermat: forall n: Nat. n >= 3 <==> not exists x y z: Nat. \
            pow(nat2int(x), nat2int(n)) + pow(nat2int(y), nat2int(n)) = pow(nat2int(z), nat2int(n))\n\
         goal odd_prime: forall p: Int. prime(p) and p > 2 ==> odd(p)\n",
        1,
        1,
    );
}

/// The round-trip pretty-printer: `parse(print(parse(src)))` is stable.
#[test]
fn printer_round_trips() {
    let src = "sort S\n\
               const x: Int\n\
               axiom a: forall y: Int. y + 1 > y\n\
               goal g: x > 0 ==> not (x = 0)\n";
    let m1 = parse(src).expect("parses");
    let printed = print_module(&m1);
    let m2 = parse(&printed).expect("re-parses the printed form");
    assert_eq!(m1, m2, "AST is stable across print/re-parse\nprinted:\n{printed}");
}

/// `let … in …` binds and substitutes.
#[test]
fn let_binding_elaborates() {
    all_props("const x: Int\ngoal g: let y = x + 1 in y > x\n", 0, 1);
}

// ── rejection paths (the firewall) ──────────────────────────────────────

/// An item body that is not a `Prop` (a bare Int term) is rejected.
#[test]
fn non_prop_body_is_rejected() {
    match elaborate("const x: Int\ngoal g: x + 1\n") {
        Err(FaceError::Unsupported(m)) => assert!(m.contains("expected Bool/Prop"), "{m}"),
        Err(e) => panic!("expected a Prop-check rejection, got a different error: {e}"),
        Ok(_) => panic!("expected a Prop-check rejection, but it elaborated"),
    }
}

/// Numeric operands unify via injection (`Int ⊂ Real`), but **unrelated** sorts
/// are rejected (the kernel sort check, no coercion path).
#[test]
fn unrelated_sort_operands_are_rejected() {
    // Int vs Real now unifies (Int injects into Real) — elaborates.
    assert!(elaborate("const x: Int\nconst r: Real\ngoal g: x = r\n").is_ok());
    // an uninterpreted sort vs Int has no injection — rejected.
    assert!(matches!(
        elaborate("sort S\nconst s: S\nconst x: Int\ngoal g: s = x\n"),
        Err(FaceError::Unsupported(_))
    ));
}

/// An unknown symbol is rejected, not silently treated as opaque.
#[test]
fn unknown_symbol_is_rejected() {
    assert!(matches!(
        elaborate("goal g: nope > 0\n"),
        Err(FaceError::Unsupported(_))
    ));
}

/// A parse error carries a byte offset.
#[test]
fn parse_error_has_offset() {
    match elaborate("goal g: forall x Int. x > 0\n") {
        // missing `:` after the binder name
        Err(FaceError::Parse { at, .. }) => assert!(at > 0),
        Err(e) => panic!("expected a parse error, got: {e}"),
        Ok(_) => panic!("expected a parse error, but it elaborated"),
    }
}

// ── slice 2: refinement-constrained quantifiers, chained cmp, `==` alias ──

/// A binder refinement constraint `(n: Int) > 5` is a *domain* restriction:
/// `forall (n: Int) > 5. P` desugars to `forall n: Int. n > 5 ==> P`.
#[test]
fn refinement_constrained_forall() {
    all_props("goal g: forall (n: Int) > 5. n > 0\n", 0, 1);
}

/// A multi-name constrained group `(a b c: Nat) >= 2` applies the constraint to
/// each name, and the constraint (domain) stays distinct from a body antecedent
/// — the Goldbach shape (`> 5` domain + `odd(n)` antecedent).
#[test]
fn constraint_vs_antecedent_distinction() {
    all_props(
        "axiom goldbach_weak: forall (n: Nat) > 5. odd(nat2int(n)) ==> \
            exists (a b c: Nat) >= 2. \
              prime(nat2int(a)) and prime(nat2int(b)) and prime(nat2int(c)) and \
              nat2int(a) + nat2int(b) + nat2int(c) = nat2int(n)\n",
        1,
        0,
    );
}

/// A chained comparison `0 < x < 10` desugars to `(0<x) and (x<10)` — a Prop.
#[test]
fn chained_comparison_elaborates() {
    all_props("const x: Int\ngoal g: 0 < x < 10\n", 0, 1);
}

/// The legacy `==` equality alias parses identically to `=`.
#[test]
fn legacy_double_equals_alias() {
    let a = parse("goal g: x == y\n").expect("==");
    let b = parse("goal g: x = y\n").expect("=");
    assert_eq!(a, b, "`==` is the `=` alias");
}

/// Round-trip with a constrained binder + chained comparison.
#[test]
fn printer_round_trips_constrained() {
    let src = "goal g: forall (n: Int) >= 2. exists (m: Int) > 0. n = m + m or n = m + m + 1\n";
    let m1 = parse(src).expect("parses");
    let printed = print_module(&m1);
    let m2 = parse(&printed).expect("re-parses");
    assert_eq!(m1, m2, "constrained AST stable across print/re-parse\nprinted:\n{printed}");
}

// ── slice 3: bounded `in` range quantifiers + triggers ──────────────────

/// A bounded range `forall x in 0..n. P` desugars to
/// `forall x: Int. 0 <= x and x < n ==> P` (half-open); `exists` uses `and`.
#[test]
fn bounded_range_quantifiers() {
    all_props("const n: Int\ngoal g: forall x in 0..n. x >= 0\n", 0, 1);
    all_props("const n: Int\ngoal h: exists x in 1..n. x > 0\n", 0, 1);
}

/// Triggers parse (single + multi-pattern, repeatable), are carried in the AST,
/// round-trip, and elaborate (the kernel `Π` can't hold them, so they are
/// dropped at elaboration — sound, since triggers only guide instantiation).
#[test]
fn triggers_parse_round_trip_and_are_dropped() {
    use adsmt_ir_lukb::ast::{Item, Term};
    let m = parse(
        "goal g: forall x: Int. prime(x) trigger prime(x) trigger { odd(x), prime(x) }\n",
    )
    .expect("parses triggers");
    let Item::Goal(_, Term::Forall(_, _, trigs)) = &m.items[0] else {
        panic!("expected a forall goal");
    };
    assert_eq!(trigs.len(), 2, "two trigger clauses");
    assert_eq!(trigs[0].len(), 1, "first is a single pattern");
    assert_eq!(trigs[1].len(), 2, "second is a multi-pattern");
    // elaborates (triggers dropped, body is a Prop).
    all_props("goal g: forall x: Int. prime(x) trigger prime(x)\n", 0, 1);
    // round-trips.
    let m2 = parse(&print_module(&m)).expect("re-parses");
    assert_eq!(m, m2, "triggers round-trip");
}

/// Round-trip of a range binder nested with an inner triggered quantifier.
#[test]
fn printer_round_trips_range_and_trigger() {
    let src = "goal g: forall x in 0..10. exists y: Int. prime(y) trigger prime(y)\n";
    let m1 = parse(src).expect("parses");
    let m2 = parse(&print_module(&m1)).expect("re-parses");
    assert_eq!(m1, m2, "range + trigger round-trip");
}

// ── slice 4: the indentation-block item body (multi-term conjunction) ────

/// An `axiom`/`assume`/`goal` body may be a block of several terms (one per
/// indented line), conjoined — terminated by the next item keyword / EOF.
#[test]
fn block_body_conjoins_terms() {
    let r = all_props(
        "const x: Int\n\
         const y: Int\n\
         axiom positives:\n  \
            x > 0\n  \
            y > 0\n\
         goal g: x + y > 0\n",
        1, // ONE axiom (the two lines are conjoined into one Prop)
        1,
    );
    // the conjoined axiom is `(x>0) and (y>0)` — an `and` at the head.
    use adsmt_ir_lukb::ast::{BinOp, Item, Term};
    let m = parse(
        "const x: Int\nconst y: Int\naxiom positives:\n  x > 0\n  y > 0\n",
    )
    .unwrap();
    let Item::Axiom(_, Term::Bin(BinOp::And, ..)) = &m.items[2] else {
        panic!("the block body should be a conjunction");
    };
    let _ = r;
}

/// A sequent whose conclusion is itself a block of conjoined terms.
#[test]
fn sequent_with_block_conclusion() {
    all_props(
        "const x: Int\n\
         goal g: x > 0 |-\n  \
            x >= 0\n  \
            x != 0 - 1\n",
        0,
        1,
    );
}

/// The block form is the same AST as the explicit-`and` form, so it round-trips
/// through the canonical (`and`) printed shape.
#[test]
fn block_body_equals_explicit_and() {
    let block = parse("axiom a:\n  p\n  q\n  r\n").unwrap();
    let explicit = parse("axiom a: p and q and r\n").unwrap();
    assert_eq!(block, explicit, "block body ≡ explicit `and`");
}

// ── slice 5: function-signature declarations (producer-readiness) ────────

/// `fn f(x: Int): Int` declares an opaque function; `fn p(x y: Int): Bool`
/// declares a predicate (`Int -> Int -> Prop`). Both are usable in quantified
/// axioms and goals (real EUF-over-functions).
#[test]
fn function_signatures_declare_and_apply() {
    let r = all_props(
        "fn f(x: Int): Int\n\
         fn p(x y: Int): Bool\n\
         axiom monotone: forall a b: Int. a <= b ==> f(a) <= f(b)\n\
         goal g: p(f(0), f(1)) or not p(f(0), f(1))\n",
        1,
        1,
    );
    assert!(r.env.lookup("f").is_some() && r.env.lookup("p").is_some());
}

/// A function-typed declaration round-trips, including multi-name param groups
/// and a Real return.
#[test]
fn fn_round_trips() {
    let src = "fn f(x y: Int, b: Bool): Real\ngoal g: forall n: Int. f(n, n, true) > 0.0\n";
    let m1 = parse(src).expect("parses");
    let m2 = parse(&print_module(&m1)).expect("re-parses");
    assert_eq!(m1, m2, "fn declaration round-trips\n{}", print_module(&m1));
}

/// A wrong-arity / wrong-sort application of a declared function is rejected by
/// the kernel (the firewall holds for user functions too).
#[test]
fn misapplied_function_is_rejected() {
    // `f` expects an Int, given a Real with no injection downward — rejected.
    assert!(matches!(
        elaborate("fn f(x: Int): Int\nconst r: Real\ngoal g: f(r) = 0\n"),
        Err(FaceError::Unsupported(_)) | Err(FaceError::Kernel(_))
    ));
}

// ── slice 6: backtick-quoted identifiers (arbitrary AIR/SMT symbols) ──────

/// A symbol with characters a bare identifier can't hold (`%`, `.`) is written
/// `` `…` `` and lexes/parses/elaborates as that exact symbol — the producer
/// need for Verus/AIR names like `%%location_label%%0`.
#[test]
fn quoted_identifier_elaborates() {
    let r = all_props(
        "const `%%location_label%%0`: Bool\n\
         fn `lib.is_even`(n: Int): Bool\n\
         goal g: `%%location_label%%0` or `lib.is_even`(0)\n",
        0,
        1,
    );
    assert!(r.env.lookup("%%location_label%%0").is_some());
    assert!(r.env.lookup("lib.is_even").is_some());
}

/// A backtick-quoted identifier whose spelling is a keyword (`forall`) is a
/// *symbol*, not the keyword — and the printer re-quotes it so it round-trips.
#[test]
fn quoted_keyword_is_a_symbol() {
    let src = "const `forall`: Bool\ngoal g: `forall`\n";
    let m1 = parse(src).expect("a quoted keyword is a symbol");
    let printed = print_module(&m1);
    assert!(printed.contains("`forall`"), "the symbol is re-quoted:\n{printed}");
    let m2 = parse(&printed).expect("re-parses");
    assert_eq!(m1, m2, "quoted-keyword symbol round-trips");
}

/// Quoted identifiers round-trip through the printer with special chars
/// preserved, in const/fn/binder/var positions.
#[test]
fn quoted_identifier_round_trips() {
    let src = "const `x~2`: Int\n\
               fn `f@hi`(a: Int): Int\n\
               goal g: forall `k!0`: Int. `f@hi`(`k!0`) > `x~2`\n";
    let m1 = parse(src).expect("parses");
    let printed = print_module(&m1);
    let m2 = parse(&printed).expect("re-parses");
    assert_eq!(m1, m2, "quoted ids round-trip\n{printed}");
}

/// An unterminated backtick is a parse error with an offset (not a panic).
#[test]
fn unterminated_quoted_identifier_errors() {
    match elaborate("goal g: `oops > 0\n") {
        Err(FaceError::Parse { .. }) => {}
        Err(e) => panic!("expected a Parse error, got: {e}"),
        Ok(_) => panic!("expected a parse error, but it elaborated"),
    }
}

// ── slice 7: data datatypes + fn=body definitions ───────────────────────

/// A `data` declaration admits a kernel inductive; its constructors are usable
/// as terms. (`Nat`/`Int`/… are reserved arith-prelude sorts, so a datatype
/// uses a fresh name — `Peano`.)
#[test]
fn data_datatype_elaborates() {
    let r = all_props(
        "data Peano = zero | succ(pred: Peano)\n\
         goal g: succ(succ(zero)) = succ(succ(zero))\n",
        0,
        1,
    );
    assert!(r.env.lookup("Peano").is_some(), "the inductive is declared");
    assert!(
        r.env.lookup("zero").is_some() && r.env.lookup("succ").is_some(),
        "constructors are declared"
    );
}

/// A recursive datatype with named + positional fields (a `List` over `Int`),
/// constructors applied to mixed arguments.
#[test]
fn data_recursive_with_fields() {
    let r = all_props(
        "data Lst = nil | cons(head: Int, tail: Lst)\n\
         const p: Lst\n\
         goal g: cons(1, p) = cons(1, p)\n",
        0,
        1,
    );
    assert!(r.env.lookup("cons").is_some());
}

/// A `fn f(..) = body` is a DEFINITION (`Modality::Def`), distinct from a
/// signature postulate (`Modality::Open`); both are usable as terms.
#[test]
fn fn_definition_vs_signature() {
    use adsmt_ir::Modality;
    let r = elaborate(
        "fn sig(x: Int): Int\n\
         fn dbl(x: Int): Int = x + x\n\
         goal g: dbl(sig(2)) > 0\n",
    )
    .expect("elaborates");
    assert!(matches!(r.env.lookup("sig").unwrap().modality, Modality::Open), "signature → open");
    assert!(matches!(r.env.lookup("dbl").unwrap().modality, Modality::Def(_)), "= body → def");
}

/// A predicate definition `fn p(..): Bool = <prop>` (`Bool` → `Prop`).
#[test]
fn fn_bool_definition_elaborates() {
    all_props("fn pos(x: Int): Bool = x > 0\ngoal g: pos(5) or not pos(5)\n", 0, 1);
}

/// A **recursive** `fn` body (mentioning the function being defined) is rejected
/// — the kernel `fix` is a later slice; the self-reference is an unknown symbol
/// (sound: no ill-typed term escapes).
#[test]
fn recursive_fn_definition_is_rejected() {
    assert!(matches!(
        elaborate("fn loops(x: Int): Int = loops(x)\n"),
        Err(FaceError::Unsupported(_))
    ));
}

/// `data` + `fn=body` round-trip through the printer.
#[test]
fn data_and_fn_def_round_trip() {
    let src = "data Tree = leaf | node(l: Tree, v: Int, r: Tree)\n\
               fn inc(n: Int): Int = n + 1\n\
               goal g: inc(0) >= 0\n";
    let m1 = parse(src).expect("parses");
    let m2 = parse(&print_module(&m1)).expect("re-parses");
    assert_eq!(m1, m2, "data + fn def round-trip\n{}", print_module(&m1));
}
