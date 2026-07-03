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

/// Value-parameterized RING sorts `GF(p)` / `IntModulo(m)` / `GFPower(p, n)`
/// elaborate to a canonical postulated sort; two same-ring consts share ONE sort
/// (equality type-checks); bad parameters are rejected at the face.
#[test]
fn ring_sorts_elaborate_and_validate() {
    // each ring sort declaration elaborates (the canonical sort is postulated).
    assert!(elaborate("const x: GF(7)\n").is_ok());
    assert!(elaborate("const m: IntModulo(6)\n").is_ok());
    assert!(elaborate("const g: GFPower(2, 8)\n").is_ok());
    // two GF(7) consts share ONE sort ⇒ `a = b` type-checks (eq needs equal sorts).
    all_props("const a: GF(7)\nconst b: GF(7)\ngoal g: a = b\n", 0, 1);
    // GF(7) and Int are DISTINCT sorts ⇒ a cross-sort equality is rejected.
    assert!(elaborate("const a: GF(7)\nconst i: Int\ngoal g: a = i\n").is_err());
    // invalid parameters are rejected at the face (usability gate): a composite
    // GF order, a non-prime GFPower base, an IntModulo m < 2, a degree-0 GFPower.
    for bad in [
        "const x: GF(6)\n",
        "const x: GFPower(4, 2)\n",
        "const x: IntModulo(1)\n",
        "const x: GFPower(3, 0)\n",
    ] {
        assert!(elaborate(bad).is_err(), "must reject: {bad}");
    }
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

// ── slice 2b: general refinement-type binders `{v: T | φ}` ──────────────

/// A **refinement-type** binder `{n: Int | n > 5}` is the general form of the
/// comparison constraint: the predicate `φ` is an arbitrary Bool term over the
/// bound name, conjoined into the domain guard (`∀ → ⟹`). Elaborates to a Prop.
#[test]
fn refinement_type_binder_forall() {
    let r = parse("goal g: forall { n: Int | n > 5 }. n > 0\n").expect("parses brace form");
    use adsmt_ir_lukb::ast::{Item, Term};
    let Item::Goal(_, Term::Forall(bs, _, _)) = &r.items[0] else {
        panic!("expected a forall goal");
    };
    assert!(bs[0].refinement.is_some(), "the binder carries a refinement predicate");
    all_props("goal g: forall { n: Int | n > 5 }. n > 0\n", 0, 1);
}

/// The brace refinement `{n: Int | n > 5}` and the comparison sugar `(n: Int) > 5`
/// elaborate to the **same** kernel term — the comparison is the single-predicate
/// special case of the general refinement.
#[test]
fn refinement_generalises_the_comparison_constraint() {
    let brace = elaborate("goal g: forall { n: Int | n > 5 }. n > 0\n").expect("brace");
    let cmp = elaborate("goal g: forall (n: Int) > 5. n > 0\n").expect("cmp");
    assert_eq!(brace.goals, cmp.goals, "`{{n|n>5}}` ≡ `(n)>5`");
}

/// In `∃`, the refinement guard is a **conjunction** (the soundness-critical
/// polarity, mirroring the comparison/range forms).
#[test]
fn refinement_type_binder_exists() {
    all_props("const k: Int\ngoal g: exists { n: Int | n > 5 }. n = k\n", 0, 1);
}

/// A multi-name refinement group `{a b: Int | a < b}` binds a predicate that
/// mentions several of the bound names (the predicate is added once, verbatim —
/// distinct from the comparison form which broadcasts per name).
#[test]
fn refinement_type_multi_name() {
    all_props("goal g: forall { a b: Int | a < b }. a < b + 1\n", 0, 1);
}

/// Idempotence (`r ∧ … ∧ r ⟺ r`): two binders whose domain guards are the
/// *same* predicate `a > 0` collapse to a single conjunct (no `and`).
#[test]
fn duplicate_guards_collapse_by_idempotence() {
    let r = elaborate("goal g: forall { a: Int | a > 0 }, { b: Int | a > 0 }. b > a\n")
        .expect("elaborates");
    let goal = format!("{}", r.goals[0]);
    assert!(!goal.contains("and"), "the duplicate `a > 0` guard is deduped: {goal}");
}

/// Round-trip of the brace refinement form through the printer.
#[test]
fn printer_round_trips_refinement() {
    let src = "goal g: forall { n: Int | n > 5 }. exists { m: Int | m < n }. n = m + 1\n";
    let m1 = parse(src).expect("parses");
    let printed = print_module(&m1);
    let m2 = parse(&printed).expect("re-parses");
    assert_eq!(m1, m2, "refinement AST stable across print/re-parse\nprinted:\n{printed}");
}

// ── slice 2c: refinement TYPES in type position (const) + tick-idents ────

/// `'p` lexes as a tick-identifier (a generic predicate parameter); a bare `p`
/// and a lone `'` do not.
#[test]
fn tick_ident_recognised() {
    use adsmt_ir_lukb::lexer::is_tick_ident;
    assert!(is_tick_ident("'p"));
    assert!(is_tick_ident("'pred1"));
    assert!(!is_tick_ident("p"));
    assert!(!is_tick_ident("'"));
    assert!(!is_tick_ident("'1p"), "must start with an ident char after the quote");
}

/// A refinement-typed constant `const c: {v: Int | v > 0}` postulates `c: Int`
/// PLUS the trusted positivity fact `c > 0` as a hypothesis (so it is sound:
/// dropping it would admit a spurious model where `c <= 0`).
#[test]
fn const_refinement_adds_positivity_hypothesis() {
    let r = all_props("const c: {v: Int | v > 0}\ngoal g: c > 0\n", 1, 1);
    // the single hypothesis is the constant's refinement fact `c > 0`, with the
    // bound var β-substituted by the constant (NOT left as a `(λv. …) c` redex).
    let hyp = format!("{:?}", r.hypotheses[0]);
    assert!(hyp.contains("Int.gt") && hyp.contains("c"), "positivity `c > 0`: {hyp}");
    assert!(!hyp.contains('λ'), "the binder is β-substituted, not a redex: {hyp}");
}

/// The refinement fact is genuinely USED: `const c: {v: Int | v > 0}` makes the
/// goal `c >= 1` provable shape-wise (1 hyp `c > 0`, 1 goal). Without the
/// hypothesis the goal would be a bare `c >= 1` over an unconstrained Int.
#[test]
fn const_refinement_round_trips() {
    let src = "const c: {v: Int | v > 0}\ngoal g: c >= 1\n";
    let m1 = parse(src).expect("parses");
    let printed = print_module(&m1);
    let m2 = parse(&printed).expect("re-parses");
    assert_eq!(m1, m2, "refinement-typed const round-trips\nprinted:\n{printed}");
}

/// A **generic** predicate parameter `'p` in a `const` type is rejected: there
/// is no `fn` to bind it (a const cannot be predicate-polymorphic), so `'p`
/// resolves to an unknown symbol.
#[test]
fn generic_pred_in_const_is_rejected() {
    let e = elaborate("const c: {v: Int | 'p(v)}\ngoal g: c = c\n");
    assert!(e.is_err(), "unbound generic `'p` in a const must be rejected");
}

// ── slice 2d: predicate-polymorphic functions (generic `'p`) ─────────────

/// A constraint-preserving identity `fn id_p(x: {v: Int | 'p(v)}): {v: Int |
/// 'p(v)} = x` is predicate-polymorphic in `'p`: the body checks ONCE with `'p`
/// abstract, and a definition emits the construct-site contract obligation as a
/// GOAL `∀'p. ∀x. 'p(x) ==> 'p(id_p('p, x))`.
#[test]
fn constraint_preserving_identity_def_emits_a_goal() {
    let r = all_props("fn id_p(x: {v: Int | 'p(v)}): {v: Int | 'p(v)} = x\n", 0, 1);
    let goal = format!("{:?}", r.goals[0]);
    assert!(goal.contains("id_p"), "the contract is about id_p: {goal}");
}

/// A predicate-polymorphic *signature* (no body) postulates the contract as a
/// TRUSTED axiom (a hypothesis), not a goal — the user asserts `g` preserves
/// `'p`; use sites instantiate it.
#[test]
fn predicate_polymorphic_signature_is_a_trusted_axiom() {
    all_props("fn g(x: {v: Int | 'p(v)}): {v: Int | 'p(v)}\n", 1, 0);
}

/// A CONCRETE refinement fn (no `'p`) gets the same contract treatment:
/// `fn inc(x: {v: Int | v > 0}): {v: Int | v > 0} = x + 1` → the obligation
/// `∀x. x > 0 ==> (inc x) > 0`.
#[test]
fn concrete_refinement_fn_emits_its_contract() {
    let r = all_props("fn inc(x: {v: Int | v > 0}): {v: Int | v > 0} = x + 1\n", 0, 1);
    let goal = format!("{:?}", r.goals[0]);
    assert!(goal.contains("inc") && goal.contains("Int.gt"), "contract `x>0 ==> inc x>0`: {goal}");
}

/// Two distinct generic predicates `'p`, `'q` bind independently; the
/// precondition is their conjunction.
#[test]
fn two_generic_predicates_bind_independently() {
    let r = all_props(
        "fn g(x: {v: Int | 'p(v)}, y: {v: Int | 'q(v)}): {v: Int | 'p(v)} = x\n",
        0,
        1,
    );
    let goal = format!("{:?}", r.goals[0]);
    // both predicates appear (as bound higher-order vars) and `g` is applied.
    assert!(goal.contains('g'), "contract mentions g: {goal}");
}

/// A `fn` whose return is NOT refined emits no obligation even with a generic
/// `'p` precondition (the precondition matters only at use sites).
#[test]
fn unrefined_return_emits_no_contract() {
    all_props("fn f(x: {v: Int | 'p(v)}): Int = x\n", 0, 0);
}

/// A predicate-polymorphic signature round-trips through the printer (the `'p`
/// tick-idents and the `{v: T | φ}` types are recovered).
#[test]
fn predicate_polymorphic_fn_round_trips() {
    let src = "fn g(x: {v: Int | 'p(v)}): {v: Int | 'p(v)}\n";
    let m1 = parse(src).expect("parses");
    let printed = print_module(&m1);
    let m2 = parse(&printed).expect("re-parses");
    assert_eq!(m1, m2, "predicate-polymorphic fn round-trips\nprinted:\n{printed}");
}

// ── slice 2e: function types `T -> U` (incl. refined arrows) ─────────────

/// A function-typed constant `const g: Int -> Int` postulates `g : Int → Int`
/// (a higher-order opaque constant); a goal may apply it.
#[test]
fn function_type_const_and_application() {
    all_props("const g: Int -> Int\nconst x: Int\ngoal h: g(x) = g(x)\n", 0, 1);
}

/// A higher-order function parameter: `fn ap(f: Int -> Int, x: Int): Int = f(x)`
/// applies its function argument. Applied to a real `Int -> Int` constant.
#[test]
fn higher_order_function_parameter() {
    all_props(
        "fn ap(f: Int -> Int, x: Int): Int = f(x)\n\
         const sq: Int -> Int\nconst c: Int\ngoal h: ap(sq, c) = sq(c)\n",
        0,
        1,
    );
}

/// `->` is right-associative: `A -> B -> C` parses as `A -> (B -> C)` and prints
/// back without inner parens; `(A -> B) -> C` keeps its domain parens.
#[test]
fn arrow_is_right_associative() {
    let src = "sort A\nsort B\nsort C\nconst g: A -> B -> C\nconst h: (A -> B) -> C\n";
    let m1 = parse(src).expect("parses");
    let printed = print_module(&m1);
    assert!(printed.contains("A -> B -> C"), "right-assoc, no inner parens: {printed}");
    assert!(printed.contains("(A -> B) -> C"), "left arrow keeps parens: {printed}");
    let m2 = parse(&printed).expect("re-parses");
    assert_eq!(m1, m2, "arrow types round-trip\n{printed}");
}

/// A **refined arrow** `{u: Int | u > 0} -> {v: Int | v > 0}` elaborates to the
/// plain value arrow `Int → Int` (refinements erased at the type level), and
/// round-trips.
#[test]
fn refined_arrow_erases_to_base() {
    // the const postulates `g : Int → Int`; no positivity hypothesis (the
    // refinements are on the arrow's domain/codomain, not a bare value).
    all_props("const g: {u: Int | u > 0} -> {v: Int | v > 0}\ngoal h: true\n", 0, 1);
    let src = "const g: {u: Int | u > 0} -> {v: Int | v > 0}\n";
    let m1 = parse(src).expect("parses");
    let m2 = parse(&print_module(&m1)).expect("re-parses");
    assert_eq!(m1, m2, "refined arrow round-trips\n{}", print_module(&m1));
}

// ── slice 2f: the trivial predicate `nop` (unrefined ≡ nop-refined) ──────

/// `nop` is the built-in always-true predicate: `{v: Int | nop(v)}` is a vacuous
/// refinement, so it adds NO hypothesis — `const c: {v: Int | nop(v)}` behaves
/// exactly like `const c: Int` (the user's uniformity: unrefined ≡ nop-refined).
#[test]
fn nop_refinement_is_vacuous() {
    // refined-with-nop: 0 hypotheses (the trivial refinement is dropped).
    all_props("const c: {v: Int | nop(v)}\ngoal g: c = c\n", 0, 1);
    // a plain const: also 0 hypotheses. The two are equivalent.
    all_props("const d: Int\ngoal g: d = d\n", 0, 1);
}

/// `nop` is polymorphic — `nop(x)` infers its type argument and is a `Prop`
/// regardless of the carrier sort.
#[test]
fn nop_is_polymorphic() {
    all_props("sort S\nconst a: S\ngoal g: nop(a)\n", 0, 1);
    all_props("const n: Int\ngoal h: nop(n)\n", 0, 1);
}

// ── slice 2g: `solve … by …` proof-term construct (the cut) ──────────────

/// `solve G by L` is a proof of `G` justified by `L`: it emits the **leaf** `L`
/// and the **bridge** `L ⟹ G` as obligations (the cut), and yields a proof of
/// `G`. Here `let pf = solve (c=c) by true in (c=c)` produces 3 goals — the leaf
/// `true`, the bridge `true ⟹ c=c`, and the main goal — all closed `Prop`s.
#[test]
fn solve_by_emits_the_cut_obligations() {
    let r = all_props("const c: Int\ngoal h: let pf = solve c = c by true in c = c\n", 0, 3);
    let goals = format!("{:?}", r.goals);
    assert!(goals.contains("true"), "the leaf obligation `true` is emitted: {goals}");
}

/// The obligations are **closed over the ambient context**: inside `forall x`,
/// `solve (x=x) by true` emits `∀x. true` and `∀x. (true ⟹ x=x)` — well-formed at
/// top level (the bound `x` is universally closed, not left dangling).
#[test]
fn solve_by_closes_over_the_context() {
    // 3 goals: the ∀-closed leaf + bridge, and the main ∀ goal. All type-check
    // (the kernel re-checks each), which is the proof that the de Bruijn
    // context-closing is correct.
    all_props("goal h: forall x: Int. let pf = solve x = x by true in x = x\n", 0, 3);
}

/// `solve … by …` round-trips through the printer.
#[test]
fn solve_by_round_trips() {
    let src = "const c: Int\ngoal h: let pf = solve c = c by true in c = c\n";
    let m1 = parse(src).expect("parses");
    let printed = print_module(&m1);
    assert!(printed.contains("solve c = c by true"), "printed: {printed}");
    let m2 = parse(&printed).expect("re-parses");
    assert_eq!(m1, m2, "solve/by round-trips\n{printed}");
}

// ── slice 2h: image binders `{y = f(x) | c}` (inference sugar) ───────────

/// The image binder `forall {y = f(x) | p(x)}. q(y)` desugars to the preimage
/// form `forall x:{Int|p(x)}. q(f(x))` — the quantifier ranges over the inferred
/// preimage `x` (type = `f`'s domain), guarded by `p(x)`, with `y` unfolded to
/// `f(x)`. The two elaborate to the SAME kernel term (the pre-verified
/// `image_quantifier_desugar`).
#[test]
fn image_binder_desugars_to_the_preimage_form() {
    let prelude = "const f: Int -> Int\nconst p: Int -> Bool\nconst q: Int -> Bool\n";
    let img = elaborate(&format!("{prelude}goal h: forall {{y = f(x) | p(x)}}. q(y)\n"))
        .expect("image binder elaborates");
    let explicit = elaborate(&format!("{prelude}goal h: forall {{x: Int | p(x)}}. q(f(x))\n"))
        .expect("explicit form elaborates");
    assert_eq!(img.goals, explicit.goals, "`{{y=f(x)|p(x)}}` ≡ the preimage form");
}

/// A non-`f(x)` image expression is rejected (the MVP requires `e = f(x)`).
#[test]
fn image_binder_requires_an_application() {
    let e = elaborate("const c: Int\ngoal h: forall {y = c | y = y}. y = y\n");
    assert!(e.is_err(), "an image binder needs `e` of the form `f(x)`");
}

/// The image binder round-trips through the printer.
#[test]
fn image_binder_round_trips() {
    let src = "const f: Int -> Int\nconst p: Int -> Bool\nconst q: Int -> Bool\n\
               goal h: forall {y = f(x) | p(x)}. q(y)\n";
    let m1 = parse(src).expect("parses");
    let printed = print_module(&m1);
    assert!(printed.contains("{ y = f(x) | p(x) }"), "printed: {printed}");
    let m2 = parse(&printed).expect("re-parses");
    assert_eq!(m1, m2, "image binder round-trips\n{printed}");
}

// ── slice 2i: `preserving` proof shape, end-to-end ──────────────────────

/// The `preserving` proof (`docs/design/SOLVE_BY_PROOF_TERMS.md` §4) composes ALL
/// the pieces end-to-end: refinement types, the refined-arrow postcondition
/// `post_f` (here an explicit axiom `∀x:{A|p}. q(f(x))`), the `solve … by …` cut,
/// and the image binder. `solve G by L` (G = "f preserves p", L = "q ⟹ p on the
/// image", written with the `{y=f(x)|p(x)}` image binder) emits the leaf `L` and
/// the bridge `L ⟹ G` as obligations — the bridge is discharged from `post_f` +
/// `L`, the leaf is the genuine content.
#[test]
fn preserving_proof_shape_composes_end_to_end() {
    let src = "sort A\n\
        const p: A -> Bool\n\
        const q: A -> Bool\n\
        const f: A -> A\n\
        axiom post_f: forall {x: A | p(x)}. q(f(x))\n\
        goal preserved: \
            let pf = solve forall {x: A | p(x)}. p(f(x)) \
                     by forall {y = f(x) | p(x)}. q(y) ==> p(y) \
            in forall {x: A | p(x)}. p(f(x))\n";
    let r = elaborate(src).expect("the preserving proof shape elaborates");
    // one hypothesis (post_f) + three goals (the solve/by leaf, the bridge, and
    // the main goal) — the full §4 cut.
    assert_eq!(r.hypotheses.len(), 1, "post_f hypothesis");
    assert_eq!(r.goals.len(), 3, "leaf + bridge + main goal");
}

// ── slice 2j: the reusable `preserving` higher-order predicate ───────────

/// `preserving` is a **defined higher-order predicate** (not a proof-producing
/// fn): `preserving(p, f) := ∀x. p(x) ⟹ p(f(x))`. In its plainest form the
/// preserved predicate is an ordinary higher-order parameter `p: A -> Bool`, so
/// it is fully reusable today — no generic machinery needed. A definition with
/// an unrefined (`Bool`) return emits NO obligation; the obligation appears only
/// at a USE site, where `preserving(even, dbl)` δ-unfolds to the concrete
/// `∀x. even(x) ⟹ even(dbl(x))` for the engine to discharge.
/// See `docs/design/SOLVE_BY_PROOF_TERMS.md` §7 (design D).
#[test]
fn preserving_as_a_defined_predicate_plain() {
    // the definition itself: 0 obligations (a `Bool`-returning def is just a
    // δ-definition of a Prop-valued predicate).
    all_props(
        "sort A\n\
         fn preserving(p: A -> Bool, f: A -> A): Bool = forall x: A. p(x) ==> p(f(x))\n",
        0,
        0,
    );
    // a use site is one concrete goal (the applied predicate, δ-unfolded at the
    // solver lowering).
    let r = all_props(
        "sort A\nconst even: A -> Bool\nconst dbl: A -> A\n\
         fn preserving(p: A -> Bool, f: A -> A): Bool = forall x: A. p(x) ==> p(f(x))\n\
         goal g: preserving(even, dbl)\n",
        0,
        1,
    );
    assert!(format!("{:?}", r.goals[0]).contains("preserving"), "the goal applies preserving");
}

/// The user's exact surface — `preserving` over a **refined-arrow** argument
/// `f: {u:A|'p(u)} -> {v:A|'q(v)}`, generic in `'p`/`'q`. The refined arrow
/// erases to the value arrow `A → A`, while `'p` and `'q` are collected (even
/// though nested inside the arrow) and bound implicitly as `Π('p)Π('q)` at the
/// head, so the body `∀x. 'p(x) ⟹ 'p(f(x))` may name `'p`. The return is
/// unrefined, so the definition emits NO def-site obligation (resolving the
/// §7 fork: the predicate IS the definition; the `'q⟹'p` leaf is not a
/// def-site goal — it only arises at a concrete use, soundly).
#[test]
fn preserving_over_a_refined_arrow_generic() {
    all_props(
        "sort A\n\
         fn preserving(f: {u: A | 'p(u)} -> {v: A | 'q(v)}): Bool = \
            forall x: A. 'p(x) ==> 'p(f(x))\n",
        0,
        0,
    );
}

/// A use site of the generic refined-arrow `preserving` instantiates `'p`/`'q`
/// (and `f`) explicitly — the dictionary-passing of §5.2 as ordinary positional
/// arguments — and δ-unfolds to the concrete preservation proposition.
#[test]
fn preserving_generic_use_site_instantiates_the_predicate() {
    let r = all_props(
        "sort A\nconst even: A -> Bool\nconst ge0: A -> Bool\nconst dbl: A -> A\n\
         fn preserving(f: {u: A | 'p(u)} -> {v: A | 'q(v)}): Bool = \
            forall x: A. 'p(x) ==> 'p(f(x))\n\
         goal g: preserving(even, ge0, dbl)\n",
        0,
        1,
    );
    assert!(format!("{:?}", r.goals[0]).contains("preserving"), "the goal applies preserving");
}

/// The reusable `preserving` round-trips through the printer (the refined arrow
/// and the generic `'p`/`'q` survive).
#[test]
fn preserving_refined_arrow_round_trips() {
    let src = "sort A\n\
        fn preserving(f: {u: A | 'p(u)} -> {v: A | 'q(v)}): Bool = \
           forall x: A. 'p(x) ==> 'p(f(x))\n";
    let m1 = parse(src).expect("parses");
    let printed = print_module(&m1);
    let m2 = parse(&printed).expect("re-parses");
    assert_eq!(m1, m2, "reusable preserving round-trips\n{printed}");
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

// ── surface `if` (the 2026-07-03 verus-fork proposal, slice ①) ───────────────

/// A value-branch `if` elaborates to the polymorphic `ite` prelude application
/// `(ite T c a b)` — the kernel re-checks it and the whole goal is a Prop.
#[test]
fn if_elaborates_to_the_ite_prelude() {
    let r = all_props("const x: Int\ngoal g: (if x > 0 then x else 0 - x) >= 0\n", 0, 1);
    // the ite head survives elaboration verbatim (the #325 lowering keys on it).
    assert!(format!("{}", r.goals[0]).contains("ite"), "got {}", r.goals[0]);
}

/// A Prop-branch `if` (both branches formulas) is a well-formed Prop — the
/// `T := Prop` instance of the same `ite` constant (no `Bool` inductive).
#[test]
fn prop_branch_if_elaborates() {
    all_props(
        "const p: Bool\nconst q: Bool\nconst r: Bool\ngoal g: if p then q else r\n",
        0,
        1,
    );
}

/// Branch sorts reconcile through the numeric lattice: `if p then 1 else 2.5`
/// injects the Int arm up to Real (the same rule binary operators use).
#[test]
fn if_branches_unify_through_the_numeric_lattice() {
    all_props("const p: Bool\ngoal g: (if p then 1.0 else 2) >= 0.5\n", 0, 1);
}

/// Rejections: a non-Prop condition, and irreconcilable branch sorts.
#[test]
fn if_rejects_bad_condition_and_mismatched_branches() {
    // condition must be Bool/Prop, not Int
    assert!(matches!(
        elaborate("const x: Int\ngoal g: (if x then 1 else 2) >= 0\n"),
        Err(FaceError::Unsupported(_))
    ));
    // Int vs Bool branches cannot unify
    assert!(matches!(
        elaborate("const p: Bool\nconst q: Bool\ngoal g: (if p then 1 else q) >= 0\n"),
        Err(FaceError::Unsupported(_))
    ));
}

/// `if` round-trips through the printer (in operand and top-level position).
#[test]
fn if_round_trips_through_the_printer() {
    let src = "const p: Bool\nconst x: Int\n\
               goal g: (if p then x else 0 - x) >= 0 and (if p then true else false)\n";
    let m1 = parse(src).expect("parses");
    let m2 = parse(&print_module(&m1)).expect("re-parses");
    assert_eq!(m1, m2, "if round-trip\n{}", print_module(&m1));
}

/// The reserved keywords force backtick-quoting for identifier use.
#[test]
fn if_keywords_are_reserved() {
    assert!(elaborate("const if: Int\n").is_err(), "bare `if` as an ident must not parse");
    // backtick-quoted, it is an ordinary identifier.
    assert!(elaborate("const `if`: Int\ngoal g: `if` >= `if`\n").is_ok());
}

// ── surface `match` (the 2026-07-03 verus-fork proposal, slice ②) ────────────

const COLOR: &str = "data Color = red | green | blue\nconst c: Color\n";
const NAT: &str = "data N = zero | succ(pred: N)\nconst n: N\n";

/// An exhaustive datatype match (bare nullary-ctor patterns resolve AS
/// constructors, not binders) elaborates to a kernel-checked Prop.
#[test]
fn exhaustive_datatype_match_elaborates() {
    all_props(
        &format!("{COLOR}goal g: match c {{ red => true, green => false, blue => true }}\n"),
        0,
        1,
    );
}

/// A wildcard `_` catch-all expands into every remaining constructor's minor.
#[test]
fn wildcard_expands_into_remaining_constructors() {
    all_props(&format!("{COLOR}goal g: match c {{ red => true, _ => false }}\n"), 0, 1);
}

/// A binder catch-all `x => …` also NAMES the scrutinee in its body.
#[test]
fn binder_catch_all_binds_the_scrutinee() {
    all_props(&format!("{COLOR}goal g: match c {{ red => true, x => x = green }}\n"), 0, 1);
}

/// Constructor patterns bind fields: `succ(m)`'s body sees `m` (a fresh binder
/// of the field sort), wildcards skip a field.
#[test]
fn constructor_pattern_binds_fields() {
    all_props(&format!("{NAT}goal g: match n {{ zero => true, succ(m) => m = zero }}\n"), 0, 1);
    all_props(&format!("{NAT}goal g: match n {{ zero => true, succ(_) => false }}\n"), 0, 1);
}

/// STRICT exhaustiveness (owner-confirmed §6.5a): an uncovered constructor is
/// a HARD elaboration error naming it — never a fabricated branch.
#[test]
fn non_exhaustive_match_is_a_hard_error() {
    let e = elaborate(&format!("{COLOR}goal g: match c {{ red => true }}\n"));
    match e {
        Err(FaceError::Unsupported(m)) => {
            assert!(m.contains("green"), "names the uncovered ctor: {m}");
            assert!(m.contains("non-exhaustive"), "says non-exhaustive: {m}");
        }
        Err(other) => panic!("expected the non-exhaustive error, got {other:?}"),
        Ok(_) => panic!("a non-exhaustive match must not elaborate"),
    }
}

/// Malformed arm sets are rejected: an unknown constructor (parenthesised
/// form), an arity mismatch, and a bare NON-nullary constructor name.
#[test]
fn malformed_arm_sets_are_rejected() {
    assert!(matches!(
        elaborate(&format!("{COLOR}goal g: match c {{ yellow(x) => true, _ => false }}\n")),
        Err(FaceError::Unsupported(_))
    ));
    assert!(matches!(
        elaborate(&format!("{NAT}goal g: match n {{ zero => true, succ(a, b) => false }}\n")),
        Err(FaceError::Unsupported(_))
    ));
    assert!(matches!(
        elaborate(&format!("{NAT}goal g: match n {{ zero => true, succ => false }}\n")),
        Err(FaceError::Unsupported(_))
    ));
}

/// Guards ride the `ite` fold: a guarded arm needs an unguarded backstop in
/// the SAME constructor bucket (the syntactic rule — never semantic
/// completeness); without one the match is non-exhaustive.
#[test]
fn guards_fold_with_a_syntactic_backstop() {
    // guarded succ-arm + unguarded succ-backstop + zero ⇒ total.
    all_props(
        &format!(
            "{NAT}goal g: match n {{ succ(m) if m = zero => true, succ(_) => false, zero => true }}\n"
        ),
        0,
        1,
    );
    // a constructor reached ONLY by guarded arms is non-exhaustive.
    assert!(matches!(
        elaborate(&format!(
            "{NAT}goal g: match n {{ succ(m) if m = zero => true, zero => true }}\n"
        )),
        Err(FaceError::Unsupported(_))
    ));
}

/// `match c { true => a, false => b }` ≡ `if c then a else b` — the
/// DEFINITIONAL identity: both elaborate to the same `ite` application (no
/// `Bool` inductive is ever declared or touched).
#[test]
fn prop_literal_match_is_definitionally_if() {
    let src = "const p: Bool\nconst q: Bool\nconst r: Bool\n\
               goal g1: match p { true => q, false => r }\n\
               goal g2: if p then q else r\n";
    let m = all_props(src, 0, 2);
    assert!(
        is_def_eq(&m.env, &m.goals[0], &m.goals[1]),
        "match-on-literals must BE the if: {} vs {}",
        m.goals[0],
        m.goals[1]
    );
}

/// A VALUE-valued datatype match kernel-checks (motive lands in `Type(0)`);
/// its verdict is the sound `Unknown` at the lowering (data-valued abstain).
#[test]
fn value_valued_match_elaborates() {
    all_props(
        &format!("{NAT}goal g: (match n {{ zero => 0, succ(_) => 1 }}) >= 0\n"),
        0,
        1,
    );
}

/// `match` round-trips through the printer (patterns, wildcards, guards).
#[test]
fn match_round_trips_through_the_printer() {
    let src = "data N = zero | succ(pred: N)\nconst n: N\nconst p: Bool\n\
               goal g: match n { zero => true, succ(m) if p => m = zero, succ(_) => false, _ => true }\n";
    let m1 = parse(src).expect("parses");
    let m2 = parse(&print_module(&m1)).expect("re-parses");
    assert_eq!(m1, m2, "match round-trip\n{}", print_module(&m1));
}
