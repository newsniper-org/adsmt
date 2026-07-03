# repro — fuel-guarded definitional-unfolding MBQI gap (verus-SAFE)

The lu-kb (`adsmtc`) path and `lu-smt` both return `unknown`/fail where **z3
verifies (3/0)**, on an obligation whose term-`ite` sits behind a *fuel-guarded
quantified definitional axiom*. Not an emit issue (the `if` renders faithfully),
not a feature issue (cas+oxiz confirmed active: nlsat perfect-square → unsat,
`prime(7)`+`ADSMT_CAS_MANIFEST` → unsat), not the ite lowering (a *direct* ite
obligation verifies). It is MBQI/trigger completeness on the **fuel-unfolding**
pattern — the dominant Verus obligation shape.

## Files
- `diff.rs` — the Verus fixture (a spec `abs` defined with `if`, a spec `code`
  defined with a Rust `match`, and two proof obligations over them).
- `ob1-abs.lukb` — the emitted, ISOLATED `abs_nonneg` obligation (shared prelude
  + the single goal `abs?(I(x!)) >= 0` under `axiom: fuel_defaults`).

## Reproduce
```
# z3 (ground truth): verifies
verus diff.rs                                   # → 3 verified, 0 errors

# lu-smt (-V adsmt): trails z3 on the fuel-unfolding obligations
VERUS_ADSMT_PATH=~/AD1/target/release/lu-smt verus -V adsmt diff.rs
                                                # → 1 verified, 2 errors (abs_nonneg, code_bounds)

# adsmtc (lu-kb path): the isolated obligation
adsmtc ob1-abs.lukb                             # → unknown   (want: unsat)
```

## The gap
The prelude carries `fuel_bool(fuel%abs) ==> (forall x. abs?(x) = if %I(x)>=0
then %I(x) else Sub(0,%I(x)) trigger abs?(x))`; the goal is `abs?(I(x!)) >= 0`
under only `axiom: fuel_defaults`. Discharging it needs (1) chasing the fuel
chain `fuel_defaults ⟹ fuel_bool = fuel_bool_default` to license the guard, then
(2) trigger-instantiating the definitional ∀ on `abs?(I(x!))`, then (3) the
unfolded-ite reasoning (which works standalone). Steps (1)+(2) are the gap.
Direction is SAT/unknown ⇒ verus-SAFE (never a false proof).
