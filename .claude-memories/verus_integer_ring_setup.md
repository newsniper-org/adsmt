---
name: verus-integer-ring-setup
description: "How to use Verus `integer_ring` (Singular Gröbner polynomial-ring proofs) in this project — the exact binary, env var, attribute syntax, and the raw-poly-lemma+spec-fn-wrapper pattern; for 선검증 of degree-3+ polynomial ring identities that nonlinear_arith's nlsat cannot close."
metadata:
  node_type: memory
  type: reference
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**Use `integer_ring` for exact polynomial RING IDENTITIES** (degree-3+, many vars) that Verus's `nonlinear_arith` (nlsat) can't close (it exhausts rlimit — nlsat is for sat-with-ordering, not identity normalization). Singular does Gröbner-basis reasoning → instant on true ring identities. Worked example: the `*Like` complex reduction algebra 선검증 (`~/complexlike-verification`, #339) — `mul_associative` (deg-3), `norm_multiplicative` (deg-4) closed with `integer_ring` after nlsat failed even on degree-4 Brahmagupta–Fibonacci.

**THREE things must all be right (each cost a debug cycle 2026-06-28):**
1. **Binary** = the locally-rebuilt fork with the `singular` Cargo feature: `/home/ybi/verus-fork/source/target-verus/release/verus`. **NOT `/usr/bin/verus`** (→ `/opt/verus/verus`, v0.2026.06.07) — that's built WITHOUT the feature and reports `integer_ring` as "unknown prover name". The fork's `tools/activate` ALSO resolves `which verus` → `/usr/bin/verus` (wrong) — invoke the rebuilt binary by ABSOLUTE PATH. Feature decl: `rust_verify/Cargo.toml` `singular = ["vir/singular", "air/singular"]`. (Singular itself: `pacman -S singular` → `/usr/bin/Singular`.)
2. **Env**: `VERUS_SINGULAR_PATH=/usr/bin/Singular` (else: "Please provide VERUS_SINGULAR_PATH to use integer_ring attribute").
3. **Syntax** = a FUNCTION ATTRIBUTE `#[verifier::integer_ring]` on an **empty-bodied `proof fn`** whose `ensures` is the polynomial equation — NOT `assert(...) by(integer_ring)` (that's an unknown prover; the by-provers are only compute/compute_only/bit_vector/nonlinear_arith).

**Pattern — Singular does NOT unfold `spec fn`s**, so state the identity over raw `int`:
```rust
#[verifier::integer_ring]
proof fn foo_poly(a:int, b:int, c0:int, re:int)
    requires re == a*c0 - b,                          // intermediate products as `requires`
    ensures re*re == a*c0*a*c0 - 2*a*c0*b + b*b,      // the raw-int polynomial identity
{}                                                    // empty body; Singular discharges `ensures`
pub proof fn foo(a:int, b:int, c0:int)                // thin spec-fn wrapper
    ensures norm(mk(a,b,c0)) == ...,                  // spec fns here (open ⇒ unfold)
{ foo_poly(a, b, c0, mk_re(a,b,c0)); }                // instantiate; unfolding matches
```
The `requires` equations form the ideal Singular reasons modulo. Pass `re`/`im` instantiated at the (open) spec-fn calls; their unfolding satisfies the `requires`, and the wrapper's spec-fn `ensures` follows by unfolding the raw conclusion. integer_ring `ensures` must be EQUATIONAL; a divisor needs a `!= 0` precondition. Inequalities / `t²=0⟹t=0` / `x·y=0∧x≠0⟹y=0` stay `nonlinear_arith` (with sign case-splits spelled out). Run via the `justfile` (`verus :=` + `export VERUS_SINGULAR_PATH :=`). See [[numberlike-family-design]].
