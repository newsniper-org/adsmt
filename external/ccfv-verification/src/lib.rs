//! CCFV pre-verification — the three invariants the clean-MBQI never-conclude-unsat
//! firewall and the CCFV inner-search termination rest on, proved on a standalone
//! abstract model **before** the CCFV core (`oxiz-mbqi/src/ccfv.rs`, Phase P1) is
//! implemented. See `external/oxiz/docs/design/CCFV_UNIFIED_INSTANTIATION.md` §12.
//!
//! The three invariants (design §6 / §8):
//!   (i)   YIELD-soundness — when CCFV closes a branch (YIELD), the instantiated
//!         constraint is genuinely entailed: `E ∪ E_σ ⊨ Cσ`. This is what keeps the
//!         engine's `emit`/`instantiate` firewall sound under the new candidate
//!         source — a yielded binding can never assert something the model refutes.
//!         (`spec` module.)
//!   (ii)  Grounding — every bound variable of `C` is mapped by the yielded `σ`
//!         into the term universe `T(E)`. This is what makes the `instantiate`
//!         gate (every replacement must be a registered ground term) satisfiable
//!         by construction, so CCFV never fabricates a witness. (`ground` module.)
//!   (iii) Termination — a well-founded measure `d(C)` strictly decreases on each
//!         search step, so the inner (dis)unification search cannot diverge or
//!         yield infinitely. (`terminate` module.)
//!
//! Fragment coverage: the `spec` module proves YIELD-soundness for the pure
//! equality skeleton (membership / reflexivity / symmetry / transitivity /
//! monotonicity). The `congruence` module **strengthens** this to the full
//! equality-with-congruence fragment CCFV actually matches over: it models a
//! congruence-respecting interpretation (`respects_cong`), proves the **function
//! congruence rule** sound (`entails_cong` — the inference syntactic matching
//! cannot make), and proves the WHOLE congruence-closure discharge a YIELD performs
//! sound by **structural induction over a derivation** (`cong_proof_sound` /
//! `cong_yield_sound`). So "matching modulo congruence" is now verified, not assumed.
//!
//! The `rules` module refines the **actual CCFV rules** — `ASSIGN` (bind a free
//! var to a ground term, the firewall guard) and `DECOMPOSE` (`f(p)≃f(x)⟶p≃x`, the
//! congruence match) — over a real state `(E_σ, pending)` and the paper's variable-
//! depth measure, proving each lowers the measure AND preserves grounding (so (ii)
//! and (iii) hold per-rule, not just at the endpoints).
//!
//! Remaining honest scope (mirroring `oxiz-sat-redesign-verification`'s discipline):
//! the branching rules (U_GEN / R_* / SPLIT), `FAIL`, and the nondeterministic rule
//! scheduler stay abstract (modelled only as "each step lowers a well-founded
//! `nat`"); building/maintaining the congruence closure *incrementally with
//! backtracking* is the EUF solver's job (verified separately, and made desync-proof
//! by the `GroundLedger` of design §10); everything here is `spec`/`proof` (ghost),
//! and the P1 implementation's obligation is to refine these abstract states/steps
//! (후검증).

pub mod spec;
pub mod congruence;
pub mod ground;
pub mod terminate;
pub mod rules;
pub mod diseq;
pub mod capstone;
