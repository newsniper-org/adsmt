# ccfv-verification

Verus **pre-verification** of the CCFV (E-ground (dis)unification) unified
instantiation core for the OxiZ clean-MBQI engine — the
`[선검증 → 구현 → 후검증]` discipline applied before `oxiz-mbqi/src/ccfv.rs`
(design Phase **P1**) is written.

Design doc: `external/oxiz/docs/design/CCFV_UNIFIED_INSTANTIATION.md` (§12).
Sibling of `external/oxiz-sat-redesign-verification` (same style + toolchain pin);
a standalone cargo workspace, **not** part of AD1's cargo workspace.

## What is proved

The three invariants the clean-MBQI **never-conclude-unsat firewall** and the CCFV
inner search rest on (design §6 / §8) — plus the **P4 model-completion** flip's
disequality + completeness + conservative-extension proofs — `41 verified, 0 errors`:

| invariant | module | theorem | why it matters |
|---|---|---|---|
| **(i) YIELD-soundness** (equality) | `src/spec.rs` | `yield_sound` | when CCFV closes a branch, every literal of `Cσ` is entailed by `E ∪ E_σ`, so the engine can never `emit` a binding the model refutes. Built on the sound proof rules `entails_{refl,member,sym,trans,mono}`. |
| **(i+) YIELD-soundness modulo CONGRUENCE** | `src/congruence.rs` | `entails_cong`, `cong_proof_sound`, `cong_yield_sound` | strengthens (i) to the full equality-with-congruence fragment CCFV matches over: models a congruence-respecting interpretation, proves the function-congruence rule (`x≃y ⟹ f(x)≃f(y)`) sound, and proves the WHOLE closure discharge sound by induction over a derivation (`CongProof`). |
| **(ii) Grounding** | `src/ground.rs` | `yield_is_grounded`, `assign_preserves_grounding` | every yielded `σ` maps the clause's bound variables into the term universe `T(E)`, so the `instantiate` gate ("every replacement is a registered ground term") is satisfiable **by construction** — CCFV never fabricates a witness. |
| **(iii) Termination** (abstract) | `src/terminate.rs` | `step_decreases`, `solve_depth` (`decreases`) | a well-founded measure strictly decreases per step, so the inner search cannot diverge — the abstract one-step skeleton. |
| **(iii+) Termination on the REAL rules** | `src/rules.rs` | `assign_decreases`, `decompose_decreases`, `assign_preserves_grounded`, `decompose_preserves_grounded` | refines (iii) onto the actual CCFV rules over a real state `(E_σ, pending)` and the paper's variable-depth measure `d(C)`: **ASSIGN** (bind a free var to a ground term — the firewall guard) and **DECOMPOSE** (`f(p)≃f(x)⟶p≃x`, the congruence match) each strictly lower `d_measure` **and** preserve grounding. So both termination *and* the firewall invariant (ii) are proved per-rule, not just at the endpoints. |
| **firewall capstone** | `src/capstone.rs` | `admissible_yield_is_grounded_and_sound` | an admissible YIELD is **both** grounded (ii) **and** sound (i) — the pair that keeps the firewall intact when CCFV becomes the unified candidate source. |
| **(i) YIELD-soundness (DISEQUALITY)** | `src/diseq.rs` | `r_yield_sound`, `entails_diseq_{member,sym,cong,mono}` | the disequality dual of (i) over a richer context `DCtx{eqs, neqs}`: the `R_VAR`/`R_FAPP`/`R_GEN` rules close a branch on `s ≄ t` soundly exactly when every model separates them. The completeness GATE `flip_is_sound` is *stated* here and *discharged* by the two modules below. |
| **P4 completeness (DOMAIN)** | `src/complete.rs` | `solve_complete`, `no_conflict_when_empty` | THE KEYSTONE. The model-completion flip reads "search found no conflict ⇒ `Sat`"; that is sound only if the search is complete. A BRUTE-FORCE enumeration over the finite witness domain is complete **by construction** (no pruning ⇒ no research-hard `fail_sound`), so "search ∅ ⇒ no conflict over the witness domain". |
| **P4 conservative extension (FRESH)** | `src/model_compl.rs` | `recolor_preserves_dmodels`, `fresh_imposes_no_conflict` | the infinite-sort half: a FRESH element outside the finite domain (one the context mentions nowhere) is entailed neither equal nor disequal to anything — recoloring it preserves every model — so it can never be a missed conflict. Together with `complete.rs`, the flip's `Sat` is sound over the WHOLE uninterpreted sort. |

## How to verify

```sh
# bundled vstd, no network:
verus --crate-type=lib src/lib.rs
# project form (pinned vstd, mirrors oxiz-sat-redesign-verification):
cargo verus verify
```

Both report `ccfv-verification … 41 verified, 0 errors` on system verus
`0.2026.06.07.cd03505`.

## Honest scope (what this does NOT establish)

Mirroring the `oxiz-sat-redesign-verification` discipline — these are pinned, not
hidden:

- **Congruence is now MODELLED, not assumed** (the `congruence` module). The
  earlier "equality fragment only" caveat is lifted: `respects_cong` makes the
  interpretation a congruence, `entails_cong` proves the function-congruence rule
  sound, and `cong_proof_sound` proves the whole congruence-closure discharge sound
  by induction over a `CongProof` derivation. What is *still* the EUF solver's
  obligation (verified separately, and made desync-proof by the `GroundLedger` of
  design §10) is building/maintaining that closure **incrementally with
  backtracking** — this scaffold proves the closure's *rules* sound, not the
  incremental data-structure that produces it.
- **Search rules — ASSIGN + DECOMPOSE are now refined** (the `rules` module), over
  a real state `(E_σ, pending)` and the paper's variable-depth measure; each is
  proved to lower `d_measure` and preserve grounding. `terminate` keeps the
  abstract one-step skeleton as the well-foundedness template. What remains
  abstract: the **equality/disequality branching rules** (U_GEN / R_* / SPLIT) and
  **FAIL** (a dead branch), and the full nondeterministic driver that schedules
  rules — modelled here only as "each step lowers a well-founded `nat`", not the
  concrete branch enumeration.
- **The P4 model-completion flip is verified in both halves** (`complete.rs`
  domain-completeness + `model_compl.rs` conservative-extension), so `flip_is_sound`
  is no longer an open obligation. What gates turning the `ccfv_model_compl` flag on
  by DEFAULT is no longer a *proof* but an empirical sweep: the implementation
  restricts the flip to the pure uninterpreted-sort (dis)equality fragment these
  proofs cover (Bool predicates + arith/BV/array equalities DECLINE), and a corpus
  0-spurious gate (Phase 5) confirms the refinement is faithful before the flip
  ships on.
- **No executable code.** Everything is `spec`/`proof` (ghost). The obligation an
  implementation must discharge is to refine these abstract states/steps — that is
  the P1 후검증 (post-verification) step.

These three invariants are precisely the hypotheses under which the design's §6
soundness argument holds; pinning them here is what lets P1 implement CCFV behind
the existing `Sig`/`TermLang` firewall without re-opening the never-conclude-unsat
question.
