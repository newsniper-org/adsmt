# SAT-level refutation witnesses are bound to their step (2026-11-08)

**Defect (found by the lu-kb design survey, HOLE-A).** `Certificate::recheck`
replayed a `TheoryWitness::Drat` by running its DRAT checker on the witness's
own integer clauses and nothing else. It never related that clause set to the
step it sat in, so a certificate could be edited at will — a hypothesis
dropped, the conclusion replaced, `hyps = []`, `parents = []` — and still
report `PASSED, 1 witness re-verified, 0 taken on faith`. `recheck() == Ok` was
therefore not an admission test (an importer would have admitted `|- false`
from nothing).

**Fix.** `TheoryWitness::Drat` now carries `atoms` (variable `i + 1` is
`atoms[i]`; `#[serde(default)]`, so older certificates read as UNBOUND). The
checker (`adsmt_cert::recheck::check_drat`):

1. replays the proof (RUP, reaches the empty clause);
2. an unbound witness (no `atoms` although a clause mentions a variable) is
   valid DRAT but is counted **taken on faith**, never re-verified;
3. a bound witness must sit in a step that concludes `false`, whose hypotheses
   include every parent's hypotheses;
4. the CNF of the step's premises (parents' conclusions and the step's own
   hypotheses) is **re-derived by the checker** with `adsmt_cert::cnf`
   (moved here from `adsmt-engine`, re-exported there), and every clause of the
   witness, read through `atoms`, must be one of those clauses. The premises
   then entail the clause set, so refuting it refutes them;
5. a premise that mentions the translator's reserved namespace `!tseitin!…`
   is rejected (it could capture an auxiliary definition it does not entail);
   a duplicated atom in the map, or a clause over a variable outside it, is
   rejected.

**Trusted base.** The CNF translator is now part of what a certificate is
checked against. A wrong translator would be trusted by both sides. Its
soundness is argued in the module docs (Tseitin atoms are content-named and
fresh) and exercised by the engine's differential tests; it is *not* yet
formally verified.

**Engine.** The solver emits `atoms` from the clauses it solved, keyed by the
atom `Term` itself (not its printed form). With a baked AOT prelude the clause
set holds prelude clauses that are not among the step's premises, so the
engine leaves the witness unbound: such certificates now count as faith, which
is what they are (their sequent does not list the prelude as hypotheses).
Listing the prelude assertions as hypotheses of the step would bind them; that
is a follow-up.

**Measured** (head `lu-smt 532649c9…`): 264 pure-SAT unsat certificates verified
with 0 on faith; 1392 lens-corpus unsat certificates, 842 DRAT steps, none
unbound (the 5 failures are pre-existing EUF-witness rejections, identical on
the pre-change binary); 12 mutation families × 40 certificates — every forgery
(drop-hyp, no-hyps, no-hyps-no-parents, concl-swap, flip-literal, extra-clause,
swap-atoms, trunc-atoms, no-lemmas) rejected, `no-atoms` falls to faith; the
two mutations that still verify (dropping a clause from the set, dropping the
parents while the hypotheses stay) are weaker-but-true claims, not forgeries.
Unit tests: `recheck::tests::{a_bound_drat_witness_is_verified,
forged_drat_steps_are_rejected, a_clause_the_premises_do_not_give_is_rejected,
a_premise_in_the_translators_reserved_namespace_is_rejected,
a_malformed_atom_map_is_rejected, a_refutation_through_tseitin_definitions_is_bound,
an_asserted_false_is_bound_without_any_atoms,
an_unbound_drat_witness_is_valid_but_counted_as_faith}`.

**Not covered.** Other witness kinds (`Opaque`, `LinArith` on faith, …) still
do not tie `result.hyps` to their parents; only DRAT is bound here.
