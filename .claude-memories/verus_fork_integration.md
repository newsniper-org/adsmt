---
name: verus-fork integration as lu-smt's primary downstream
description: Verus fork (~/verus-fork) consumes lu-smt as an SMT backend via `verus -V adsmt`; the rc.7→rc.28 arc has been driven by closing the gap end-to-end. rc.10 hash-cons; rc.12 T0; rc.13/14 §3.4 Buchberger+F4+plugin; rc.15 §3.1.A-D + §3.2/§3.3 skeletons + §3.4 CLI; rc.16 §3.5.A-G end-to-end + T0'.1-.3; rc.17 promoted §3.5 v0→v0.x + §3.2 dynasm-rs + §3.3 phase 2 + Stålmarck trailing; rc.18-19 verus-fork retry follow-ups; rc.20 §3.5.J gate clause-only half; rc.21 verus-fork rc.20 retry's three priorities all land; rc.22 verus-fork rc.21 retry §(d) Arc::ptr_eq fast paths in alpha_eq_rec + Type::eq; rc.23 verus-fork rc.22 retry §4 UF iter().any(alpha_eq) → IndexSet (e''.1/2/3); rc.24 verus-fork rc.23 retry — ematch::TermUniverse Vec→IndexSet (real hot site one crate over) + workspace-wide cold sweep; rc.25 verus-fork rc.24 retry found the *correct* ematch fix unmasked UF::close()'s naive O(N²) congruence closure (wall UP 7×): (e⁗.1) signature-hashed congruence + (e⁗.2) Arc::ptr_eq roots + (T0''') theory-phase deadline cascade; rc.26 verus-fork rc.25 retry confirmed `:rlimit` EXACT (1s→1011ms) + UF off flamegraph, user landed (e⁗⁗.1/.2) UF derive_equalities HashSet dedup directly (∞→finite), then the chain reached the E-matcher tail: (e⁗⁗.3) ematch/quant_conflict matcher binding + substitute_in alpha_eq→== + (e⁗⁗.4) Combination::check NO-dedup Vec→HashSet + (T0'''') extend_with_equalities deadline.  MILESTONE: SMT-solving hot path FULLY de-quadratified (rc.21→rc.26 throttle-unmask chain terminates).  rc.27 verus-fork rc.26 retry confirmed the perf milestone (deadline budget-exact at every rlimit) but found the real §3.5.J blocker was a P0 SOUNDNESS bug, not performance: opaque OR-of-AND assert + `(assert false)` → unsound `sat` (had masked verus_smoke's trivial unsat across the whole rc.7→rc.26 arc).  Fixed by (S.1) keep-flattenable-subset + had_opaque Sat→Unknown downgrade + (S.3) propositional-false short-circuit; verus_smoke now returns `unsat`.  (S.2) Tseitin OR-of-AND deferred.  rc.28 verus-fork rc.27 retry was the §3.5.J FUNCTIONAL SUCCESS — `verus -V adsmt` → `1 verified, 0 errors` 511ms (baseline verus_smoke `unsat` 8ms, three orders inside the ≤1500ms window, the P-vb finish line + quantitative close of the rc.7→rc.27 perf arc) — but found the rc.27 (S.1) fix never reached the `--aot-load` path: a baked opaque OR-of-AND + `(assert false)` made AOT-load drop the empty clause → `sat`-for-unsat (baseline `unsat` vs aot `sat` at 1/8/16/19/24 opaque asserts).  rc.28 (S.1-AOT) extends (S.1) to the AOT path: `restore_cdcl_state_into` keeps genuine empty clauses (explicit `ok` flag) + a trailing v1.2 `CdclSection::had_opaque` wire field threads the bake-time opaque flag → `Solver::aot_prelude_had_opaque` → seeds `check_ground`'s `had_opaque`.  Divergence table fully closed; 951/951 green.  CONFIRMED by verus-fork rc.28 retry (mirror 6491a58, verus-fork c1b06735): all three paths (baseline / AOT / JIT) sound — full verus_smoke `--aot-load` → `unsat` 13ms (was `unknown`), JIT-over-AOT → `unsat`, and the §3.5.I AOT env path (`VERUS_ADSMT_AOT_LUART` → `--aot-load`) drives `verus -V adsmt` → `1 verified, 0 errors` 530ms — §3.5.I proven sound end-to-end, **DONE**.  Only §3.5.H (vargo post-build bake hook) remains before the per-query AOT win is automatic.  rc.29 = verus-fork (S.2) Tseitin OR-of-AND — the last completeness gap before v1.0.  `flatten_to_clauses` returned `None` on nested OR-of-AND → `Unknown` where z3 says `unsat` (sound but incomplete; witness `(or (and P (not P)) (and P (not P)))`).  (S.2) = standard Tseitin in cnf.rs: conjunction-in-disjunct → fresh content-named aux `aux ⟺ subformula` (`!tseitin!<subterm>`; per-call counter would alias sub-formulas onto the same hash-consed Term → unsound), const-folded, equisatisfiable, linear.  All three paths inherit completeness (bake side bakes real clauses, `had_opaque` degrades to deadline/size only).  Audited: witness → unsat on baseline+AOT+JIT; `(or P (and Q R))` → sat; rc.27 repro + rc.28 divergence table stay unsat; 951→956 green.  CONFIRMED by verus-fork rc.29 retry (mirror 78a7bf5): (S.2) holds on all three paths; full verus_smoke baseline+AOT → unsat; driver `1 verified, 0 errors`.  STATUS CORRECTION: §3.5.H is ALSO already DONE (verus-fork `5533adfe`) — implemented as a frontend-agnostic `scripts/aot-bake-prelude.sh` + `just aot-bake-prelude` (NOT a vargo-internal hook; Y4 unification keeps adsmt the common engine so the AOT bank stays Verus-independent — bakes `--from-verus` default or `--from-smt2`, caches under `$VERUS_ADSMT_AOT_CACHE_DIR`; bake→activate→verus = `1 verified, 0 errors` 292ms vs 511ms unbanked).  **MILESTONE: every technical item across the rc.7→rc.29 arc is now landed on BOTH sides** (P-vb.1-8, §3.1, §3.5.A-J, T0'/T0''', the rc.21→26 de-quadratification, rc.26→28 P0 soundness + AOT + JIT, rc.29 (S.2) completeness).  The ONLY remaining gate for the v1.0.0 stable cut = the formal completeness/soundness audit-sweep scope (rc.29 + verus-fork audits cover the key cases; broader corpus e.g. real Y4 obligations / adsmt-contrib emit round-trip is the sign-off-holder's call) + explicit user sign-off (NOT the §3.5.J functional-success milestone).  POST-rc.29 (Y4-driven, but verus-fork pins EXPECTED_ADSMT_VERSION): rc.30 (Y4 datatypes + vstd surface + OxiZ delegation) surfaced a verus-fork-side **driver crash on a *fast* `unknown`** — **CLOSED both sides 2026-06-09**.  Real trigger was one layer below the `Canceled` arm I forwarded: `air/src/smt_verify.rs:579` `smt_get_model`'s `discovered_error.expect()` — `(:reason-unknown "(incomplete …")` routes to `Undetermined(false)`→treated-as-sat→`(get-model)`, lu-smt's no-model error missed the Z3-canonical `"model is not available"` substring → empty-model parse → `.expect()` panic → `PanicOnDropVec` re-panic → abort.  verus-fork fix = `Some(...) else { Invalid }` (solver-agnostic, no soundness guard weakened, fast-`unknown` → `0 verified, 1 errors`); adsmt **rc.32.1 cosmetic** (`2a315be`, no bump) = reword the get-model error to the canonical substring so air takes its cheap not-verified shortcut.  rc.32 added the **`--emit-cert`/`--emit-cert-dir`(= the `ADSMT_CERT_DIR` hook target)/`--emit-cert-format`** producer surface for the `-V emit-isabelle/rocq` chain; the verus-side `-V emit-*` argv/env wire is a SEPARATE cycle, NOT yet landed (producer side already unblocks it).  verus-fork `EXPECTED_ADSMT_VERSION` → **rc.32.1**.  rc.32.2/.3 + rc.33 (P0 theory-atom soundness + OxiZ simplex pop bug + `external/oxiz` → 0.2.4 base + R7.11 cert-emit gaps A/B) closed the cert-emit pipeline; verus-fork P2 `-V emit-isabelle/rocq` wire landed, gaps A/B/B′ confirmed end-to-end (real obligation → cert.cbor → .thy + .v).  **rc.34 = §3.5 JIT-on-AOT replay CLOSED on adsmt's side** (§3.5.F real event replay + `(check-sat)` consult; §3.5.E canonical GF(2) signature **exact-match** verdict cert — see [[jit-aot-replay-section-3-5]]).  **CONFIRMED by verus-fork 2026-06-10** (`.local-replies-from/verus-fork/2026-06-10-rc34-pin-emit-pipeline-regression-clean-jit-3.5HJ-queued.md`): pinned **`EXPECTED_ADSMT_VERSION` → rc.34**, rebuilt lu-smt + adsmt-emit runtime + contrib wasm + verus (vstd 1690 green); **emit pipeline regression-clean** (gaps A/B/B′ stay closed on rc.34, cert wire + `-V adsmt` verdicts unchanged from rc.33, as flagged — a regression check not a re-validation).  §3.5.E/F replay acknowledged LIVE; §3.5.I already done (argv threads `--aot-load` + `--jit-trace-load` off env vars + `-V jit-trace-load` config alias); **§3.5.H** (extend `scripts/aot-bake-prelude.sh` to also `lu-smt --jit-trace-emit` the warm-up query + stage the `.lutrace`) **+ §3.5.J** (5-mode smoke retry; threshold should drop) QUEUED as verus-fork's next cycle.  **THEN verus-fork ran §3.5.J (2026-06-10) and the consult NEVER short-circuited — every mode fell through (NOT a no-adsmt-action cycle after all).** verus-fork landed §3.5.H (`scripts/aot-bake-prelude.sh` now also bakes the warm-up `.lutrace`) + §3.5.I, ran the 5-mode matrix: tight-rlimit rows stayed `unknown`, replay always `GuardsPassed`.  Root cause = TWO adsmt-side bugs the rc.34 unit tests masked (they hand-built traces with pool *indices* as atoms, never the real recorder): **(A)** recorder writes `atom_key_hash_u32(term)` (content HASH) but `replay_events` indexed `aot_pool_terms[atom]` (pool POSITION) → always `diverged`; bank-only pool also omitted per-query atoms; **(B)** CDCL returns Unsat on a ROOT conflict without calling `on_conflict` (can't 1-UIP a root contradiction) → no terminal `Conflict` event → `root_conflict` stayed false.  **rc.34.1 fix** (`deb7e11`, bump `52dad19`): `replay_events(events, atom_map: &HashMap<u32,Term>)` resolves via new `Solver::live_atom_map()` over the FULL live formula (bank ∪ query) keyed the same way + collision flag; the session-boundary fallback appends `Restart`+level-0 `Conflict` to non-empty Unsat traces; the `level0_falsifies_prelude_clause` backstop is gated to empty-signature + collision-free (exact-match stays the sound primary).  Regression `real_recorder_trace_replays_through_hash_atom_map` exercises the real recorder→replay round-trip (the missing test); CLI-verified bake→emit→`--aot-load`+`--jit-trace-load`→unsat; 1070 green.  PROCESS LESSON: a replay unit test that hand-builds the trace payload can pass while the real record→emit→load→replay path is fully broken — always round-trip through the real producer.  Reply: `.local-replies-to/verus-fork/2026-06-10-rc34.1-section-3.5J-fix-atom-key-and-terminal-conflict.md` (pin **rc.34.1**, re-bake, re-run; tight-rlimit rows should flip to `unsat`).  See [[jit-aot-replay-section-3-5]].  Determinism caveat (run-to-run atom names) is ruled out as the cause.  **§3.5.J CONFIRMED by verus-fork on rc.34.1 (2026-06-10)** — re-baked the trace + re-ran the 5-mode matrix: tight-rlimit rows (1/10/100) flipped to `unsat`, RLIMIT-INDEPENDENT (consult returns the recorded verdict, no search); the JIT-on-AOT-prelude arc is **functionally closed**.  `EXPECTED_ADSMT_VERSION` → rc.34.1.  Caveat: the wall *win* is fixture-gated — verdict-independence is unconditional but the consult costs ~0.45 s (trace load + live `canonical_gf2_signature` recompute) vs a 0.021 s native solve of a trivial tautology, so it's net-positive only when the skipped search exceeds the consult (a heavy obligation, not `a‖¬a`).  **rc.34.2 = slim-trace (verdict-only), LANDED** — the dominant consult cost was the 3.5 MB full trace (the whole propagation stream), which the exact-match route never reads.  `lu-smt --jit-trace-emit-slim <PATH>` emits — on a clean Unsat only — just the §3.5.E signature + a synthetic `[Restart, Conflict@0]` (`Solver::build_slim_jit_trace`), dropping the `Decide`/`Propagate`/`Backjump` stream (MB → hundreds of bytes); no recorder installed.  Sound by construction (a slim trace carries a signature → exact-match route → never reaches the empty-signature-gated backstop).  Regression `slim_trace_is_verdict_equivalent_to_full_and_tiny`; CLI-verified; verus-fork's bake script uses `slim` unconditionally (one-line flag swap).  1070 → 1071 green.  **rc.34.3 = signature digest (the real lever).** verus-fork's rc.34.2 measurement re-scoped it: slim dropped only **0.6%** of a prelude trace; the §3.5.E GF(2) signature is the other **99.4%** (one polynomial per clause × thousands), so slim moved neither the consult wall (~0.45 s) nor the bake (~2.03 s).  Fix: replace the megabyte basis with a **32-byte canonical clause-set digest** (`Solver::jit_trace_digest`, KangarooTwelve-256 via `lu_common::k12`; new adsmt-engine dep) — both wire (basis dropped from full+slim; `.lutrace` v2 trailing `signature_digest`) AND compute (the digest hashes the canonical clause set, skipping the GF(2) polynomial encoding; consult's `canonical_gf2_signature` is now lazy/guards-only).  Consult exact-match = `signature_digest == Some(jit_trace_digest())`; legacy v1 → GF(2) `(classes,basis)` fallback.  Sound (same exact-formula-match via a collision-resistant hash).  3 regressions; CLI-verified (full 113 B / slim 99 B tiny; real prelude collapses from MB).  1071 → **1074** green.  Reply: `.local-replies-to/verus-fork/2026-06-10-rc34.3-signature-digest-landed.md`.  See [[jit-aot-replay-section-3-5]].  **rc.34.4 = incremental clause-fold digest (the consult goes O(query delta)).** verus-fork re-baked on rc.34.3 (`.local-replies-from/verus-fork/2026-06-11-rc34.3-digest-collapses-trace-but-consult-now-compute-bound.md`): the digest collapsed the trace (3.5 MB → 99 B) and verdict-independence held, but the consult wall was UNCHANGED (~0.42 s) — they isolated it as the live digest COMPUTE, since `jit_trace_digest` still re-canonicalised the WHOLE prelude∪query formula (CNF-flatten + sort + dedup thousands of prelude clauses) on EVERY `(check-sat)`.  Fix: an order-independent **clause-fold** — each clause hashed by ATOM NAME (`clause_name_hash`, K12-256, so a clause's hash is independent of the rest of the formula) combined into a `(sum,count)` **AdHash** multiset accumulator (`clause_set_fold`: K12 hashes added mod 2²⁵⁶, NOT XOR — XOR self-cancels duplicate clauses + is linear-collidable, and the digest is soundness-critical).  The fold is an exact multiset homomorphism, so the **prelude fold is precomputed ONCE at `--aot-bake`** into the bank trailing **v1.3 `CdclSection::prelude_clause_fold`** (`at_end()`-gated like rc.28 `had_opaque`; older banks recompute once at `--aot-load`) → each `(check-sat)` folds only the per-query delta + `combine`s = O(query).  `.lutrace` unchanged (still v2; digest computed differently, stored identically).  5 regressions; CLI-verified (bake → `--aot-load` + `--jit-trace-load` → unsat short-circuit).  1074 → **1080** green.  verus-fork scoping: O(delta) mainly helps the **exact re-run** case (re-verifying unchanged code vs a warm bank) = what §3.5.J targets.  Reply: `.local-replies-to/verus-fork/2026-06-11-rc34.4-incremental-clause-fold-digest.md`.  **rc.34.5 = precomputed prelude atom map (the LAST prelude-scale consult term).** verus-fork re-baked rc.34.4 (`.local-replies-from/verus-fork/2026-06-11-rc34.4-digest-O-delta-but-live-atom-map-is-the-residual.md`): the digest fold is O(delta) ✓ but the consult wall stayed ~0.38 s — they isolated it as `live_atom_map()` (the §3.5.F replay's content-hash→`Term` resolver), which rebuilt a map over the WHOLE bank∪query formula every consult.  Fix (their lever 2): precompute the prelude atom map ONCE at `--aot-load` (`Solver::aot_prelude_atom_map`, built in `with_aot_cdcl`) and CHAIN a small per-query map (`query_atom_map`, prelude `Term`s skipped) over it via a resolver closure — `replay_events` now takes `resolve: impl Fn(u32)->Option<Term>`, no clone.  Slim/digest traces reference no query atom → replay never touches the prelude → consult is O(query delta).  No wire/bank change; synthetic 4002-clause prelude consult marginal `(3)−(2)` ≈ 0 ms (was prelude-scale).  2 regressions; CLI-verified; 1080 → **1082** green.  Reply: `.local-replies-to/verus-fork/2026-06-11-rc34.5-precomputed-prelude-atom-map.md`.  **rc.34.6 = AOT-only path un-taxed.** verus-fork measured rc.34.5: §3.5.J consult `(3)−(2)`≈0 ms ✓ but the prelude atom-map build ran on EVERY `--aot-load` (it was in `with_aot_cdcl`), regressing the AOT-only `verify-adsmt-fast` path ~0.019 s → ~0.40 s for a map only the trace path reads.  Fix: gate the precompute on a loaded trace — moved to `set_loaded_jit_trace` (`build_prelude_atom_map`).  Bare `--aot-load` builds nothing; JIT sessions amortize the one-time build.  No wire/bank change; 1083 green.  Reply: `.local-replies-to/verus-fork/2026-06-11-rc34.6-gate-prelude-atom-map-on-loaded-trace.md`.  **rc.35 = abductive-reasoning SMT-LIB surface (NOTICE, not a request-driven fix).** Exposes adsmt's `Abductive` verdict as explicit cvc5-compatible commands — `(declare-abducible <pattern> [<expl>])`, `(abduce <goal>)` (native ranked JSON), `(get-abduct <name> <goal>)` (cvc5; `(define-fun … Bool …)`), `(get-abduct-next)` (cursor) — so Verus can ASK what hypothesis would discharge a failed/`unknown` obligation, not just receive sat/unsat/unknown.  air ALREADY parses the `abductive` JSON (`air/src/smt_verify.rs::parse_abductive_candidates_line`); the gaps left on the VERUS side are (1) ISSUE `(get-abduct …)` on a failed obligation, (2) emit `(declare-abducible …)` for in-scope vars/lemmas so abducts are actionable, (3) back-translate the abduct to Verus surface syntax for a diagnostic/code-action.  Abduct is ADVISORY — the user justifies it (requires/invariant/lemma), never auto-assumed; deductive `unsat` stays the trusted verdict.  Notice: `.local-replies-to/verus-fork/2026-06-11-rc35-abductive-smtlib-surface-get-abduct.md`.  See [[abductive-smtlib-surface]].  **rc.35.1** = verus-fork acked rc.34.6 (AOT-only restored, `(2)` 0.40s→0.019s — §3.5 perf arc CLOSED) + filed a verify-or-explain DESIGN (A2a request-wire → A2b VIR vocabulary → A2c back-translate+code-action; no code this cycle) with 3 questions. Answered: (1) `(abduce G)` takes G=the goal P not ¬P (H⊢goal=precondition strengthening; derivation-based so the abduct must be re-checked — F-consistency not enforced); (2) `(get-abduct)` emits one `(define-fun)`/`(fail)` line; (3) added a re-parseable `term` field to the ranked JSON (`term_to_smtlib`) so A2a+A2c share one parser. 1090 green. Reply: `.local-replies-to/verus-fork/2026-06-12-rc35.1-reparseable-term-and-design-answers.md`.  Then verus-fork accepted all 3 answers + REQUESTED **consistency-enforced abduction** (the re-check is necessary-not-sufficient: a vacuous H inconsistent with F passes `F∧H⊨P` vacuously → misleading `requires x>0 ∧ x<0`).  Implemented (NO bump, on rc.35.1): opt-in `(set-option :abduct-consistency true)` → engine `SAT(F∧H)` per candidate (push/assert/check-sat/pop, drop only proven-Unsat); `(abduce)` JSON adds a `consistent` field, `(get-abduct)` drops inconsistent (cvc5 semantics).  Engine-side avoids the consumer's N SmtProcess round-trips.  CLI-verified; 1091 green.  Reply: `.local-replies-to/verus-fork/2026-06-12-rc35.1-consistency-enforced-abduction-landed.md`.  Then verus-fork filed a **streaming-robustness REQUEST** (`.local-requests-from/verus-fork/2026-06-12-request-abduce-must-not-exit-on-parse-error-streaming.md`): `(abduce <term>)` with an unparseable/unknown-operator term EXITS lu-smt (code 13) instead of report-and-continue → kills verus's persistent streaming session (reader RecvError, never sees `<<DONE>>`); blocks A2a.  Same class as the 2026-06-08 fast-unknown crash.  Root cause = MY rc.35 dispatch: `Command::Abduce`/`DeclareAbducible` returned `DispatchResult::Error(13,…)`, which the streaming loop exits on UNLESS OxiZ is configured (pre-rc.35 `(abduce)` was `Raw` → non-strict warn+continue, so rc.35 introduced it).  Fixed (NO bump): `Driver::recoverable_command_error` — the abductive READ-ONLY query commands report on stderr + `Continue` (sound: they touch neither the assertion stack nor any verdict; `(assert)` stays exit-without-OxiZ = the sound refusal); `--strict-commands` still fatal.  Integration test `adsmt-cli/tests/streaming_robustness.rs` (spawns the binary on the exact repro).  1091→1094 green.  See [[feedback-streaming-no-exit-on-command-error]].  Reply: `.local-replies-to/verus-fork/2026-06-12-streaming-robustness-abduce-no-exit-fixed.md`.  Then verus-fork filed an **engine REQUEST — theory-aware abductive SEARCH** (`.local-requests-from/verus-fork/2026-06-12-request-theory-aware-abduction-search.md`): the abduce *search* is syntactic (SLD/α-match+Horn), so `x>0 ∧ y>0 ⊬ x+y>0`, `x>0 ⊬ x≥1` → `[]`; verus obligations are all theory/arithmetic → SLD abduce empty on all of them, A2 useless.  Implemented (NO bump, opt-in): `(set-option :abduct-theory true)` → `Driver::abduce_theory` bounded minimal-subset search over declared abducibles for `F∧H⊨G` (=`F∧H∧¬G` unsat, dual of the consistency check) + `SAT(F∧H)` = full cvc5 get-abduct.  **OPT-IN chosen after comparing opt-in/opt-out/always:** SLD & theory are complementary not nested (SLD's Horn rule base is F-independent → theory-as-default would drop SLD candidates Lean/T4 rely on), theory pays a check-sat per subset, and it's symmetric with opt-in `:abduct-consistency`.  6 integration regressions (`adsmt-cli/tests/theory_abduction.rs`).  1094→1100 green.  See [[abductive-smtlib-surface]].  Reply: `.local-replies-to/verus-fork/2026-06-12-theory-aware-abductive-search-landed.md`.
type: project
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
A user-maintained Verus fork at `~/verus-fork/` carries an
`adsmt` backend option (`verus --crate-type=lib -V adsmt`) that
shells out to `lu-smt` as a subprocess.  Since rc.7 (2026-06-03)
the lu-smt RC churn has been dominated by closing the gap between
"Verus emits a full Z3-style prelude + check-sat session" and
"lu-smt ingests every command in the session without bailing".

**Why:** Verus is the primary external pressure on lu-smt's
SMT-LIB v2 surface — Z3 / cvc5 already swallow these inputs,
lu-smt was the lone backend dropping them, and the long-running
verification sessions Verus generates expose all the streaming /
budget / surface-coverage gaps at once.  The
`.local-requests-from/verus-fork/` inbox is the joint working
surface for cross-project asks.

**How to apply:**
- When parser / CLI / engine changes look like they target
  "things the SMT-LIB spec already requires," check whether
  Verus drove the discovery — Z3-style preludes
  (`(set-option :rlimit N)`, `:pattern` / `:qid` / `:skolemid`
  annotations on quantifier bodies, numeric literals at sort
  Int, attributed expressions `(! expr :kw v)`) all came in
  through this path.
- Streaming behaviour matters: subprocess consumers hold stdin
  open across an entire session and rely on
  `(echo "<<DONE>>")` sentinels to delimit response batches.
  Buffering to EOF deadlocks both sides — every IO-touching
  change should preserve the per-command flush from
  `602192a`.
- The keyword-parsing convention bit one feature in rc.9:
  `adsmt_parser::sexpr::tokenise` strips the leading `:` off
  every keyword, so `match` arms like `":rlimit"` are dead
  code — write `match` arms against the bare form (`"rlimit"`).
- The verus-fork side may park progress on `P-vb.8.*` retry
  cycles waiting for landed adsmt changes — coordinate via
  the inbox `§ 6 cross-side migration ledger` rather than
  guessing.

## Active request (2026-06-04, status: adsmt-side complete, awaiting verus-fork retry)

Request file:
`.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`
(last revised 2026-06-04T12:17 — §3.2 and §3.4 sharpened into a
shared `GF(2)` Gröbner kernel).

Reply filed:
`.local-replies-to/verus-fork/2026-06-04-engine-refactor-r1-through-hashcons-status-update.md`
(commit `7b26047`), mirrored to verus-fork via `just
mirror-local-replies-to verus-fork
~/verus-fork/.local-replies-from/adsmt/`.

**Diagnostic anchor (§1, post-landing clarification):**
`verus -V adsmt` smoke busy-loops at 100% CPU.  Trace localises
to `crate::quant::collect_universe → gather_subterms` doing
`u.insert(t.clone())` per node.  Our re-read against the
pre-R1 sources: `Term::clone` was **already** O(1) (each App /
Lam variant stored `Arc<Term>`, so derived `Clone` emitted only
`Arc::clone`s).  The expensive op was `HashSet::insert`'s
**derived structural `Hash` / `Eq`** walking the whole subtree
— *that* is what's O(N) per node and O(N²) cumulative.  The
deadline cascade
(`check_sat_with_deadline` → `cdcl_with_restarts_deadline` →
`cdcl_solve_with_model_deadline` 256-iter probe →
`flatten_to_clauses_with_deadline`) can't fire because the busy
loop sits inside hashbrown's per-node hash computation.

**Primary ask (§2, "R" refactor) — DONE:**

| phase | commit | scope | gate |
|---|---|---|---|
| R1 | `855c01a` | `adsmt-core::term` shape: `Term(Arc<TermInner>)` + new `TermInner` enum (App/Lam children = bare `Term`, not `Arc<Term>`).  PascalCase constructors `Term::Var/Const/App/Lam` retained for back-compat.  `kind()` accessor + `Deref<Target=TermInner>`. | `cargo test -p adsmt-core` 38 ✓ |
| R2 | `231777a` | 19-file cascade: engine + theory + cert + quant + abduce.  ~214 pattern-match sites migrated to `match t.kind() { TermInner::… }`. | 437 ✓ |
| R3 | `322308d` | cli + ffi + lints + parser.  Scope narrower than predicted — only `lu-smt`'s `top_level_bool_polarity` helper still had a pattern site. | workspace 748 ✓ |
| §2.3 hash-cons | `2b765d2` | `scc::HashIndex<TermInner, Weak<TermInner>>` global cache.  `Term::PartialEq` = `Arc::ptr_eq`, `Hash` = pointer hash. | workspace 754 ✓ |

`adsmt-core::Term` is internal to adsmt-core, so external oxiz /
Honey-Be fork sync unaffected.  After §2.3,
`gather_subterms` should drop from O(N²) to O(N) per literal —
this is the actual asymptote fix, not R1-R3 alone.

**Long-horizon ask (§3, "+" meta-compiler 4-layer):**

- **§3.1 AOT prelude bank.** Parse Verus prelude once at
  `vargo` / `verus-cross-validate` build time, hash-cons every
  term, compile axiom CNF/Tseitin form into a static atom bank,
  ship as `prelude-<sha>.luart` mmap'd alongside `lu-smt`.
  Subsequent `(check-sat)` queries see the prelude
  pre-asserted; `collect_universe` runs over already-hash-consed
  storage.
- **§3.2 Meta-tracing JIT, *algebraic-certificate guards.***
  Departure from value-guarded meta-tracing (PyPy etc.): traces
  record a set of **`GF(2)` polynomial relations + equivalence
  relations** observed during the hot path, and the emitted
  machine code is guarded on **survival of those relations** in
  the current query's ideal — not on any single variable's truth
  value.  Concretely a guard can pin things like
  `x + y + z = 0 mod 2`, "atoms `a`, `b` in the same UF-class,"
  or the `(and|or|=>|not)` skeleton matching the recorded shape
  modulo α-renaming.  Guard miss → fall back to the interpreter
  exactly like a value-guard miss.  Contract: *the trace's
  correctness is witnessed by an algebraic certificate, not a
  value fingerprint.*  The relation-check uses the same kernel
  as §3.4.
- **§3.3 Stålmarck pre-saturation at AOT.**  Saturate the
  prelude's propositional skeleton offline → fixed-point
  implication graph baked into the §3.1 artifact.  CDCL stays
  the per-query SAT backend but starts with the saturated graph
  as a head-start clause set; theory conflicts / quantifier
  instantiations still route to DPLL(T).
- **§3.4 `GF(2)` Gröbner-basis theory sibling — decidable, not
  heuristic.**  Encode the SAT problem as polynomials over
  `GF(2)[x₁, …, xₙ]`: every clause becomes a polynomial (e.g.
  `(x ∨ ¬y ∨ z) ↦ (1 − x)·y·(1 − z) = 0`); every variable
  carries `xᵢ² − xᵢ = 0` so only `{0, 1}` survives in the
  algebraic closure.  Compute reduced Gröbner basis
  (Buchberger / F4 / F5 — engineering choice).  Then:
  **`1 ∈ basis ⇔ V(I) = ∅ ⇔ UNSAT, certifiable**; otherwise
  SAT with concrete witnesses.  Equivalence chain is Hilbert's
  Weak Nullstellensatz over `GF(2)` — *no false positives, no
  false negatives, no completeness gap*.  Cost is in the basis
  computation (Buchberger worst-case doubly exponential, F4 / F5
  much better on structured inputs).  Many Verus BV queries
  (mask invariants, overflow guards, witnessed-encoded AEAD
  lemmas) fit small enough ideals that an F4-style basis lands
  inside `:rlimit`, and the constant-1 witness flows into the
  existing `adsmt-cert::Certificate` infrastructure as
  `TheoryWitness`.  Registers via the standard
  `Combination::register` as `adsmt-theory::finite_field`
  sibling — no `Combination` restructuring needed.

**Shared kernel point (§3.2 ↔ §3.4):**  The Gröbner machinery
behind §3.4 also serves §3.2's relation-survival check — re-
checking a recorded polynomial relation against the current
ideal is one normal-form reduction against the cached basis,
which is fast in the common case.  So whichever of the two
layers lands first amortises the engineering for the other.

**Layering invariant (§3.5):** each upper layer is an
optimisation pass that defers to the lower layer when its guard
fails or preconditions miss; *no layer is load-bearing for
correctness*.  The existing CDCL(T) engine (post-R refactor)
remains the spec.

**Cross-side ledger (§6):**

| row | side | event |
|---|---|---|
| 1 | adsmt | ✓ acknowledgement reply filed at `.local-replies-to/verus-fork/2026-06-04-engine-refactor-r1-through-hashcons-status-update.md` (commit `7b26047`); mirrored to `~/verus-fork/.local-replies-from/adsmt/` |
| 2 | adsmt | ✓ R1-R3 + §2.3 commits `855c01a` / `231777a` / `322308d` / `2b765d2`; version tag `1.0.0-rc.10` |
| 3 | verus-fork | **pending** — re-run `-V adsmt` smoke against post-`2b765d2` build per §7; append result row to `.claude-notes/trackers/pr-verus-backend-tracker.md` §5 |

**§2.3 hash-cons crate pick — `scc::HashIndex 3.7.1`.**  Chosen
after comparing dashmap / scc / papaya / flurry / evmap / moka /
parking_lot::RwLock<HashMap> / contrie.  Decision criteria:
1. **`peek_with`** is fully lock-free for the cache-hit path
   (the hot path in repeated prelude axioms).
2. **`entry_sync`** gives atomic `Occupied` / `Vacant` dispatch
   for the upgrade-or-replace-dead-weak / `insert_entry`
   branches — removes the race-loop the insert-then-update
   pattern would have needed.
3. Mature (production track since 2.x), Apache-2.0, active.
4. No epoch-pin guard parameter leaking into kernel surface
   (rules out flurry).
5. Weak-GC semantics compatible (rules out moka's
   eviction-policy enforcement).

Workspace dep: `scc = "3"` (workspace.dependencies) →
`adsmt-core/Cargo.toml: scc.workspace = true`.  Pulls
`sdd` (epoch reclamation) + `saa` transitively.

**Reproducer for verus-fork retry (§7):**

```sh
cd ~/AD1
git rev-parse HEAD              # 2b765d2 or later
cargo build --release -p adsmt-cli
# Then the original transcript-replay loop:
verus --log smt-transcript --log-dir /tmp/verus-log-adsmt /tmp/verus_smoke.rs
sed 's/:rlimit 30000000/:rlimit 1000000/' /tmp/verus-log-adsmt/root.smt_transcript > /tmp/test-1s-budget.smt2
time timeout 10 /home/ybi/AD1/target/release/lu-smt < /tmp/test-1s-budget.smt2
```

Expected post-`2b765d2`: `unknown` / `abductive` verdict
within 1 s, not SIGKILL after 10 s.  If still SIGKILL → signal
we missed a hotspot beyond `gather_subterms` and need next
diagnostic.

**§3 meta-compiler proposal — acknowledged, uncommitted.**
Per the 2026-06-04 reply: layering is compatible with
`adsmt-theory::Combination` (§3.4 finite_field sibling
registers via the existing `Combination::register`, no
restructuring).  Hash-cons (§2.3, just landed) is the
kernel-side prerequisite for §3.2 JIT guard machinery —
pointer identity makes guards like "this App head is `+`" or
"atoms a, b in same UF-class" constant-time on `Arc::ptr_eq`.
**§3.1 AOT prelude bank** is the highest-leverage follow-up
(canonical-structure half already exists post hash-cons; the
missing piece is the `prelude-<sha>.luart` mmap surface).
**Nothing in §3 gates v1.0.0 stable** per our reply.

## rc.11 → rc.15 cycle (2026-06-04 → 2026-06-05) — what landed

| RC | what | commit(s) |
|---|---|---|
| rc.11 | bump + memory sync | `d146a82` + `545a547` |
| rc.12 | (get-info :reason-unknown) Z3-canonical mapping + T0 deadline cascade inside `propagate_two_watched` inner loop | `05a3214` (parser+dispatcher), `a3aa4e4` (bump), `c5964db` (T0) |
| rc.13 | §3.4 Buchberger v0 (dense Gröbner-basis decider in `adsmt-theory-finite-field`) | `bde2f8c` → `98159c1` + `db05c14` (bump) |
| rc.14 | §3.4 F4 v1 (bit-packed Gröbner) + `FiniteFieldTheory` plugin via `Combination::register` + `Solver::with_finite_field` builder + budget-exhaustion `force_check` hook + §3.1 AOT prelude bank counter-proposal filed | `3ecf7eb` → `cada5a3`, `5ca3de7`, `8ba77e1`, `af04b6e` (bump) |
| rc.15 | T1.1/T1.2 §3.4 CLI surface + §3.1.A→§3.1.D end-to-end + §3.2 + §3.3 skeletons + docs + §3.5 ack | see breakdown below |

### rc.15 commit breakdown

| sub-cycle | commit | scope |
|---|---|---|
| T1.1 | `e0e3f77` | `--finite-field-periodic <N>` + `--finite-field-budget-exhaustion` CLI flags |
| T1.2 | `50931f2` | `(set-option :finite-field-…)` mid-session SMT-LIB handler with auto-register on first call |
| §3.1.A | `a547a5b` + `0eebf57` | `adsmt-aot` scaffold + `.luart` v0 writer (header + topo-sorted Term pool + assertion list with per-axiom `qid: Option<String>`) |
| §3.1.B | `699bd5b` | `lu-smt --aot-bake / --aot-output / --aot-sha` CLI |
| §3.1.C | `941163d` | `.luart` v0 reader + Term-DAG reconstruction (hash-cons re-intern) + minimal `Type::Display` inverse parser |
| §3.1.D | `38fd8ee` | `Solver::with_aot_prelude(ReconstructedPrelude)` builder + `intern_external(&Term) -> Term` adsmt-aot helper + `lu-smt --aot-load` CLI (mutually exclusive with `--aot-bake`); driver mirrors prelude into `assertions` ledger so `(get-unsat-core)` / `--audit-json` see prelude axioms |
| §3.2 | `d11aafb` | `adsmt-jit` crate skeleton: `JitGuard` (PolyInvariant via shared GF(2) `reduce` / EquivClass / SkeletonShape depth-3) + `JitCache::lookup` + `Trace { key, guards, kernel_id }`. Recorder + dynasm-rs compiled-kernel emit deferred to follow-up |
| §3.3 | `52efc77` | `adsmt-stalmarck` crate skeleton: `Lit` + `ImplicationGraph` (BTreeMap adjacency for deterministic iteration) + `Saturator::saturate_simple` transitive closure + `detect_contradiction` BFS witness. n-saturation dilemma rule deferred |
| rc.15 bump | `c53ec60` | workspace + 7 path-dep manifests + Cargo.lock |
| docs | `2b4d2da`, `34dba51` | README + PORTFOLIO + 4-lang CLI cheatsheet + doc-link fixes |

### rc.15 5-mode smoke matrix retry (verus-fork side, 2026-06-04)

verus-fork ran a 5-mode matrix on the rc.15 build against
`verus_smoke.rs` (`verus! { fn main() {} }`):

| mode | `--finite-field-budget-exhaustion` | `--finite-field-periodic` | `--aot-load` | rlimit 1 s | rlimit 5 s | rlimit 7 s |
|---|---|---|---|---|---|---|
| **A** baseline           | ✗ | 0 | ✗ | 5 221 ms / unknown | 5 352 ms / unknown | 60 002 ms / timeout |
| **B** F4 budget hook     | ✓ | 0 | ✗ | 5 249 ms / unknown | 5 451 ms / unknown | 60 002 ms / timeout |
| **C** AOT-loaded prelude | ✗ | 0 | ✓ | 5 807 ms / unknown | 5 950 ms / unknown | 60 002 ms / timeout |
| **D** AOT + F4 hook      | ✓ | 0 | ✓ | 5 854 ms / unknown | 5 937 ms / unknown | 60 002 ms / timeout |
| **E** F4 periodic 16     | ✗ | 16 | ✗ | 5 208 ms / unknown | 5 407 ms / unknown | 60 002 ms / timeout |

**Diagnostic — load-bearing**: Mode C (`--aot-load`,
5-line per-query trailer) lands on the *same* `~5.3-5.9 s` floor
as Mode A's full 1071-line transcript replay.  This is the
**strongest possible signal** that the floor lives *inside
`(check-sat)` itself* — not in parser / declare / assert /
CNF-flatten / theory-init.  Bake itself is cheap (19 ms for the
verus_smoke prelude).

§3.1 AOT bank works as designed but does not lift the floor;
§3.4 F4 plugin via CLI works as designed but the deadline cascade
catches before the budget-exhaustion hook gets to run.  The
remaining hot path is *inside CDCL between deadline checks*:
T0 (rc.12) added a check inside `propagate_two_watched` but the
work *between* two consecutive calls (conflict analysis,
clause-learning insertion, VSIDS bumps, restart housekeeping,
post-backjump unit-prop) runs unmodulated on prelude-sized clause
sets.

### §3.5 JIT-on-AOT-prelude request (2026-06-04, status: adsmt-side ack mirrored)

Request file:
`.local-requests-from/verus-fork/2026-06-04-3.5-jit-on-aot-prelude.md`.

Reply filed: `.local-replies-to/verus-fork/2026-06-04-3.5-jit-on-aot-prelude-ack.md`
(commit `b484369`), mirrored via `just mirror-local-replies-to
verus-fork ~/verus-fork/.local-replies-from/adsmt/`.

§3.5 = **combination sub-cycle** between §3.1 v0 (Term-DAG bake)
and §3.2 skeleton's eventual fully-traced CDCL.  Three layers:

1. **`.luart-cdcl` v1 format** — extends v0 `.luart` with a CDCL
   section: `flatten_version` + post-flatten clause vec + initial
   BCP trail + two-watched index + VSIDS activity + phase-save
   polarities.  Atom references stay v0 pool indices.  v0 readers
   ignore trailing v1 bytes (additive shape).
2. **`adsmt-jit::CdclTracer`** — hooks `propagate_two_watched` /
   `analyze_conflict_1uip` / `cdcl_solve_with_model`'s decision
   branch.  Records event stream `Propagate / Conflict / Backjump
   / Decide / Restart` (Restart load-bearing — Luby-restart
   without it breaks soundness).
3. **Trace replay at `(check-sat)`** — validates the trace's GF(2)
   algebraic signature against the per-query basis delta; if all
   relations + equivalence classes survive, replay events
   wholesale, else fall back to full CDCL.

### §3.5 ack key decisions (our reply)

- **`.luart-cdcl` header**: recommend adding `lu_smt_binary_sha256:
  [u8; 32]` next to `flatten_version` — catches Rust-toolchain /
  compile-flag drift the source-level knob misses.  Computed via
  `current_exe()` + SHA-256, cached in `OnceCell`.
- **`watch_count`**: u64 (matches v0 `pool_len` / `assert_len`),
  inner `watching_clauses: Vec<u32>` element type.  Optional
  future-proofing gate: `0x00`/`0x01` element-type discriminator
  byte for v2 expansion.
- **Trace event vocabulary**: `Propagate / Conflict / Backjump /
  Decide / Restart` = 5 events.  Restart added (Luby soundness).
  `Learn` implicit in `Conflict { learnt }`; `Forget` =
  cache-management, not soundness, so v0 ships without.
- **GF(2) signature timing**: hybrid — end-of-trace **mandatory**
  + checkpoint at **phase transitions** (Restart, high-LBD
  Conflict, scope-0 Backjump).  v0 ships end-only; checkpoints
  unlock partial-replay fallback in v1.E.  Snapshots reuse
  `FiniteFieldTheory::force_check`'s existing basis output, no
  new GF(2) cost.
- **Vocabulary reuse**: share *guard* surface (`JitGuard` /
  `GuardResult` / `check_guard` / `JitCache`); split *event*
  surface — new `adsmt-jit::cdcl` submodule with
  `CdclTraceEvent` / `CdclTrace` / `CdclCheckpoint` /
  `GF2Snapshot`.  Bytecode-trace and CDCL-trace have different
  replay semantics.
- **§3.5.A**: lives in `adsmt-aot` next to existing v0 sections
  (no new crate — cache-key / SHA computation stays in one place).
- **§3.5.B**: `--aot-bake --aot-include-cdcl` composable flag
  rather than a new `--aot-bake-with-cdcl` mode.
- **T0' counter-ask**: adsmt-side will land T0'.1 (deadline check
  inside `analyze_conflict_1uip`) + T0'.2 (inside learnt-clause
  insertion + activity bookkeeping) + T0'.3 (inside post-backjump
  unit-prop) **in parallel** with §3.5.A — independent value,
  shrinks the silent-CDCL-give-up window even without JIT replay.

### Updated §6 ledger (rc.15 cycle)

| date | side | event |
|---|---|---|
| 2026-06-04 | adsmt | T1.1 (`e0e3f77`) + T1.2 (`50931f2`) §3.4 CLI surface |
| 2026-06-04 | adsmt | §3.1.A→§3.1.D end-to-end (`a547a5b` + `0eebf57` + `699bd5b` + `941163d` + `38fd8ee`) — bake/load round-trip works, smoke confirmed (prelude UNSAT and SAT cases) |
| 2026-06-04 | adsmt | §3.2 skeleton (`d11aafb`) + §3.3 skeleton (`52efc77`) |
| 2026-06-04 | adsmt | workspace bump to testing `1.0.0-rc.15` (`c53ec60`) + docs refresh (`2b4d2da`, `34dba51`) |
| 2026-06-04 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.14 → rc.15 + 5-mode smoke matrix retry — all 5 modes hit the same `~5.3 s` floor; Mode C invariance localises floor inside `(check-sat)` |
| 2026-06-04 | verus-fork | §3.5 JIT-on-AOT-prelude design filed at `.local-requests-to/adsmt/2026-06-04-3.5-jit-on-aot-prelude.md` |
| 2026-06-04 | adsmt | §3.5 ack at `.local-replies-to/verus-fork/2026-06-04-3.5-jit-on-aot-prelude-ack.md` (commit `b484369`); recommends binary-SHA in `.luart-cdcl` header, Restart added to event vocab, hybrid signature timing, vocabulary reuse split |
| 2026-06-05 | verus-fork | §3.5 counter-ack at `.local-replies-to/adsmt/2026-06-04-3.5-jit-on-aot-prelude-counter-ack.md` — accept all six adsmt recommendations; decline the optional `0x00/0x01` watch-width gate byte (format-version bump preferred over permanent v0/v1 compat surface during testing channel); add §3.5.J.pre row (verus-fork 5-mode retry after T0'.1–.3, ahead of §3.5.J full retry); T0' parallel progression confirmed.  Design phase closes; §3.5.A + T0'.1 unblocked on adsmt side. |

## rc.16 cycle (2026-06-05) — what landed

| sub-cycle | commit | scope |
|---|---|---|
| T0'.1 | `627aded` | deadline check inside `analyze_conflict_1uip_deadline` (new variant; original keeps its public signature).  256-iter cadence inside the trail-walking resolution loop.  `DEADLINE_CHECK_INTERVAL = 256` + `expired(deadline)` helper promoted to module-level constants so every `*_deadline` function in `adsmt-engine/src/cdcl.rs` shares the cadence. |
| T0'.2 + T0'.3 | `03649f3` | T0'.2 = deadline check inside the learnt-clause reduction loop (`for (i, idx) in to_drop.into_iter().enumerate()`, every 256-th iteration) + unconditional check after the loop exits.  T0'.3 = unconditional `if expired(deadline)` right before the `continue` of the conflict-handling branch, so the next outer `propagate_two_watched` call doesn't run unmodulated after a backjump. |
| §3.5.A | `df18edd` | new `adsmt_aot::cdcl` module with `CdclSection { binary_sha256: [u8; 32], flatten_version: u32, clauses, trail, watches, vsids, saved_phase }` + sub-record types (`CdclClause`, `TrailEntry` carrying `reason_clause_idx: i64` with `-1` sentinel, `WatchEntry`, `VsidsEntry`, `SavedPhaseEntry`).  `write_cdcl_section` + `read_luart_with_cdcl(buf) -> (LuartFile, Option<CdclSection>)` — v0 readers silently ignore trailing v1 bytes.  v1 `watch_count: u64` + inner `watching_clauses: Vec<u32>` fixed-width per counter-ack §(b). |
| §3.5.B | `00ce626` | `lu-smt --aot-bake --aot-include-cdcl` composable flag.  Mutex rules: `--aot-include-cdcl` without `--aot-bake` → exit 12; `--aot-include-cdcl + --aot-load` → exit 12.  `current_binary_sha256()` helper: SHA-256 of `current_exe()` via `sha2` crate.  `FLATTEN_VERSION: u32 = 0` constant — bumped on next breaking change to `flatten_to_clauses`.  v0 emits `CdclSection::empty(binary_sha, FLATTEN_VERSION)` (real CDCL state capture is the §3.5.F follow-up that exposes `Solver::dump_cdcl_state`). |
| §3.5.C | `f91bea5` | `Solver::with_aot_cdcl(prelude: adsmt_aot::ReconstructedCdclPrelude)` builder.  New `ReconstructedCdclPrelude { prelude: ReconstructedPrelude, cdcl_section: Option<CdclSection> }` + `reconstruct_with_cdcl(&[u8])` adsmt-aot helper.  v0 semantics: assertions thread through `with_aot_prelude` as before; `cdcl_section` is stashed (`let _cdcl_section_for_3_5_f = ...`) until §3.5.F lands `restore_cdcl_state(...)`.  CLI `load_aot_prelude` switched to `reconstruct_with_cdcl`; `Driver::new` takes `Option<ReconstructedCdclPrelude>` and routes through `with_aot_cdcl`. |
| §3.5.D | `95efa45` | new `adsmt_jit::cdcl` submodule.  `CdclTraceEvent` = 5-event vocabulary: `Propagate { atom, polarity, antecedent: i64 (-1 = prelude-only) }` / `Conflict { learnt: Vec<(u32, bool)>, lbd: u32 }` / `Backjump { to_scope: u32 }` / `Decide { atom, polarity }` / `Restart`.  `GF2Snapshot { basis: Vec<Polynomial>, classes: Vec<(String, u32)> }` + `CdclCheckpoint { at_event, signature }` + `CdclTrace { events, signature, checkpoints, guards: Vec<JitGuard>, kernel_id }` — shares the guard surface with §3.2's bytecode `Trace` per counter-ack §5.5 vocabulary reuse.  `CdclTracer { events }` recorder (append-only, `record(event)` + `finalize(sig, guards)`). |
| §3.5.E | `5fac19d` | `FiniteFieldTheory::current_generators() -> Vec<Polynomial>` — re-runs `sat_encoder::cnf_to_generators` on the installed `clauses + n_vars`.  `GF2Snapshot::empty()` + `GF2Snapshot::capture(theory, classes)` helpers.  Capture is one cheap CNF-to-polynomial pass, not a fresh Gröbner computation (per counter-ack §5.4 free-at-the-kernel-layer guarantee). |
| §3.5.F | `77ea879` | `Solver::replay_aot_cdcl_trace(&CdclTrace, classes: &[(String, u32)]) -> ReplayOutcome` + new `ReplayOutcome { GuardMiss, GuardsPassed }` enum.  v0 skeleton: evaluates `trace.guards` via `adsmt_jit::check_guard` against `trace.signature.basis` + the engine-supplied class view.  `GuardMiss` on first failure (full-discard v0 per counter-ack §5.4).  Actual event replay is deferred to follow-up that wires `restore_cdcl_state(...)` into `check_sat_with_deadline`.  adsmt-engine grows an `adsmt-jit` dep so the recorder and the dispatcher share one vocabulary. |
| §3.5.G | `7706327` | new `adsmt_jit::cdcl_io` module with `LUTRACE_MAGIC = "lutrace\0"` + `LUTRACE_VERSION = 0` + `write_trace` / `read_trace` byte-level codec.  v0 wire shape covers events + `kernel_id` only; `signature` / `guards` / `checkpoints` reconstructed as empty on read.  `lu-smt --jit-trace-emit <PATH>` (writes empty `.lutrace` v0 = 24-byte header-only payload) + `--jit-trace-load <PATH>` (decode + 12/15 error-code mapping).  Mutex rule: `--jit-trace-emit + --jit-trace-load` → exit 12. |
| rc.16 bump | `ae12a9f` | workspace + 8 path-dep manifests + Cargo.lock |
| books cheatsheet | `4de2727` | 4-lang `§3.5 JIT-on-AOT-prelude` section added (en/ko/ja/de) |
| docs | `44ef399` | README + PORTFOLIO + submodule pointer refresh |

### v0 → v1 follow-up items (deferred per counter-ack)

- **§3.5.C**: `restore_cdcl_state(...)` engine-side method (consumed by `with_aot_cdcl` to set up the CDCL trail / watches / VSIDS from `cdcl_section`).  v0 currently stashes the section away unused.
- **§3.5.D**: engine-side recorder hooks (calls to `tracer.record(CdclTraceEvent::*)` inside `propagate_two_watched` / `analyze_conflict_1uip` / `cdcl_solve_with_model`'s decision branch).  v0 ships the data structures only.
- **§3.5.E**: mid-trace checkpoint capture at phase transitions (Restart, high-LBD Conflict, scope-0 Backjump).  v0 ships end-of-trace only.
- **§3.5.F**: actual event replay through the CDCL state machine.  v0 ships the guard-evaluation gate only.
- **§3.5.G**: extended wire format that persists `signature` / `guards` / `checkpoints` — needs a GF2Poly wire shape (queued for v1).

### Updated §6 ledger (rc.16 cycle)

| date | side | event |
|---|---|---|
| 2026-06-05 | adsmt | T0'.1 (`627aded`) deadline check inside `analyze_conflict_1uip_deadline` |
| 2026-06-05 | adsmt | T0'.2 + T0'.3 (`03649f3`) deadline checks around learnt-clause reduction + post-backjump unit-prop |
| 2026-06-05 | adsmt | §3.5.A (`df18edd`) `.luart-cdcl` v1 section writer + reader |
| 2026-06-05 | adsmt | §3.5.B (`00ce626`) `--aot-bake --aot-include-cdcl` composable flag + `current_binary_sha256` |
| 2026-06-05 | adsmt | §3.5.C (`f91bea5`) `Solver::with_aot_cdcl` + `ReconstructedCdclPrelude` |
| 2026-06-05 | adsmt | §3.5.D (`95efa45`) `adsmt-jit::cdcl` submodule (5-event vocabulary + CdclTrace + CdclTracer + GF2Snapshot + CdclCheckpoint) |
| 2026-06-05 | adsmt | §3.5.E (`5fac19d`) `GF2Snapshot::capture` + `FiniteFieldTheory::current_generators` |
| 2026-06-05 | adsmt | §3.5.F (`77ea879`) `Solver::replay_aot_cdcl_trace` guard-evaluation gate (v0 skeleton) + `ReplayOutcome` enum |
| 2026-06-05 | adsmt | §3.5.G (`7706327`) `lu-smt --jit-trace-emit / --jit-trace-load` + v0 `.lutrace` binary format |
| 2026-06-05 | adsmt | workspace bump to testing `1.0.0-rc.16` (`ae12a9f`) + books cheatsheet (`4de2727`) + docs refresh (`44ef399`) |
| (pending) | verus-fork | `EXPECTED_ADSMT_VERSION` rc.15 → rc.16 + §3.5.J.pre 5-mode smoke matrix retry against T0'.1–.3 (verus-fork side; gated on rc.16 publish) |
| **DONE** | verus-fork | §3.5.H — landed as frontend-agnostic `scripts/aot-bake-prelude.sh` + `just aot-bake-prelude` (verus-fork `5533adfe`), NOT a vargo-internal hook (adsmt stays the common engine); bakes `--from-verus`/`--from-smt2`, caches under `$VERUS_ADSMT_AOT_CACHE_DIR`, emits §3.5.I activation; bake→activate→verus = `1 verified, 0 errors` 292ms |
| **DONE** | verus-fork | §3.5.I — `SmtProcess::solver_argv` threads `--aot-load` from `VERUS_ADSMT_AOT_LUART` (2026-06-05); proven sound end-to-end at the rc.28 retry (driver → `1 verified, 0 errors` 530ms) |
| **DONE** | verus-fork | §3.5.J — FUNCTIONAL SUCCESS at the rc.27 retry: `verus -V adsmt` → `1 verified, 0 errors` 511ms (baseline verus_smoke `unsat` 8ms), three orders inside the ≤1500ms window — the P-vb finish line |
| (pending) | adsmt | §3.5.F engine-side event replay — wire `restore_cdcl_state(...)` into `check_sat_with_deadline` so guard-passed traces actually fire instead of just gating fallback. |
