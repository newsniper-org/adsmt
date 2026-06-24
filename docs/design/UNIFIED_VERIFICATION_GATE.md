# Unified Verdict-Verification Gate — One Soundness Spine for the Multi-Paradigm Core

*Status: design exploration (brainstorm artifact). Forward-looking; not yet a
committed adsmt feature.*

## 0. The question

We are designing a **strict-superset language** whose two distinguished
subsets are (1:1) SMT-LIB v3 and (1:1) typed Datalog/ASP, solved by a single
conflict-driven core (CDCL/MCSAT trail) carrying several propagators — SMT
theory propagators, an unfounded-set / stable-model propagator, eventually CP
global-constraint propagators — on **one shared trail**. Symbols are declared
`def` (defined, closed-world, rule/inductive semantics) or `open` (constrained
classically). The organic ASP⊕SMT cooperation lives in the *interior* of the
language: sentences that neither subset can express, where defined atoms and
theory atoms co-occur.

A hard, deferred decision is **how tightly to couple** the stable-model
reasoning and the theory reasoning (loose, clingo-style Boolean-abstraction
theory propagator vs. tight, one grounding-free core). We argued this is not a
one-shot architecture bet but a **rung on the explainer ladder** (oxiz-nl2's
"freeze the loop, grow the explainer" pattern), backstopped by an independent
**verification gate** so that coupling-density affects speed/completeness but
never soundness.

That argument rests on one premise, which this document examines in full:

> **Can the answer-set (ASP) verification gate be unified with oxiz-nl2's
> G-SAT / G-UNSAT gates as the *same abstraction* — a cheap, independent,
> per-verdict re-check that downgrades to `Unknown` on failure — so that
> "every paradigm explains itself" extends to ASP (and CP, and HO) *for free*,
> and the whole ladder sits on a single soundness spine?**

**Verdict (summary).** Yes, with a precise and honest structure:

| side | uniformity | cost | status |
|---|---|---|---|
| **model side** (SAT / answer-set-exists / CP-solution / counterexample) | genuinely uniform: *evaluate the witness* | cheap; ASP adds a self-contained stability check (P for normal programs) | **holds, ~free** |
| **no-model side** (UNSAT / no-answer-set) | uniform at the *abstraction* level (verdict + checkable certificate), but the certificate **kind** is paradigm-specific (resolution/DRAT, CAD covering, ASP loop-proof) | per-paradigm checker; some kinds not yet built | **holds in shape, not free** |

The asymmetry is *exactly* the one oxiz-nl2 already lives with (cheap universal
G-SAT vs. CAD-specific G-UNSAT covering). ASP introduces no new *shape*, only a
new certificate kind on the existing spine. Consequently the loose↔tight
coupling decision is genuinely de-risked: **soundness is independent of coupling
correctness**, so the only remaining question is tactical — *when* to tighten.

---

## 1. Background: why the gate is the spine of hybridization

The standard obstacle to combining reasoning engines is that **trusting a second
engine makes the whole only as sound as the weakest engine**. adsmt sidesteps
this with *independent verification gates*: a verdict is trusted only after a
simple, independent checker re-validates it; otherwise it is downgraded to
`Unknown`. Because the checker does not depend on *how* the verdict was produced,
adding engines (or buggy heuristics) cannot create a wrong final answer.

This is why hybridization is *cheap-to-soundness* in adsmt and expensive
elsewhere. The whole multi-paradigm program hinges on whether the gate
abstraction is **paradigm-uniform** — if it is, every paradigm becomes a
free-to-add, self-justifying plugin; if it is not, each paradigm reintroduces
the trust problem at its seam.

---

## 2. The existing gates (the precedent)

oxiz-nl2 ships two gates, formally pre-verified in Verus
(`oxiz-nl2-verification`), and both follow the same shape:

- **G-SAT** (`gates::checked_model_implies_sat`). A claimed `Sat` carries a
  **model** — an *exact* assignment (`BigRational`, or an in-house
  `AlgebraicReal` for irrational witnesses, **never** an `f64`). The checker
  evaluates every atom at the exact witness. Trust iff all hold. This makes
  `FALSE_SAT` *structurally impossible*, independent of which tier produced the
  model (Layer-0, Sturm, CDCAC, CAC, DFS, …).

- **G-UNSAT** (`covering::covering_implies_unsat`). A claimed `Unsat` carries a
  **covering**: a finite set of cells, each tagged with an atom it falsifies
  everywhere on it, together covering the whole space. The checker re-validates
  the two hypotheses (each cell falsifies its tag; the cells cover). The McCallum
  projection that *built* the covering is **never trusted** — a projection bug
  can only fail the cover-check ⇒ `Unknown`, never a false `Unsat`.

The common form is a triple:

```
Gate(P) = ( Witness, check: Witness × Problem → Bool, soundness: check ⇒ verdict )
```

with three required properties of `check`:

1. **Independent** — does not call, or trust, the producing engine.
2. **Cheap & total** — terminates with a definite accept/reject, much cheaper
   than solving.
3. **Sound** — `check` accepts ⇒ the verdict is correct (the *only* thing trusted).

Failure ⇒ downgrade to `Unknown` (always sound). This is the entire firewall.

---

## 3. The abstraction, generalized

We seek a single trait shared by all paradigms:

```rust
/// A verdict that justifies itself. The producer is never trusted; only `check`.
trait SelfJustifying {
    type Witness;                  // model | answer set | covering | proof | core
    /// Independent, cheap, total. `Some(true)` ⇒ verdict provably holds;
    /// `Some(false)`/`None` ⇒ downgrade to Unknown.
    fn check(problem: &Problem, w: &Self::Witness) -> Option<bool>;
}
```

The spine is: **the core may use any engine, any coupling, any heuristic to
*produce* a (verdict, witness); the gate `check` is the sole arbiter of trust.**
"Every paradigm explains itself" = "every paradigm produces a gate-checkable
witness." Hybridization's admission criterion becomes exactly this trait.

The model side and the no-model side behave differently and must be analyzed
separately.

---

## 4. Does ASP fit?

### 4.1 Model side — answer-set existence

Claimed verdict: *a (theory) answer set exists.* Witness: the answer set itself
— the set `M` of true `def`-atoms (relative to a theory interpretation `θ` of
the `open` symbols). The checker must validate, **independently of the search**:

1. **Theory model** (the `open`/SMT part). `θ` is a model of the classical
   theory constraints. *This is exactly G-SAT* — evaluate the theory atoms at the
   exact witness `θ`. Reuse verbatim.
2. **Stability** (the `def`/ASP part). `M` is a *stable model* of the program
   **reduct relative to `θ`**. Concretely (Gelfond–Lifschitz, with theory atoms):
   - Fix the truth of every theory atom from the verified `θ` (a theory atom
     forced true acts as a *fact* in the reduct; forced false deletes its rule).
   - Form the reduct `P^{M,θ}`: drop rules whose negative `def`-body literal is
     true in `M`; delete the remaining negative literals.
   - Compute the **least model** of the resulting definite program (a Horn
     least-fixpoint — polynomial).
   - **Trust iff that least model equals `M`.**

Both sub-checks are independent of the engine, total, and re-validate the verdict
(theory-answer-set semantics, ASPMT/Bartholomew–Lee). So the **model side fits
the abstraction**, and it is *compositional but ordered*: verify `θ` first, then
stability **relative to** `θ`. The order matters because the reduct depends on
`θ` (a theory-forced atom changes which rules survive); the composition is not a
naive conjunction of two independent gates but a **pipeline** `θ ⊳ M`.

**Cost.** For **normal** programs (no disjunction in `def`-heads) the stability
check is a single Horn least-fixpoint = polynomial ⇒ genuinely a *cheap gate*,
on par with G-SAT. For **disjunctive** `def`-heads, stability = "`M` is a model
of the reduct *and minimal* among them"; minimality checking is **co-NP-complete**
⇒ the gate itself may need a (smaller) solve. This is the one place the
"cheap-gate" promise weakens (see §7).

Witness materialization interacts with **lazy grounding**: the gate needs the
relevant ground `def`-atoms materialized to recompute the reduct's least model.
For a *found* answer set this is finite and bounded by the support of `M`; the
gate forces materialization of exactly the atoms in (and one resolution step
around) `M`. So lazy grounding and the model-side gate are compatible — the gate
*pins* the lazily-grounded fragment it needs.

### 4.2 No-model side — no answer set exists

Claimed verdict: *no theory answer set exists.* This is the hard, asymmetric
side — exactly as in SMT, where SAT is "exhibit a model" but UNSAT is "exhibit a
proof." There is no small "evaluate-the-witness" object; the certificate is a
**proof of non-existence in the answer-set proof system**:

- SMT/SAT UNSAT cert = resolution / **DRAT** / LFSC (adsmt already produces these
  via `adsmt-cert`, `adsmt-parser-lfsc-drat`).
- CAD UNSAT cert = the **covering** (G-UNSAT).
- ASP UNSAT cert = a refutation in an ASP proof system — e.g. resolution over the
  **completion + loop formulas** (the standard "no stable model" witness), or an
  unsat-core of the grounded+completed program. clingo can emit proofs/cores, but
  the format is less standardized than DRAT and *we do not have a checker yet*.

The crucial point: the **gate abstraction still holds** — each of these is "a
proof object + an independent checker." Uniformity is at the *abstraction* level
(verdict + checkable certificate + downgrade-on-fail), **not** at the certificate
*format* level. This is precisely oxiz-nl2's existing asymmetry: G-SAT is one
cheap universal checker; G-UNSAT is a CAD-specific certificate kind. ASP adds a
*new certificate kind* (loop-proof) to the *same spine* — it changes the plugin,
not the architecture.

---

## 5. The asymmetry, stated cleanly

```
                 │ model side (∃ solution)          │ no-model side (∄ solution)
─────────────────┼──────────────────────────────────┼──────────────────────────────
witness          │ an assignment / answer set       │ a refutation proof / core
checker          │ EVALUATE (cheap, universal)      │ VERIFY A PROOF (per-paradigm)
SMT              │ model eval (G-SAT)               │ resolution / DRAT / LFSC
CAD/CAC          │ model eval (G-SAT)               │ covering (G-UNSAT)
ASP (normal)     │ eval θ  ⊳  Horn-fixpoint stable  │ completion + loop-formula proof
ASP (disjunctive)│ eval θ  ⊳  co-NP minimality       │ (harder; minimality refutation)
CP               │ propagate-to-fixpoint check      │ LCG clause / no-good resolution
```

- The **model side is the uniform, cheap, free part**: a model is a model; you
  evaluate it. ASP's only addition is a *self-contained* stability recompute,
  composed *after* the theory gate via the theory-relative reduct.
- The **no-model side is uniform only in shape**: every paradigm carries an
  independently-checkable certificate, but the kinds differ and some are
  unbuilt. This is not new debt introduced by ASP; it is the same debt oxiz-nl2
  already pays for CAD.

---

## 6. Why unifying matters (the payoff)

If the abstraction holds (and §4 shows it does, modulo §7), four properties fall
out — and they are the real prize:

1. **Soundness decouples from coupling-correctness.** Since *every* verdict is
   gated, the loose↔tight ASP–SMT coupling, the lazy-grounding interplay, the
   propagator scheduling, and the projection can all be **wrong without producing
   a wrong answer** — at worst `Unknown`. This is the direct answer to the
   deferred decision: it is demoted from "a one-shot soundness-critical
   architecture bet" to "a speed/completeness tuning knob," safely slid along the
   explainer ladder at any time.

2. **Hybridization becomes free-to-add.** Any new engine/paradigm (CP, HO-ATP, a
   local-search SAT-finder, an ML guesser, the legacy nlsat) is admissible **iff
   it can emit a gate-checkable witness/cert.** The gate is the membership test.
   Fast-but-unsound heuristics are welcome as *model-side producers* — gated by
   the evaluator, they can never lie.

3. **One certificate, many consumers.** The gate's witness/cert *is* the artifact
   the three #1 use cases need:
   - **verus** — the UNSAT proof = the trust object;
   - **Verilog utility** — the model = the *counterexample trace* (the input
     sequence a testbench missed);
   - **Sledgehammer** — the UNSAT proof = the Isar-reconstructible object
     (`prover_emit`-Isabelle is the reconstruction half).
   Unifying the gate therefore also unifies the cert-emit pipeline (DRAT / Isar /
   CEX-trace are *emitters* over one certificate spine, mirroring `adsmt-emit`'s
   language-agnostic package model).

4. **Reproducibility for free.** A gate-checked verdict + its witness is a pure,
   replayable artifact — the property the §3.5 AOT/JIT replay already fights for
   (Date/random banned). The gate makes "every verdict is a reproducible,
   re-checkable datum" a *system invariant*, not a per-engine effort.

---

## 7. Where it is *not* free (honest subtleties)

1. **Disjunctive stability is co-NP.** For disjunctive `def`-heads the model-side
   stability check is itself coNP-complete (minimality). Options: (a) restrict
   the cheap-gate guarantee to **normal / stratified** programs (poly), where the
   model side is genuinely as cheap as G-SAT; (b) accept that the disjunctive
   gate is a *bounded auxiliary solve* and budget it; (c) require the producer to
   emit a *minimality witness* (a per-atom support proof) that downgrades the
   check back to evaluation. Recommendation: start at (a), the rung where the
   gate is provably cheap; treat disjunction as a later strengthening.

2. **The reduct is theory-relative ⇒ ordered composition.** The ASP gate is not
   independent of the SMT gate; it is *parameterized* by the verified theory
   model `θ`. The pipeline `θ ⊳ M` must be respected (verify `θ`, fix theory-atom
   truths, then check stability). A naive "AND of two independent gates" is
   **wrong** — it would miss that a theory-forced atom changes the reduct. This is
   a correctness obligation on the gate composition, and a Verus 선검증 target
   (the analog of the cdcac covering lemma): *"`θ` is a theory model ∧ `M` is the
   least model of `P^{M,θ}` ⟹ `M` is a theory answer set."*

3. **No-model certificate for ASP is unbuilt.** A checkable "no stable model"
   proof (completion + loop-formula refutation, or a verified unsat-core) is real
   engineering, not free. Until it exists, ASP `Unsat` verdicts must be **trusted
   only as `Unknown`** unless they reduce to an SMT/SAT UNSAT cert we already
   check. (Note: under the `def`/`open` split, many "no answer set" results
   actually bottom out in a *theory* UNSAT over the completion — those *do* ride
   the existing DRAT/covering gates. The genuinely ASP-specific non-existence
   proofs are the residual.)

4. **Lazy grounding must pin the gate's fragment.** The gate recomputes a least
   model over the *materialized* `def`-atoms; a lazy grounder must guarantee that
   the support of the claimed `M` (and its immediate reduct neighborhood) is
   materialized before the gate runs. This is a contract between the grounder and
   the gate, not a soundness hole, but it must be explicit.

---

## 8. Conclusion — the answer

**Yes — the gate unifies, on one spine, with a uniform cheap model side and a
pluggable (per-paradigm) no-model side.** Precisely:

- The **abstraction** `SelfJustifying { Witness, check }` is paradigm-uniform and
  is *the* single soundness spine. ✓
- The **model side** is uniformly *evaluate-the-witness*; ASP contributes a
  self-contained Horn-fixpoint stability check (poly for normal programs),
  composed *after* G-SAT through the **theory-relative reduct** (ordered pipeline
  `θ ⊳ M`). ✓
- The **no-model side** is uniform *in shape* (verdict + independently-checkable
  certificate + downgrade-on-fail) but per-paradigm *in kind* (DRAT / covering /
  loop-proof). This is the *same asymmetry oxiz-nl2 already has*, not a new one. ◐

Therefore the central consequence holds: **soundness of the whole hybrid is
independent of the ASP–SMT coupling density**, so the deferred "loose vs tight"
decision is de-risked to *"when to tighten"* — a tactical, ladderable choice, not
a soundness bet.

"Every paradigm explains itself" is thus adoptable as a **design law**:

> Any verdict from any paradigm, produced by any engine/coupling/heuristic, is
> trusted **only** through an independent, cheap-where-possible, downgrade-on-fail
> gate over a paradigm-appropriate witness/certificate. The core is free to be
> fast and clever; the gate is the sole keeper of soundness.

---

## 9. Interface sketch

```rust
/// Verdict carried with its self-justification. Producer untrusted.
enum Justified<W> { Sat(W), Unsat(Cert), Unknown }

/// One soundness spine; each paradigm supplies the two checkers it can.
trait Gate {
    type Model;     // assignment | answer set (θ ⊳ M) | CP solution
    type Cert;      // DRAT | covering | loop-proof | LCG no-good

    /// Cheap, independent, total. None ⇒ Unknown.
    fn check_model(p: &Problem, m: &Self::Model) -> Option<bool>;
    /// Independent proof check. None ⇒ Unknown.
    fn check_cert(p: &Problem, c: &Self::Cert) -> Option<bool>;
}

// SMT theory  : check_model = exact eval (G-SAT); check_cert = DRAT/LFSC
// CAD/CAC     : check_model = exact eval (G-SAT); check_cert = covering (G-UNSAT)
// ASP (normal): check_model = eval θ  ⊳  least-model(reduct)==M ; check_cert = loop-proof (TODO)
// CP          : check_model = propagate-to-fixpoint consistent  ; check_cert = no-good resolution
```

The driver is uniform: *produce* `(verdict, witness)` by any means → run the
matching `Gate::check_*` → trust or downgrade. The trail/explainer coupling lives
*below* this line and cannot affect what is trusted *above* it.

---

## 10. Open items / next

- **선검증 target:** the theory-relative reduct soundness lemma (§7.2) in Verus,
  alongside the existing covering/gates/cdcac/nia modules — the answer-set analog
  of `covering_implies_unsat`.
- **Decide the cheap-gate fragment:** commit to normal/stratified `def` for the
  poly model-side guarantee first; schedule disjunctive (co-NP) as a strengthening.
- **ASP no-model certificate:** design a checkable loop-formula/core proof, or
  characterize how far `def`/`open`-completion lets ASP non-existence ride the
  existing DRAT/covering gates.
- **Grounder↔gate contract:** specify the materialization obligation for lazy
  grounding so the model-side gate always has its fragment pinned.
- **Cert-emit unification:** confirm DRAT / Isar (`prover_emit`) / CEX-trace as
  emitters over the single `Cert` spine (the `adsmt-emit` package model applied to
  proofs).
```
