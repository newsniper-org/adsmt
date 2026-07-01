# CAS backend integration — the pluggable oracle interface

Status: **design (pre-v1.0.0)**. Decision-of-record for integrating Computer
Algebra Systems as untrusted, re-checked delegation oracles. Supersedes the
"discuss, don't build, pre-1.0" framing: the user has scoped **Singular as a
pre-1.0 deliverable**, with the *interface* locked first.

## 0. Decisions of record (user, 2026-06-30)

1. **Interface-first.** The pluggable multi-backend CAS interface is the #1
   deliverable — designed and locked *before* any one backend is built, so
   backends are select-and-callable and a contrib backend is a drop-in.
2. **Singular: pre-1.0.** Implemented before the stable cut (the first in-tree
   backend), behind a default-off feature.
3. **PARI/GP: post-1.0, co-designed now.** Its capability rows + witness types
   are fixed in this doc alongside Singular; only the impl waits.
4. **Everyone else** (GAP, Cadabra, Mathics, FriCAS/Axiom, Giac, Maxima,
   Macaulay2, SymEngine, …): **out-of-tree in `adsmt-contrib`** as `cas-backend-*`
   crates implementing this interface — never in the core workspace.
5. **Verdict-path scope:** a CAS answer becomes a *trusted verdict* only for the
   re-checkable classes (cofactor / factor / division); everything else
   downgrades to `Unknown` or surfaces as an advisory abduct. (§3 table.)
6. **License/linkage:** subprocess only — no `libsingular`/`libpari` FFI in
   core. Every high-capability CAS is GPL; subprocess keeps the Apache-2 default
   build GPL-free *and* firewalls the untrusted oracle from trusted memory. One
   boundary serves both concerns. (A BSD library backend — SymEngine, SymPy,
   FriCAS — *may* link in a contrib crate under its own feature; the core rule
   is subprocess.)
7. **Explicit selection via the `adsmt.toml` manifest; its directory IS the
   project root.** No CAS backend runs unless the user names it in the `[cas]`
   section of an **`adsmt.toml`** (the general adsmt project manifest — `[cas]` is
   one section, extended from the earlier `adsmt-cas.toml`). The directory
   containing `adsmt.toml` is the **root of an adsmt-using project**; discovery
   walks up from the input / CWD to the nearest `adsmt.toml`, exactly like Cargo
   finds `Cargo.toml`. The `[cas]` table is the select-and-call control (the
   user's "취사선택하여 호출" requirement, §4.3): it pins which backends, their
   binaries/paths, the per-backend class allow-list, timeouts, and versions. No
   `adsmt.toml` (or no `[cas]`) ⇒ no CAS (default-off, matching the `cas`
   feature). This makes a CAS-assisted run **reproducible** (a verus CI is
   deterministic only if the oracle set is pinned).

## 1. The soundness contract (the load-bearing invariant)

> **No CAS answer flips an adsmt verdict without a witness the trusted core
> re-validates — in time cheaper than, and independent of, the CAS's own
> search.** A CAS is an untrusted oracle; it *finds*, the core *checks*.

The asymmetry is **per obligation, per direction**. The classic SMT asymmetry
(dropping a constraint preserves Unsat, destroys Sat — `[[feedback_soundness_opaque_fallback]]`,
the `#291` div/mod `Sat→Unknown` gate) is the *default*, but it **inverts** for
existential search (§2.2). So the interface does NOT bake in a fixed
"unsat-trusted / sat-downgraded" rule; each `(backend, class)` row declares
**which verdict direction is witness-backed**, and that direction's witness has
a trusted re-checker. The other direction downgrades.

A failed re-check is a CAS bug ⇒ `Unknown`, **never** a verdict. The re-checker
is clean-room Rust in the trusted core (`adsmt-theory-finite-field`,
`oxiz-math/polynomial`, …) and vendors **no** CAS-derived code.

## 2. The challenge problems — why the interface must be direction-aware

The user posed three problems that are exactly the taxonomy stress-test.

### 2.1 Why they matter
They span the three witness shapes the interface must carry, and they show the
witnessed direction is **not** always "unsat".

### 2.2 Existential Diophantine (challenges 1 & 2)
`∃ x,y,z,w∈ℕ. xⁿ+yⁿ+zⁿ=wⁿ` for fixed `n≥5` (and the `k=4`, `n≥6` analogue).
These are *open* (Euler's sum-of-powers conjecture territory; Hilbert's 10th
makes general Diophantine existence undecidable).

- **SAT direction is witness-backed.** A found tuple `(x,y,z,w)` is re-checked
  by the trusted core in one bignum evaluation `xⁿ+yⁿ+zⁿ −̇ wⁿ = 0`. ⇒ **RE-ADMIT
  `sat`.** (A CAS/search that returns a tuple gives adsmt a *sound model*.)
- **UNSAT direction is open.** "No solution exists" has no short certificate ⇒
  **DOWNGRADE → `Unknown`** (never a fabricated `unsat` — that is the
  false-verus-proof direction).

This **inverts** the ideal-membership row (§3), where *membership* (the unsat of
the negation) is the cofactor-witnessed direction. Hence the per-row
`witnessed_dir` field.

### 2.3 Universal refutation (challenge 3, Bunyakovsky-adjacent)
`∀ h∈ℤ[x]. reducible(h) ⟺ finite({prime values of h on ℤ})`.

This biconditional is **false**, and adsmt can *refute* it soundly:
- `⟸` fails. Counterexample `h(x)=x²+x+2`: irreducible over ℤ, yet `x²+x=x(x+1)`
  is always even so `h` is always even and `≥2`, prime only at `h(0)=h(−1)=2` —
  finitely many primes, **not** reducible. The refutation witness is
  `(h, irreducibility-cert, fixed-divisor 2)`; the core re-checks
  `irreducible(h)` (factor-search bound) + `2 | h(x) ∀x` (evaluate `h(0),h(1)`
  mod 2) + `h(x)≥2` ⇒ finitely many primes. ⇒ **RE-ADMIT the `∀`-refutation**.
- The forward Bunyakovsky direction (`irreducible + admissible ⇒ ∞ primes`) is
  *open* ⇒ the *positive* `∀` claim **downgrades**.

So the interface carries a **counterexample** witness for universals, and again
the witnessed direction is the *refutation* (∃ counterexample), not the proof.

**Taxonomy extracted:** witness shapes = `{ Cofactor, FactorList, IntSolution,
Counterexample, PrimalityCert, DivisorWitness }`; each is one verdict
*direction* of one *class*; the opposite direction downgrades unless it too has a
witness.

### 2.4 What the challenges force into the classifier (deepening)

The three problems are not just rows — they fix three structural requirements on
the obligation classifier and the witness type.

1. **First-order existential Diophantine is its own class.** Challenges 1/2 are
   `∃ x̄ ∈ ℕ (or ℤ). P(x̄) = 0` (a single polynomial, or a system). The
   classifier must recognize the quantifier *prefix* and the variable *domain*
   (ℕ vs ℤ — `xⁿ` over ℕ excludes the trivial `0`/sign solutions, so the domain
   is part of the obligation, NOT a detail). `CasClass::DiophantineExists`
   carries `{ system: Vec<Poly>, domain: NatOrInt, vars }`. Witnessed dir =
   **Sat**; witness = `IntSolution(Vec<BigInt>)`; re-check = substitute + bignum
   evaluate the *original* polynomials (degree/`pow` faithfully). Nonexistence is
   open ⇒ Unknown. **A bounded-domain variant `∃ x̄∈[lo,hi]. P=0` is DECIDABLE and
   is routed to the NATIVE engine, NOT a CAS** (decision, §8): the class records
   the bound, and the classifier hands a bounded ∃ to native/`oxiz-nl2`'s integer
   CP propagator (`fdlcg`) for a *definite* sat/unsat; only an **unbounded** ∃
   reaches the CAS.

2. **Higher-order universals over ring elements need a HO refutation class.**
   Challenge 3 quantifies over `h ∈ ℤ[x]` itself — `∀ h. φ(h)`, a HO universal
   over a *polynomial-typed* variable. adsmt is HOL+HKT, so this is in-language,
   but the classifier must recognize *which sort the bound variable ranges over*
   (a ring/polynomial sort vs a base scalar) — that decides whether a CAS can
   even produce a witness. `CasClass::UniversalRefutation` carries
   `{ bound: (Name, RingOrPolySort), body: Term }`; witnessed dir = **Sat** (of
   the negation, i.e. an `∃`-counterexample); witness = a concrete `h` (a
   polynomial value) **plus** the sub-witness that makes `¬φ(h)` true. The
   *positive* `∀` claim is open/undecidable ⇒ Unknown.

3. **The `Counterexample` witness is COMPOSITE — it recurses into sub-classes.**
   For challenge 3 the counterexample `h(x)=x²+x+2` is sound only with the reason
   `¬φ(h)` holds: `irreducible(h)` (a factor-search-bound sub-witness) **and**
   `finite({primes of h})` (a `DivisorWitness`: `2 | h(x) ∀x`, proven by
   `h(0)≡h(1)≡0 mod 2`, plus `h(x)≥2`). So `Witness::Counterexample` carries the
   instantiation `h` and a `Vec<Witness>` of sub-witnesses, and `admit()`
   re-checks it by (a) substituting `h` into the body and (b) discharging each
   sub-witness through the SAME re-checkers as its own class. The witness type is
   therefore a small *tree*, and the re-checker is *recursive* — which is exactly
   why `admit()` lives in the trusted core and not in any backend.

These three are the taxonomy's stress-test, not v1 deliverables — most instances
are open, so they primarily exercise the **downgrade** path. But pinning them now
keeps `CasClass`/`Witness` expressive enough that a future backend (or adsmt's
own bounded search / abduction) can return a *sound* `sat`/refutation where one
exists, re-checked by the core.

## 3. Capability table — SPLIT BY TRUST MODEL (adversarial-review §9 hardening)

The original single table conflated two trust models and shipped five unsound
rows. It is split: **(A) witness-delegated** — a *short* certificate the core
checks independently of the CAS's search; **(B) downgrade-only** — no short
witness exists, so the "re-check" would be the decision procedure re-run (often
with a dropped side condition). `witnessed_dir` = the direction the witness
proves; the other direction is always Unknown. **Every re-check is against the
original `Sequent` (§4/§6), in the obligation's own ring.**

### A. Witness-delegated (trusted ONLY after the core re-check passes)

| Class | Backend | Witnessed dir | Witness | Trusted re-check (against the original) |
|---|---|---|---|---|
| Ideal membership `g₁=0,…⊢ f=0` | Singular `lift` | **unsat** (of `f∉I`) | cofactors `qᵢ` (paired to `gᵢ`, §9-G9) | `f −̇ Σqᵢgᵢ = 0` as an **exact identity in the obligation's coefficient ring**. **char-0 (Int/Real/ℚ/ℤ[x]) ⇒ `oxiz-math` `BigRational` ONLY; `adsmt-theory-finite-field` is GF(2)-only and FORBIDDEN for char ≠ 2 (B1)**; ring mismatch ⇒ Unknown |
| Factorization — **REDUCIBLE only** | Singular / PARI | **sat** (reducible) | ≥2 non-unit factors | `∏ = target` exact in-ring **and** each factor non-unit. The **irreducible** direction has no short cert ⇒ Unknown (NOT `oxiz-math::is_irreducible` — a confirmed stub, B5) |
| Compositeness `n` composite | PARI | **sat** | a divisor `d` | **`n>1 ∧ 1 < d < n ∧ n mod d = 0`** (proper-divisor bound — B6) |
| Existential Diophantine (ch. 1/2) | search / PARI | **sat** | int solution tuple | **`(∀i. xᵢ ∈ domain) ∧ P(x̄)=0`**, exact `BigInt` — domain-membership of EVERY coordinate **and** the equation (B3); nonexistence ⇒ Unknown |
| Universal refutation (ch. 3) | Singular + PARI | **sat** (∃ counterexample) | `h` + `Vec<Witness>` covering EVERY conjunct of `¬φ(h)` | substitute `h` into the **original negated body**, decompose `¬φ(h)` into conjuncts, require a discharged sub-witness for **each** (entailment-coverage — B7); any uncovered/mis-shaped conjunct ⇒ Unknown |
| Primality `n` prime | PARI | **unsat** (of composite) | Pratt / ECPP cert | modexp / EC arith — **checker must be built first**, else Unknown |

### B. Downgrade-only (Unknown / advisory — never a CAS verdict)

| Class | Why no witness |
|---|---|
| Ideal **non**-membership `f∉I` | no short cert (would re-verify the basis is Gröbner) |
| **Irreducibility** (positive) | non-existence of a factor has no short cert; needs a *complete* Mignotte-bounded fail-*closed* search, not the stub |
| Rational-fn identity with a **vanishing denominator** | cross-multiply is sound only under `q≠0 ∧ s≠0`; under adsmt's **total** division (`x/0` fixed, #291) `x/x=1` is FALSE at 0 (B4). Admissible ONLY if the classifier confirms denominators are non-vanishing over the domain (fraction-field / indeterminate sorts); else Unknown |
| QE-equivalence; transcendental zero-test; group/tensor word-problem | open / undecidable |

## 4. The interface (the locked surface)

A new core crate **`adsmt-cas`** (no heavy deps; pure types + trait + the
classifier + the re-check dispatch). Backends live behind features / in
`adsmt-contrib`.

```rust
// adsmt-cas/src/lib.rs  (sketch — the surface to lock)

/// A class of algebraic obligation a backend may decide.
pub enum CasClass {
    IdealMembership, Factorization, Compositeness, Primality,
    RationalIdentity, DiophantineExists, UniversalRefutation, /* … */
}

/// Which verdict direction a witness proves (§1 asymmetry is per-row).
pub enum WitnessedDir { Sat, Unsat, Either }

/// Capability descriptor — what a backend offers, declared up front so the
/// dispatcher can SELECT among backends without calling them (the user's
/// "취사선택하여 호출" requirement). Mirrors the adsmt-emit-pm manifest shape
/// (capability tags + version), but execution is native subprocess, not wasm.
pub struct CasCapability {
    pub class: CasClass,
    pub witnessed: WitnessedDir,
    pub kind: WitnessKind,   // which Witness variant this row returns
}

/// The coefficient ring of an obligation — `admit()` dispatches the re-checker
/// on it (B1: a GF(2) re-checker on a char-0 obligation is unsound).
pub enum Ring { Z, Q, R, ZmodP(BigInt), GF2, /* … */ }   // char recovered from the term

/// The witness the backend returns; each variant has a trusted re-checker.
pub enum Witness {
    Cofactors(Vec<(usize, Poly)>),   // (gᵢ index, qᵢ) pairs — f = Σ qᵢ·gᵢ  (B7-G9)
    Factors(Vec<Poly>),              // ≥2 NON-UNIT factors; ∏ = target (reducible only, B5)
    IntSolution(Vec<BigInt>),        // a Diophantine point (re-check ALSO domain ∈, B3)
    Counterexample(Term, Vec<Witness>), // h + one sub-witness PER conjunct of ¬φ(h) (B7)
    PrimalityCert(PrattOrEcpp),
    Divisor(BigInt),                 // re-check 1 < d < n (B6)
}

/// The one trait every backend (in-tree or contrib) implements.
pub trait CasBackend: Send {
    fn name(&self) -> &'static str;
    /// Static — lets the dispatcher pick WITHOUT spawning the CAS.
    fn capabilities(&self) -> &[CasCapability];
    /// Run the (already-classified, extracted) obligation. Subprocess for
    /// core backends. Returns a witness or "can't decide". The extracted
    /// `CasObligation` is a ROUTING input to the BACKEND only — never to `admit`.
    fn decide(&self, ob: &CasObligation) -> CasReply; // { Witnessed(dir, Witness) | Undecided | Error }
}

/// The trusted core re-checker — NOT part of the backend. Clean-room; the only
/// thing allowed to MOVE a verdict, and the SAME function the offline cert
/// checker calls (§7). It takes the ORIGINAL `Sequent` (hyps + concl), NOT the
/// extracted `CasObligation` (B2): it re-derives ring/relation/quantifier-prefix
/// /domain FROM the term (treating the extraction as untrusted hints), DERIVES
/// the verdict from what the witness establishes (it IGNORES the backend's
/// declared `dir` — G3), and rejects any witness that leaves a non-ground
/// residual after substitution (kills quantifier-alternation / dropped-conjunct).
pub fn admit(goal: &Sequent, witness: &Witness) -> Disposition; // Verdict(SatLevel) | Unknown | Advisory
```

### 4.1 Dispatch / routing (the fallthrough)
Lives in `adsmt-cli` next to the OxiZ delegation, mirroring its gating
(`oxiz_fallback`/`oxiz_inproc`, feature `cas` default-off, `ADSMT_SINGULAR_PATH`
like `ADSMT_OXIZ_PATH`):

```
native check-sat → OxiZ delegation (unchanged)
  → residual Unknown? → classify obligation FROM THE TYPED TERM (preserve ring
      structure; not the flattened SMT-LIB history)
      → select backend(s) whose capabilities() cover (class, needed-dir)
          → backend.decide()  (subprocess)
              → admit():  re-check witness in trusted core
                  → ok    → Verdict (+ emit a real Certificate)
                  → fail  → Unknown            (CAS bug — never a verdict)
                  → no witness for needed dir → downgrade Unknown / Advisory abduct
      → no class match → stays Unknown
```

A direct `Theory`/`TheoryHooks` bus member is **wrong** for v1 (hooks must be
cheap + per-assignment; a fork+IPC+seconds CAS call there is a latency
catastrophe). If solve-time algebra is later *proven* necessary, the honest
shape is a thin shim that accumulates in `assign_hook` and fires the CAS **once**
at `final_check_complete` — not a live propagator. (Note: the `*Like` G2 case is
**no longer** solver-gated — nl2 is on the bus; its residual is internal
`Reduces`-spine wiring — so do **not** lead with the bus shim. The stale
`adsmt-class/src/numberlike.rs` "until oxiz-nl2 on the bus" comment should be
corrected.)

### 4.2 Why not the emitter PM runtime
`adsmt-emit-*` is the *output* side (fed a `Certificate`, emits proof text) and
its wasmi runtime is sandboxed/deterministic/no-FS — a heavyweight native CAS
(GMP/NTL/FLINT) can't run there and a CAS is *input* side anyway. We reuse the
PM's *discipline* (manifest / content-addressing / capability tags / lockfile)
as the **CAS backend registry**, not its execution model.

### 4.3 The `adsmt.toml` manifest (explicit backend selection — decision 7)

The `[cas]` section of the project's **`adsmt.toml`** is the user's
select-and-call control. The **directory containing `adsmt.toml` is the adsmt
project root** — discovery walks up from the input file / CWD to the nearest
`adsmt.toml` (like Cargo's `Cargo.toml`). The dispatcher (§4.1) only ever
considers a backend the `[cas]` section names AND enables, and only for the
classes it permits. No `adsmt.toml` / no `[cas]` ⇒ no CAS.

```toml
# adsmt.toml  (project root marker) — the [cas] section; absence ⇒ no CAS runs.
[cas]
enabled = ["singular"]          # only these backends are eligible

[cas.backends.singular]
kind    = "subprocess"          # core rule; a contrib FFI backend may say "ffi"
path    = "/usr/bin/Singular"   # overrides $ADSMT_SINGULAR_PATH
classes = ["ideal-membership", "factorization"]   # allow-list (subset of capabilities())
timeout-ms = 5000
version = "4.3.2"               # pinned; recorded into every admitted Certificate

[cas.backends.pari]             # present but not enabled ⇒ inert
kind    = "subprocess"
path    = "/usr/bin/gp"
classes = ["compositeness", "factorization"]
enabled = false
```

Rules that make it load-bearing:
- **Opt-in, never inferred.** The manifest is the *only* way a backend turns on
  — the `cas` cargo feature being compiled in is necessary but not sufficient.
- **Class allow-list ⊆ `capabilities()`.** The manifest may *narrow* a backend's
  declared capabilities (e.g. trust Singular for membership but not
  factorization) but never *widen* them — the dispatcher intersects.
- **Reproducibility.** `version` is pinned and **stamped into the Certificate**
  (§7), so a CAS-admitted verdict records exactly which oracle/version produced
  the witness — and the offline re-check (§7) doesn't need the CAS at all, so a
  pinned manifest is for provenance + routing, not for trust.
- **Dispatch order = the `cas.enabled` array order (user-controlled,
  deterministic).** When more than one enabled backend covers an obligation's
  `(class, needed-dir)`, the dispatcher tries them **in the exact order the user
  listed in `cas.enabled`** — first backend whose witness `admit()`-re-checks
  wins; a backend that returns `Undecided`/`Error`/a failed re-check falls
  through to the next. The order is the user's preference, not an internal
  heuristic, so a CAS-assisted run is reproducible from the manifest alone.
- **Reuses the `adsmt-emit-pm` manifest discipline** (the registry, not the
  wasm runtime): the parser/types can be shared with `adsmt-emit-pm/src/manifest.rs`.

## 5. Phasing

- **P0 (pre-1.0, lands the interface) — LANDED:** the `adsmt-cas` crate — types
  (`Obligation`/`Witness`/`Verdict`/`Disposition`/`Ring`/`Domain`), the
  `CasBackend` trait, the exact-`BigRational`/`BigInt` `admit()` re-checker for
  the **Cofactor** + **FactorList** + **Divisor** + **IntSolution** witnesses
  (its own clean-room `poly::MPoly` over ℚ — §9-B1: NOT the GF(2)
  `adsmt-theory-finite-field` crate), and the `dispatch` fallthrough. The surface
  is locked and unit-tested against hand-built witnesses (good + adversarial: a
  *wrong* cofactor / unit factor / improper divisor / out-of-domain solution is
  REJECTED → Unknown — the §9-B1/B3/B5/B6 scenarios).
- **P1 (pre-1.0): Singular backend — LANDED.** `cas-backend-singular`
  (`cas-backends/`); subprocess; classes = ideal membership + factorization
  (`→unsat`/either, re-admitted by the P0 re-checkers). Non-membership downgrades.
  Real Singular 4.4.1 e2e tests (skip-gated). z3/Singular-differential gate per
  `[[feedback_z3_differential_for_unsat_trust]]`.
- **P1.5 (pre-1.0) — the typed-term classifier, LANDED (membership first):** the
  `term` module (feature `term`, optional `adsmt-core` dep so the re-check core
  stays dependency-light). `term_to_mpoly` is the **faithful partial recognizer**
  (§6.2 backstop) — an arith HOL term → its exact `MPoly`, or `None`, never a
  wrong polynomial. `classify_membership(hyps, goal)` lifts a polynomial-equation
  sequent into an `IdealMembership` obligation (sub-ideal-sound generator
  dropping).
- **P1.6 (pre-1.0) — the ∃-Diophantine classifier, LANDED:**
  `classify_diophantine(goal)` recognizes a goal `∃x̄. ⋀ⱼ(…)` and lifts it into a
  `DiophantineExists` obligation over ℤ. It runs on POST-`#325`-lowered terms
  (§6.2 path ii) yet stays trusted because the Nat/WNat refinement is **recovered
  from the explicit relativization guard** the lowering leaves in the body
  (`∃x:Nat.P` → `∃x:Int. (>= x 1) ∧ P`, adsmt-ir-lower `positivity`) — no type
  info is lost. **Strict all-or-nothing (§9-B3):** each `∃`-body conjunct must be a
  polynomial equation (→ a system poly) or a recognized Nat/WNat guard (→ a
  domain); ANY other conjunct — an upper bound (bounded ⇒ native, §8), a
  disequality, a free-variable parameter, a nested quantifier — makes the whole
  classification `None`. This is the soundness crux: unlike membership, dropping
  an `∃`-conjunct WEAKENS the system and would admit a non-solution. Variable
  indices seed in `∃`-prefix order so `system` / `domains` / a witness tuple align.
  `classify_sequent(hyps, goal)` is the unified classifier entry (membership then
  ∃, then ¬prime); `consult(manifest, backends, hyps, goal)` is the end-to-end
  one-call surface (classify → `dispatch` → re-checked `Disposition`).
- **P1.7 — `consult()` end-to-end entry, LANDED.**
- **P1.8 — compositeness classifier, LANDED.** `classify_compositeness(goal)`
  recognizes `¬prime(k)` (ground `k ≥ 2`) → `Compositeness{k}` (§6.1). The
  remaining classes (factorization / universal refutation) stay deferred — see
  §6.1 for why factorization lacks a sound term representation and universal
  refutation is downgrade-only; the `admit()`/backend halves already exist.
- **P1.5 (pre-1.0, optional, zero shipped footprint):** Singular as an
  *independent-algorithm* (Gröbner vs CAD) differential oracle for `oxiz-nl2`
  (`oxiz-nl2/src/differential.rs`), strengthening the live `#356` frontier. No
  runtime trust.
- **P2 (post-1.0): PARI/GP backend** (rows already fixed in §3): compositeness
  (free re-check) + factorization; primality *iff* the Pratt/ECPP checker is
  built; Diophantine-search `sat`-witness.
- **Contrib (any time):** `adsmt-contrib/cas-backend-{gap,giac,fricas,…}`
  implementing `CasBackend` — never in core.
- **Research track:** algebraic abduction (Singular `radical` / ideal-quotient,
  PARI `factor` → hypotheses) on the existing advisory-abduct surface; and the
  challenge-problem obligations (§2) as the taxonomy's north star — most are
  open/undecidable, so they exercise the **downgrade** path by design.

## 6. Obligation extraction — scope and the soundness backstop

The classifier reads the **typed HOL term** (the goal + in-scope hypotheses at
the adsmt-core / lukb level, sorts intact), NOT the flattened SMT-LIB history —
flattening drops the ring structure the CAS needs.

- **What it extracts:** normalize the candidate (in)equation to `Σ cᵢ·monomial`
  over a recognized ring sort, recover the quantifier prefix (`∃`/`∀`/none) and
  each bound variable's sort (scalar `Int`/`Real` vs a ring/polynomial sort), and
  emit a `CasObligation { ring, vars, polys, relation, quantifier, domain }`.

### 6.1 The precise scope (IN / OUT)

**IN scope — extracted, a CAS may be tried** (the verdict is STILL gated on
`admit()` re-checking against the original `Sequent`, §6.2):

- **Ring purity.** The conclusion — and, for ideal membership, the *equational*
  hypotheses — normalize to **pure polynomials over ONE recognized commutative
  ring** (ℤ / ℚ / ℝ / a declared field / ℤ[x]), in indeterminates that are exactly
  the free / Skolem / ring-typed variables, built **only** from `{+, −, *,
  literal-exponent power, ring constants}`, related by `{=, ≠, <, ≤, ∣}`.
- **Per-class shape:**
  - *Ideal membership* `g₁=0,…,gₘ=0 ⊢ f=0` — `hyps` supply the `gᵢ` (**only the
    polynomial-equation hyps**; a non-polynomial hyp is IGNORED — sound because
    `f∈⟨subset⟩ ⟹ f∈⟨all⟩`), `concl` is `f=0`.
  - *Factorization / compositeness / primality* — a single polynomial `p`, or a
    **ground** integer `n`.
  - *Existential Diophantine* `∃x̄∈D. ⋀ⱼ Pⱼ(x̄)=0` — one homogeneous `∃` block over
    Int/Nat vars, `D` per-var (Nat `≥1` / WNat `≥0` / Int none), **literal**
    exponents.
  - *Universal refutation* `∀h:Ring/Poly. φ(h)` — a single `∀` over a
    **ring/polynomial-sorted** bound variable (the HOL reach).

**Classifier status (the `term` module).** Ideal membership (P1.5), existential
Diophantine (P1.6), and compositeness (P1.8) are LANDED. The other two are
deliberately deferred (their `admit()`/backend halves exist, only the
term-recognizer is out):
- *Compositeness* (LANDED, P1.8): `classify_compositeness` recognizes a goal
  `¬prime(k)` for a ground `k ≥ 2` (`prime` is a built-in `Int → Prop` const
  lowered to `App(Const("prime"), k)`; `composite` is not a const) → a
  `Compositeness{k}` obligation whose `Divisor` witness (`1 < d < k`) `admit`s to
  `Sat` = "k composite" = the `¬prime(k)` goal established. ONLY the `¬prime`
  direction — proving `prime(k)` VALID needs a Pratt/ECPP **primality
  certificate** (the `Primality` class, post-1.0; a divisor cannot witness
  primality). Non-ground / `k < 2` ⇒ `None`. Like ∃-Diophantine, the
  obligation-level verdict's mapping to a *goal* verdict for other query
  polarities is the live-consult layer's concern. **Precondition:** the re-check
  proves the *arithmetic* fact "k composite"; mapping it to `¬prime(k)` is valid
  only where `prime` is the RESERVED built-in — the lu-kb/`install_arith` prelude
  (kernel-forbidden to redeclare), i.e. the Verus/lu-kb path. The bare SMT-LIB
  face does NOT reserve `prime`, so the integration (which holds the `Env`) must
  not route a user-declared `prime` here (unlike `+`/`*`, universally reserved).
- *Factorization* lacks a **sound term representation**. `reducible(p)` is not a
  built-in; it would surface as `∃q r. p = q·r ∧ ¬unit(q) ∧ ¬unit(r)`, but
  `¬unit` is not cleanly polynomial-expressible (a unit is `±1` over ℤ, a nonzero
  constant over ℚ[x]) — recognizing it soundly needs ring-aware unit detection the
  classifier does not yet have. Deferred.
- *Universal refutation* (challenge 3, Bunyakovsky-adjacent) is open/undecidable
  → the **downgrade** path by design (§3-B); no trusted classifier is planned.

**OUT of scope — `Unknown`, no CAS runs:**

- Any **uninterpreted-function / non-ring subterm**, mixed sorts (BV / array /
  string), transcendental ops, or a **non-literal exponent** `xⁿ` (`n` a variable
  ⇒ exponential, not polynomial, undecidable).
- **Genuine quantifier alternation** (`∀∃` / `∃∀`): the extractor MUST NOT flatten
  it (that is break B2) — it maps only to the single-block classes above, else
  `Unknown`. A quantifier over a non-ring sort is out.
- The **post-#325 opaque-EUF residual / raw-SMT-LIB** path: heuristic only ⇒
  **advisory / Unknown-only** (§9-G5). Only the **pre-lowering typed** (lukb /
  adsmt-ir) level, where the ring sort survives, yields a *trusted* verdict.

### 6.2 Why a liberal boundary is still sound

- **Bounded by recognizability.** Extraction fires ONLY when the term normalizes
  to a polynomial (in)equation / system over a ring the classifier knows. A
  transcendental, mixed-theory, or unrecognized shape ⇒ NOT extracted ⇒ stays
  `Unknown`. No guessing.
- Scope is a **routing + completeness** decision, NOT a trust one. Over-reach
  (extract a shape it shouldn't, or normalize wrong) can only mis-route → the
  witness fails `admit()`'s re-check against the original `Sequent` → `Unknown`.
  The ONE soundness constraint scope imposes: a **trusted** verdict needs the
  pre-lowering typed term, because `admit()` must recover the true sorts/domain
  to re-check faithfully (§9-B2/G5).
- **The #325 hazard.** The CIC→HOL lowering ([[cic_hol_lowering]]) drops type
  relations to opaque EUF, so ring/field structure may already be *gone* by the
  time a term reaches the native engine. Two options, decided here:
  (i) classify at the **lukb / pre-lowering** level where the ring sort is still
  typed (preferred — the lu-kb-successor is where Verus emits, [[verus_emits_lukb_surface]]);
  (ii) re-recognize `+`/`*`/`pow` over `Int`/`Real` from the residual shape as a
  fallback. **Only path (i) may yield a TRUSTED verdict (§9-G5)** — `admit()`
  needs the pre-#325 typed `Sequent` to faithfully recover ring/domain/quantifier;
  the post-lowering EUF / raw-SMT-LIB residual is itself a re-extraction, so
  path (ii) is **advisory / Unknown-only** (membership-cofactor identities
  survive as advisories, but no `sat`/domain verdict).
- **THE SOUNDNESS BACKSTOP (why an extraction bug can't be unsound) — corrected.**
  `admit()` re-checks the witness against the **original `Sequent` (hyps +
  concl), NOT the extracted `CasObligation`** (§9-B2): it re-derives
  ring/relation/quantifier/domain from the term and rejects any witness leaving a
  non-ground residual after substitution. So a mis-extraction (dropped conjunct,
  flattened `∃∀`, mis-read domain, non-ring term) can only route a *wrong query
  to the CAS* → the witness fails the re-check against the original `Sequent` →
  `Unknown`, **never** a wrong verdict. Extraction is a *routing heuristic*
  (untrusted); only `admit()`'s re-check against the `Sequent` is trusted. This
  is the engine's "delegation fires on Unknown, result re-verified" firewall —
  but the firewall is real ONLY because the re-check input is the `Sequent`, not
  the extraction (the original design handed `admit()` the extraction, which is
  the B2 break the review caught).
- **How the LANDED code realizes the firewall (P1.5/P1.6).** The shipped `admit`
  takes the `Obligation`, not the `Sequent` — yet it is B2-sound, by TWO
  properties the classifier guarantees: **(1) faithful classification** — the
  `term`-module classifiers are all-or-nothing over the soundness-critical
  structure (`term_to_mpoly` never returns a wrong polynomial; `classify_diophantine`
  bails on ANY unrecognized `∃`-conjunct), so the `Obligation` is an EXACT
  reflection of the original goal, never a lossy one; and **(2) single-obligation
  identity** — `dispatch()` hands the SAME `Obligation` to the backend AND to
  `admit`, so the CAS query and the re-check can never diverge (the B2 hazard was
  a lossy CAS query re-checked against a different, fuller original). Under (1)+(2),
  re-checking the witness against the `Obligation` IS re-checking against the
  `Sequent`. The classifier's all-or-nothing discipline is therefore a *trusted*
  property, discharged by the adversarial classifier tests (dropped conjunct →
  partial witness rejected; unrecognized guard/bound/free-var → `None`).

## 7. The CAS-admitted Certificate

A CAS-admitted verdict emits an `adsmt-cert` `Certificate` that is **re-checkable
offline without the CAS installed** — the verus/ITP trust story requires that a
proof obligation discharged via Singular be replayable by a checker that has no
Singular.

- **New witness variant** `adsmt-cert::Witness::Cas { backend, version, class,
  ring, sequent, witness }` — carries the FULL witness (cofactors / factors /
  divisor / int-solution / counterexample-tree / primality-cert), the original
  **`Sequent` (hyps + concl)** — NOT a bare `Term` (§9-G1: ideal membership is
  `g₁=0,…⊢f=0`; the `gᵢ` are the in-scope hypotheses and must come from `hyps`,
  never the untrusted witness), the coefficient `ring` (§9-B1 dispatch), and the
  manifest-pinned backend+version (§4.3). It does **NOT** store a `verdict`
  field: the offline checker **derives** the verdict from the witness via the
  shared re-checker (§9-G3), so a forged `verdict` is impossible. A CAS-source
  verdict may **never** use the `TheoryWitness::Opaque` hatch (§9-G2) — the
  offline checker rejects any CAS-tagged `Opaque` cert (OxiZ-Opaque is sound by
  parity; a CAS is not).
- **Contrast with the OxiZ-delegated cert** ([[oxiz_relationship]] Gap A
  `build_delegated_unsat_cert`): OxiZ is trusted *by parity*, so its cert is
  *synthesized* (no witness needed). A CAS is untrusted, so its cert must carry
  the **actual witness** — the cert IS the re-check input.
- **ONE re-checker, two callers — and they MUST share input type.** The
  clean-room re-check is a single function `admit(goal: &Sequent, &Witness)`;
  online `admit()` and the offline `adsmt-cert` checker both call it **on the
  same `Sequent` from the cert** — NOT online-on-the-extracted-struct,
  offline-on-a-term (the divergence the review caught, §9-B2). They cannot
  diverge ([[feedback_roundtrip_through_real_producer]]). A failed offline
  re-check = an invalid cert, identically to a failed online `admit()` = Unknown.
- **Replayable + content-addressed; depth-bounded fail-closed.** The cert
  flattens to the hash-cons pool (survives the ciborium/wire path, Gap B). The
  counterexample-tree (§2.4-3) is depth-bounded on BOTH deserialization AND
  checking — an attacker-controlled `Vec`/`Box` chain exceeding the bound is
  rejected (Unknown/invalid), never accepted (§9-G6; same class as the ciborium
  recursion limit). Re-checking needs only `adsmt-cert` + `oxiz-math` (char-0)
  / `adsmt-theory-finite-field` (GF(2) only) — never the CAS.

## 8. Settled decisions (was: open items) — user, 2026-07-01

- **Counterexample-tree bound = `MAX_WITNESS_DEPTH = 8` AND
  `MAX_WITNESS_NODES = 4096`, checked at DESERIALIZATION, fail-closed.** A
  witness tree exceeding either bound is rejected (invalid cert / `Unknown`),
  never accepted. Both are generous — challenge-3 is depth 2 / ~3 nodes — and
  the depth bound is a DoS guard against an attacker-controlled `Vec` chain
  (same class as the ciborium recursion limit). The checker itself is an
  **iterative worklist** (no native recursion), so checking never stack-overflows
  regardless; the bound is purely the deserialization/accept gate.
- **Bounded-domain Diophantine routes to the NATIVE engine, not a CAS.** When
  every existential variable has a finite domain (`∃x̄∈[lo,hi]` or a finite
  sort), the obligation is DECIDABLE by finite search — the native engine +
  `oxiz-nl2`'s integer CP/finite-domain propagator (`fdlcg`, on the bus) decide
  it with a **definite** verdict (sat via a found witness, unsat via exhaustion).
  The classifier therefore does NOT extract a CAS obligation for a bounded ∃; it
  leaves it to the native/OxiZ path. Only an **unbounded** ∃ Diophantine reaches
  the CAS (sat witness-backed, unsat ⇒ Unknown — §2.2/§3-A).
- **`adsmt.toml` file discovery = walk up from the input file / CWD to the
  nearest `adsmt.toml`; that directory is the project root** (decision 7, §4.3).
  The `[cas]` section reuses the `adsmt-emit-pm` manifest-parser types where they
  fit. (Backend try-order was already settled: the `cas.enabled` array order.)

## 9. Adversarial-review hardening (2026-06-30) — GOVERNS ON CONFLICT

A 7-agent adversarial review (each lens trying to BREAK the soundness firewall)
found **7 code-confirmed breaks**: the original design's central claim failed
because (a) `admit()` was handed the *extracted* obligation, not the original
term, and (b) several named re-checkers were unfaithful to the original
semantics. The §3 "re-check" column had conflated **two trust models** —
genuine witness-delegation (a short cert checked independently) vs
decision-procedure-re-run-with-a-dropped-side-condition. §2–§7 above are
corrected; this section is the authoritative changelog and **governs if any
earlier prose still conflicts**.

**P0-gating (block the locked-interface cut — these are TYPE/spec, fixed pre-code):**
1. **B2/G1/G3 — `admit(goal: &Sequent, &Witness)`** takes the original sequent
   (hyps+concl), re-derives ring/relation/quantifier/domain from the term,
   **derives** the verdict from the witness (ignores the backend's declared
   `dir`), rejects non-ground post-substitution residuals. Online + offline share
   this exact function + input.
2. **B1 — ring/characteristic dispatch.** `adsmt-theory-finite-field` is
   **GF(2)-only** (verified: coeffs∈{0,1}, `squarefree` caps exponents at 1,
   `add`=XOR) → **FORBIDDEN for char ≠ 2**. Char-0 cofactor/factor re-check routes
   **only** to `oxiz-math` `BigRational` mul/sub/is_zero; ring mismatch ⇒ Unknown.
3. **B6 — Divisor re-check requires `1 < d < n ∧ n mod d = 0`** (proper-divisor;
   else every prime is "composite"). This is a P0 re-checker.
4. **B5 — FactorList: `witnessed_dir = Sat` (reducible) only** (≥2 non-unit
   factors, ∏=target in-ring); irreducible ⇒ Unknown. **Do NOT wire
   `oxiz-math::is_irreducible`** — verified stub (calls deg-4 reducibles
   irreducible).
5. **B7 — `Counterexample(Term, Vec<Witness>)`** (not `Box`); `admit()`
   substitutes `h` into the original negated body and requires entailment-coverage
   — a discharged sub-witness for **every** conjunct of `¬φ(h)`; uncovered ⇒
   Unknown. (Type locked at P0 though the row is post-1.0.)
6. **G2 — no `Opaque` for CAS provenance.** `adsmt-cert::Witness::Cas` (does not
   exist yet — to be added, carrying the existing `Sequent` type) forces the
   re-checkable path; the offline checker rejects a CAS-tagged `Opaque`.

**Doc-level (gate the rows they govern, folded into §2–§7):** B3 Diophantine
re-check = `(∀i. xᵢ∈domain) ∧ P=0`; B4 rational-identity needs `q≠0∧s≠0`
discharged (total-division #291 hazard) or the classifier refuses vanishing
denominators → Unknown; G4 specify the `sat`/refutation (countermodel) cert +
the polarity invariant (`witnessed_dir=Sat` never emits an `unsat` cert; compose
with `:goal-negation`); G5 only the pre-lowering typed path yields a trusted
verdict, option-(ii) residual = advisory/Unknown; G6 depth-bound the
counterexample tree, fail-closed; G7 the `final_check` bus shim is a *latency*
optimization — it may emit only a re-checked conflict or Unknown, **never `Sat`
on the CAS's word**; G8 gating CI consumes the **offline cert** (no live CAS),
`admit()` evaluates via `BigRational`/`BigInt` (never `Ratio<i128>` — silent wrap
at deg ≥ 5), fail-closed → Unknown on a non-literal exponent; G9 the cert pins
the `qᵢ↔gᵢ` pairing + var-index order (derived from `Sequent.hyps`).

**HELD (firewall genuinely holds — not re-litigated):** cofactor membership as an
exact in-ring identity (self-certifying); non-membership/open-Diophantine-unsat
correctly → Unknown (no witness can smuggle a fabricated unsat); manifest attacks
(allow-list ⊆ `capabilities()` intersect; try-order fallthrough can't starve or
false-accept) — all conditional on the P0 fixes above. **Bottom line: the
firewall concept is sound; it is real only after the 6 P0-gating fixes land — so
they are prerequisites for the `adsmt-cas` crate.**

### 9.1 P1.6 implementation-time adversarial review (2026-07-01)

A second 4-lens adversarial workflow ran against the LANDED `classify_diophantine`
(lenses: domain-widening, conjunct-drop, index-alignment, term_to_mpoly
faithfulness), tasked to construct a concrete spurious-`Sat` goal. Result: three
lenses confirmed the code robust (all-or-nothing `else return None` chain holds;
`term_to_mpoly` returns no wrong polynomial — the two-level App match is an arity
firewall; a mis-sorted Real `+` is sound because an integer witness that roots the
system is also a real one, `ℤ⊂ℝ`). One lens found a **real break**:

- **B8 — shadowed `∃`-binders defeat the free-variable check.** `∃x.∃x. (x≥0) ∧
  (y=1)` with `y` FREE: `peel_exists` returns `["x","x"]` so `n=2`, but the
  name-keyed `VarIndex` seeds only ONE slot (both `x`s → index 0), so `vars.len()`
  starts at 1; the free `y` then lifts it to 2 and the guard `vars.len() > n` reads
  `2 > 2` = false — the free variable escapes, yielding
  `DiophantineExists{[y−1],[WNat,Int]}` that `admit([0,1])` accepts → spurious
  `Sat` for a non-closed goal. **Fix:** `classify_diophantine` refuses a `∃`-prefix
  with duplicate binder names (a name-indexed `MPoly` cannot faithfully separate
  shadowed binders anyway). Zero completeness cost — the lowering assigns FRESH
  `x!k` names, never duplicates. Regression-tested (`shadowed_binders_*`,
  `an_unrecognized_lower_bound_bails_all_or_nothing`,
  `a_partial_application_of_an_arith_op_is_not_a_polynomial`).
