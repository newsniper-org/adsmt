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
7. **Explicit selection via a TOML manifest.** No CAS backend runs unless the
   user names it in a project-local `adsmt-cas.toml`. The manifest is the
   select-and-call control (the user's "취사선택하여 호출" requirement, §4.3):
   it pins which backends, their binaries/paths, the per-backend class
   allow-list, timeouts, and versions. No manifest ⇒ no CAS (default-off,
   matching the `cas` feature). This makes a CAS-assisted run **reproducible**
   (a verus CI is deterministic only if the oracle set is pinned).

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
   open ⇒ Unknown. (Note: a bounded-domain variant `∃ x̄∈[lo,hi]. P=0` *is*
   decidable and could even be a native job — the class records the bound so the
   classifier can route a bounded instance to the native engine and only an
   *unbounded* one to the search/CAS.)

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

## 3. Capability table (Singular now, PARI co-designed)

`witnessed_dir` = the verdict direction the witness proves; the other direction
downgrades.

| Class | Backend | Witnessed dir | Witness | Trusted re-check (crate) | Other dir |
|---|---|---|---|---|---|
| Ideal membership `f∈⟨gᵢ⟩` | Singular `lift` | **unsat** (of `f∉I`) | cofactors `qᵢ` | `f −̇ Σqᵢgᵢ = 0`, degree-bounded poly mul/cmp (`adsmt-theory-finite-field`, `oxiz-math/polynomial`) | `f∉I` → Unknown |
| Polynomial / integer factorization | Singular / PARI | **either** | factor list | multiply back, exact cmp | — |
| Compositeness `n` composite | PARI | **sat** (witness exists) | a factor `d∣n` | one division (free) | primality → cert-gated |
| Primality `n` prime | PARI | **unsat** (of composite) | Pratt / ECPP cert | modexp chain / EC arith — **checker must be built** | else Unknown |
| Rational-fn identity `p/q−r/s=0` | any | **unsat** (of `≠`) | — | cross-multiply + poly cmp | — |
| Existential Diophantine (ch. 1/2) | PARI / search | **sat** | int solution tuple | bignum evaluate | nonexistence → **Unknown** |
| Universal refutation (ch. 3) | Singular + PARI | **sat** (∃ counterexample) | counterexample + sub-certs | replay the sub-certs | positive ∀ → Unknown |
| Ideal non-membership; QE-equivalence; irreducibility(¬); transcendental zero-test; group/tensor | any | — | — | — | **Unknown / advisory** |

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

/// The witness the backend returns; each variant has a trusted re-checker.
pub enum Witness {
    Cofactors(Vec<Poly>),            // f = Σ qᵢ·gᵢ
    Factors(Vec<Poly>),              // ∏ = target
    IntSolution(Vec<BigInt>),        // a Diophantine point
    Counterexample(Term, Box<Witness>), // a ∀-refutation + its sub-cert
    PrimalityCert(PrattOrEcpp),
    Divisor(BigInt),
}

/// The one trait every backend (in-tree or contrib) implements.
pub trait CasBackend: Send {
    fn name(&self) -> &'static str;
    /// Static — lets the dispatcher pick WITHOUT spawning the CAS.
    fn capabilities(&self) -> &[CasCapability];
    /// Run the (already-classified, extracted) obligation. Subprocess for
    /// core backends. Returns a witness or "can't decide".
    fn decide(&self, ob: &CasObligation) -> CasReply; // { Witnessed(dir, Witness) | Undecided | Error }
}

/// The trusted core re-checker — NOT part of the backend. Clean-room; the only
/// thing allowed to MOVE a verdict. Returns the sound disposition.
pub fn admit(ob: &CasObligation, reply: &CasReply) -> Disposition; // Verdict(SatLevel) | Unknown | Advisory
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

### 4.3 The TOML manifest (explicit backend selection — decision 7)

A project-local **`adsmt-cas.toml`** is the user's select-and-call control. The
dispatcher (§4.1) only ever considers a backend that the manifest names AND
enables, and only for the classes the manifest permits. No file ⇒ no CAS.

```toml
# adsmt-cas.toml  — explicit opt-in; absence ⇒ no CAS backend runs at all.
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

- **P0 (pre-1.0, lands the interface):** the `adsmt-cas` crate — types, the
  `CasBackend` trait, the classifier (typed-term → `CasClass`), the `admit()`
  re-checker for the **Cofactor** + **FactorList** + **Divisor** witnesses (the
  primitives already exist in `adsmt-theory-finite-field` + `oxiz-math`). No
  backend yet — but the surface is locked and unit-tested against hand-built
  witnesses (good + adversarial: a *wrong* cofactor must be REJECTED → Unknown).
- **P1 (pre-1.0): Singular backend.** `cas-backend-singular` behind the `cas`
  feature; subprocess via `ADSMT_SINGULAR_PATH`; classes = ideal membership +
  factorization (`→unsat`/either, re-admitted by the P0 re-checkers). Non-
  membership downgrades. z3/Singular-differential gate per
  `[[feedback_z3_differential_for_unsat_trust]]`.
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
- **Bounded by recognizability.** Extraction fires ONLY when the term normalizes
  to a polynomial (in)equation / system over a ring the classifier knows
  (`Int`, `Real`, a declared field, `ℤ[x]`). A transcendental, mixed-theory, or
  unrecognized shape ⇒ NOT extracted ⇒ stays `Unknown`. No guessing.
- **The #325 hazard.** The CIC→HOL lowering ([[cic_hol_lowering]]) drops type
  relations to opaque EUF, so ring/field structure may already be *gone* by the
  time a term reaches the native engine. Two options, decided here:
  (i) classify at the **lukb / pre-lowering** level where the ring sort is still
  typed (preferred — the lu-kb-successor is where Verus emits, [[verus_emits_lukb_surface]]);
  (ii) re-recognize `+`/`*`/`pow` over `Int`/`Real` from the residual shape as a
  fallback. v1 takes (i) for the typed path and (ii) only for raw SMT-LIB input.
- **THE SOUNDNESS BACKSTOP (why an extraction bug can't be unsound).** `admit()`
  re-checks the witness against the **ORIGINAL obligation term**, never against
  the extracted normal form. So a mis-extraction (e.g. recognizing a non-ring
  term as a polynomial, or normalizing wrong) can only ever route a *wrong query
  to the CAS* → the returned witness fails the re-check against the original →
  `Unknown`. It can **never** admit a wrong verdict. Extraction is thus a
  *routing heuristic*, not a trusted step — only `admit()`'s re-check is trusted.
  This is the same firewall as the engine's "delegation only fires on Unknown,
  result re-verified" discipline.

## 7. The CAS-admitted Certificate

A CAS-admitted verdict emits an `adsmt-cert` `Certificate` that is **re-checkable
offline without the CAS installed** — the verus/ITP trust story requires that a
proof obligation discharged via Singular be replayable by a checker that has no
Singular.

- **New witness variant** `adsmt-cert::Witness::Cas { backend, version, class,
  obligation, witness, verdict }` — carries the FULL witness (cofactors / factors
  / divisor / int-solution / counterexample-tree / primality-cert), the original
  obligation term, and the manifest-pinned backend+version (§4.3) for provenance.
- **Contrast with the OxiZ-delegated cert** ([[oxiz_relationship]] Gap A
  `build_delegated_unsat_cert`): OxiZ is trusted *by parity*, so its cert is
  *synthesized* (no witness needed). A CAS is untrusted, so its cert must carry
  the **actual witness** — the cert IS the re-check input.
- **ONE re-checker, two callers.** The clean-room re-check is a single function;
  online `admit()` and the offline `adsmt-cert` checker both call it. They cannot
  diverge, so "the CAS verdict was admitted" and "the cert re-checks" are the
  same proposition by construction ([[feedback_roundtrip_through_real_producer]]:
  the producer and the checker share the real path). A failed offline re-check =
  an invalid cert, identically to a failed online `admit()` = `Unknown`.
- **Replayable + content-addressed.** The cert flattens to the hash-cons pool
  like every other adsmt cert (so it survives the ciborium/wire path, Gap B), and
  re-checking needs only `adsmt-cert` + `adsmt-theory-finite-field` + `oxiz-math`
  — never the CAS. A CAS-admitted `unsat` is as portable as a native one.

## 8. Open items for the next discussion turn
- The `adsmt-cert::Witness::Cas` wire encoding (CBOR/JSON) + whether the
  counterexample-tree (§2.4) needs a recursion-depth bound on the checker.
- Whether the bounded-domain Diophantine variant (§2.4-1) routes to the *native*
  engine rather than a CAS (it is decidable).
- The `adsmt-cas.toml` *file* discovery (project-local vs `$XDG_CONFIG`) and
  whether it shares the `adsmt-emit-pm` lockfile format verbatim. (The *backend
  try-order* is settled: the `cas.enabled` array order, §4.3.)
