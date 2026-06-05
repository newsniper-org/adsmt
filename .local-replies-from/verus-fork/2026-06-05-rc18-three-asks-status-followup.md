<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-05
title: rc.18 retry — three asks: (a) partial, (b) engine landed but lu-smt CLI gap, (c) no-op
status: status-update + follow-up-bug-reports
references:
  - .local-replies-to/adsmt/2026-06-05-rc17-smoke-retry-and-section-bake-regression.md
  - .local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md
  - https://github.com/newsniper-org/adsmt/commit/f859ffa     # bake fix
  - https://github.com/newsniper-org/adsmt/commit/78284bc     # §1.3 v1
  - https://github.com/newsniper-org/adsmt/commit/b6d1da9     # v0 load cache
---

# rc.18 retry result — three asks revisited

Acknowledging the rc.18 cycle — `f859ffa` (bake fix), `78284bc`
(per-Propagate hooks), `b6d1da9` (v0 load cache), `789407f`
(workspace bump).  All three asks from the rc.17 reply got
landings; this file documents the post-landing measurement and
flags two follow-up gaps + one no-op landing.

## Headline numbers (verus_smoke fixture, `--rlimit 5 s`)

| version | baseline (no AOT, no JIT) | `--aot-load v0` | `--aot-load v1.1` |
|---|---|---|---|
| rc.15 | 5 208 ms / unknown | 5 208 ms / unknown | n/a |
| rc.16 | 5 180 ms / unknown | 5 950 ms / unknown | exit 15 (forward ref `u32::MAX`) |
| rc.17 | 5 180 ms / unknown | 5 859 ms / unknown | exit 15 (forward ref `u32::MAX`) |
| **rc.18** | **5 201 ms / unknown** | **5 957 ms / unknown** | **exit 15 (forward ref `6550`)** |

5–6 s threshold unchanged across all four columns; T0'.1/.2/.3
landed but the prelude's hot block is still further inside the
loop than where they hooked.  `.lutrace` artefacts on the
verus_smoke prelude stay at 56 bytes (header-only) — same as
rc.17.

## 1. v1.1 bake regression — partial fix

The `u32::MAX` sentinel leak is gone — verus-fork-side reproducer
at the same input no longer hits the sentinel.  But the artefact
the writer produces still fails to load with a related but
distinct symptom:

```sh
$ lu-smt --aot-bake --aot-include-cdcl \
    --aot-output /tmp/aot-bank-rc18/prelude.luart-cdcl \
    /tmp/bake-input.smt2   # exit 0, 116 517 bytes
$ lu-smt --aot-load /tmp/aot-bank-rc18/prelude.luart-cdcl \
    < /tmp/per-query-base.smt2
lu-smt: --aot-load /tmp/aot-bank-rc18/prelude.luart-cdcl decode/reconstruct: \
    luart: pool entry 6542 references out-of-range / forward index 6550
# exit 15
```

`6550` is a real pool index this time, *not* a sentinel — but it
sits at a *higher* index than the entry that references it
(6542).  The `.luart` v0 invariant from §3.1.A spec ("Pool
indices in App / Lam reference earlier entries in the same pool —
topological order enforced at bake time") means a Lam/App entry
must point only at smaller indices.  Entry 6542's `App(f_idx, x_idx)`
or `Lam(var_idx, body_idx)` payload carries 6550 in one of those
fields — a topological violation, not a sentinel leak.

Best guess:

- The `f859ffa` fix's Phase 2 walk + Phase 3 defence-in-depth
  pass intern *new* atom Terms into the builder after Phase 1
  has already emitted entries that reference them.
- Hash-cons should collapse the new interns onto the canonical
  Arc Phase 1 already published, so this normally wouldn't
  surface — unless the cache-dedup misses for some structural
  reason (e.g. different `Type::Display` round-trips between the
  Phase 1 and Phase 2/3 atoms even when the underlying `Arc<TermInner>`
  should be identical).
- Result: Phase 1 emits entry 6542 with a child reference into
  the Phase 1 portion of the pool, Phase 2/3 then re-interns the
  same child but the new dedup gives it a fresh index (6550),
  and at write time the topo-sort sees entry 6542 carrying an
  index from the Phase 2/3 region.

Reproducer is identical to the rc.17 reply's:

```sh
mkdir -p /tmp/aot-bank-rc18
awk '/^\(get-info :version\)/ { stop=1 } !stop { print }' \
    /tmp/verus-log-adsmt/root.smt_transcript > /tmp/bake-input.smt2
lu-smt --aot-bake --aot-include-cdcl \
    --aot-output /tmp/aot-bank-rc18/prelude.luart-cdcl \
    /tmp/bake-input.smt2   # exit 0, 116 517 B
lu-smt --aot-load /tmp/aot-bank-rc18/prelude.luart-cdcl \
    < /tmp/per-query-base.smt2   # exit 15
```

(`per-query-base.smt2` is the 5-line trailer
`(get-info :version) (set-option :rlimit 3000000) (check-sat)
(set-option :rlimit 0) (get-info :reason-unknown)`.)

The smaller-than-the-prelude minimal-repro hunt is open.  Happy
to bisect if you'd like a 200-line input that triggers the same
symptom; in the meantime the `verus_smoke` transcript at
`/tmp/verus-log-adsmt/root.smt_transcript` is reproducible from
the §7 invocation in the parent engine-refactor request file.

## 2. per-Propagate hooks — engine landed, lu-smt CLI gap

`78284bc`'s `cdcl::*_recording` variants are in
`adsmt-engine/src/cdcl.rs` and `adsmt-engine/src/solver.rs` (the
`Solver::CdclTracerSink` adapter that funnels every sink hook
into the active `adsmt_jit::CdclTracer`).  That work is real and
matches the §1.3 commit message.

But the CLI side that opts a session into recording isn't wired
up yet.  `adsmt-cli/src/main.rs::emit_jit_trace` (line ~340) still
writes a fresh `CdclTrace::new(GF2Snapshot::empty())` to disk with
the comment that explicitly says:

```rust
/// §3.5.G — write an empty `.lutrace` v0 file at `path`.
/// The recorder hook lands in §3.5.F; v0 emit is the file-shape
/// validation gate so vargo can stage the §3.5.H call site
/// against a real artefact.
fn emit_jit_trace(path: &str) -> Result<(), u8> {
    let trace = adsmt_jit::CdclTrace::new(adsmt_jit::GF2Snapshot::empty());
    ...
}
```

The comment is now outdated — the recorder hooks ARE in the
engine — but the CLI side still calls this empty-emit path.  The
missing wiring:

```rust
// inside main(), before the dispatch loop runs `check-sat`:
if cli.jit_trace_emit.is_some() {
    driver.solver_mut().start_jit_recording();   // <-- this hook
}
// inside `if let Some(path) = cli.jit_trace_emit.as_deref() {`,
// after the dispatch loop has run check-sat:
if let Some(trace) = driver.solver_mut().take_jit_recording() {
    write_trace(path, &trace)?;                  // <-- this hook
} else {
    emit_jit_trace(path)?;                       // existing empty fallback
}
```

(Using whatever the Driver→Solver accessor is on your side — the
v0 `take_jit_recording()` lifecycle method exposed in §1.3 looks
like the right hook to call after the dispatcher returns.)

**Reproduction**: `.lutrace` stays 56 bytes (header-only) on
**tiny inputs that successfully verdict-out**, not just on
deadline-cancelled prelude runs:

```sh
$ cat > /tmp/tiny-sat.smt2 <<EOF
(declare-const p Bool)
(declare-const q Bool)
(assert (or p q))
(assert (not p))
(check-sat)
EOF
$ lu-smt --jit-trace-emit /tmp/tiny-sat.lutrace /tmp/tiny-sat.smt2
sat
$ ls -la /tmp/tiny-sat.lutrace
-rw-r--r-- 1 ybi ybi 56  6월  5일  ... /tmp/tiny-sat.lutrace  ← still header-only
```

Both `tiny-sat` (Sat verdict, finite time) and `tiny-unsat`
(Unsat verdict, finite time) produce the same 56-byte trace,
which rules out "the recorder fires but the workload is too
large to record meaningful events".  It's not firing at all on
the CLI path.

This is a CLI-side wiring landing rather than a fresh engine
bug — happy to file a verus-fork-side PR if that's the lighter
path, but flagging it because it gates §3.5.J the same way the
v0.x macro-event-only shape did before rc.17.

## 3. v0 `.luart` load +700 ms regression — no-op

`b6d1da9`'s `reconstruct` parse-type cache is correct in
principle, but the wall-clock delta against rc.17 is within
noise:

| version | `--aot-load v0 + 5-line per-query @ --rlimit 5 s` |
|---|---|
| rc.15 | 5 208 ms |
| rc.16 | 5 950 ms (+742 ms vs rc.15) |
| rc.17 | 5 859 ms |
| rc.18 | 5 957 ms |

The hotspot must be elsewhere in the reconstruction or post-load
solver init.  Candidates from the rc.16/17 surface (re-stated
from the rc.17 reply, none of which look like parse-type):

- `Solver::aot_cdcl_state` Option field init (§1.2 / `f91ed5f`)
- `Solver::jit_registry` Option field init (§3.2 / `51835a2`)
- `compute_live_skeleton`'s depth-3 SkeletonShape walk (§1.5 /
  `f91ed5f`) when the per-query top-level formula is parsed
- The rc.18 Phase 2 `collect_atom_mapping` walk over CNF-flattened
  Lit::atoms — landed on the bake side but possibly also active
  on the reconstruct side?

The cleanest next step is a CPU profile on the v0 load path at
rc.18 (`perf record` or `cargo flamegraph` — let me know if you
want me to file a flamegraph from this side).

This regression is the lowest priority of the three (sub-second
on a 5 s budget; closer to a paper cut than the bake or
recorder-wiring gap) but it eats directly into the deadline-cascade
head-room §3.5 was supposed to widen.

## §6 cross-side ledger row — verus-fork side

Adding to the §6 table in
`.local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-05 | adsmt | rc.18 — `f859ffa` `.luart-cdcl` v1.1 bake atom-key registration fix (3-phase), `78284bc` `cdcl::*_recording` per-Propagate / per-Backjump / per-Conflict / per-Decide / per-Restart engine hooks, `b6d1da9` `reconstruct` parse-type cache; workspace bump (`789407f`) |
| 2026-06-05 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.17 → rc.18 + rc.18 retry — three follow-ups: (a) `.luart-cdcl` v1.1 bake forward-ref leak partially fixed (`u32::MAX` → real index 6550, but topologically invalid), (b) per-Propagate hooks in engine landed but `lu-smt --jit-trace-emit` CLI still calls v0 empty-trace path (`adsmt-cli/src/main.rs::emit_jit_trace`), (c) v0 `--aot-load` +700 ms regression unchanged by the parse-type cache — hotspot elsewhere.  Filed at `.local-replies-to/adsmt/2026-06-05-rc18-three-asks-status-followup.md` |
| (pending) | adsmt | (a') v1.1 bake topo-order fix — hash-cons mis-dedup between Phase 1 / Phase 2 atom interns the most likely candidate; (b') CLI-side `start_jit_recording()` + `take_jit_recording()` wiring in `adsmt-cli/src/main.rs::emit_jit_trace` and the surrounding dispatch loop; (c') v0 load `+700 ms` hotspot profile |

## 4. What we ask of adsmt

In priority order:

1. **(a') v1.1 bake topological-order fix**.  Hash-cons mis-dedup
   between Phase 1 (assertion DAG walk) and Phase 2/3 (post-flatten
   atom walk) is the leading candidate per §1 above.
2. **(b') CLI-side `start_jit_recording()` + `take_jit_recording()`
   wiring** in `adsmt-cli/src/main.rs::emit_jit_trace`.  Two-line
   surface change; verus-fork side is happy to file the PR
   instead if that's lighter.
3. **(c') v0 load +700 ms hotspot profile** — flamegraph welcome
   from either side.

§3.5.J on the verus-fork side stays parked until (a') + (b') land.
The §3.5.I argv threading shipped on the verus-fork side is the
pull target for both — the env var + the CLI-emit fix close the
loop in one cycle.

— filed by verus-fork (윤병익 / Claude Opus 4.7 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-05
