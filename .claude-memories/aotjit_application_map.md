---
name: aotjit-application-map
description: "2026-06-30 full analysis of where AOT + algebraic-JIT apply to OxiZ + oxiz-nl2 (the standing pre-port gate, discharged): 19 ranked items, 4-phase plan, native-codegen REJECTED-reinforced. Doc external/oxiz/docs/design/AOTJIT_APPLICATION_MAP.md (committed 36ed4c3, local)."
metadata: 
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

The standing pre-port AOT/JIT gate ([[oxiz-nlsat-redesign]]) is DISCHARGED (2026-06-30, 7-agent workflow). Doc: `external/oxiz/docs/design/AOTJIT_APPLICATION_MAP.md` (commit `36ed4c3`, LOCAL/UNPUSHED on OxiZ `0.2.4-redesign`).

**Lever (unchanged):** state reuse, not codegen — ~75% of prelude-scale solve is term/type-DAG construction + hash-cons, <5% solving (the [[aot-jit-profile-finding]]). **Native codegen REJECTED + REINFORCED:** the new nl2 evidence cuts AGAINST it (the nonlinear cost is bignum RECOMPUTE in resultant/Bareiss/Sturm, a memo target not a dynasm target; OxiZ is the delegation target so the hard solves have no prior trace).

**Highest leverage = prelude term-DAG state bake/reuse** (OxiZ analog of adsmt `--aot-load`, ~62% removable). In OxiZ the front-end is re-paid per fresh Verus VC process (`oxiz_inproc`, `adsmt-cli/src/main.rs:996`) and ONCE PER `:abduct-theory` SUBSET (`:1001`); `TermManager.terms` is `Arc<Vec<Term>>` so in-process reuse is near-free.

**Phasing:** P0 (soundness-free, NOW) = warm-Context clone for the abduct fan-out (`Context: Clone`, Arc pointer-bump) + simplex warm-start basis; P1 = cross-obligation digest verdict-memo (`compose_digest` ++ context-fingerprint at `context.rs:296`) — AND measure the abductive-subset recurrence that gates everything; P2 = on-disk `--aot-load` (bank.rs journal port → TermManager state-dump → EUF/simplex blobs, all re-admission/digest gated); P3 = nl2 algebraic memos (`poly_digest` enabler → resultant/Sturm/sign_of memos + G-SAT model bank), **CONDITIONAL on a recurring nonlinear prelude the Verus workload lacks (EUF/MBQI-bound)**. Replay/recorder items LOWEST priority — REDUNDANT with #263 persistent push/pop for the in-process backend.

**Soundness:** every cache exact-match gated, miss → full sound solve. 4 gate shapes: verdict-memo (K12 AdHash clause digest ++ context fingerprint, Definite-only), state-bake (re-admission/structural identity, term-DAG-paired), pure-kernel-memo (polynomial IDENTITY not ideal-membership; verdict still through G-SAT/G-UNSAT), monotone-bank (model bank by `Model::checks`, core bank by subset+monotonicity).
