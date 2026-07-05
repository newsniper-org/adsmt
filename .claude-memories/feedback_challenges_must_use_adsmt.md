---
name: feedback-challenges-must-use-adsmt
description: "When the user poses research \"도전과제\" (challenge problems), they MUST be attacked USING adsmt as the tool, not answered as pure literature analysis."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

When the user hands over a "도전과제" (challenge-problem) list (e.g. 2026-07-02: HAMSA "Simplified Kernel Parametrization" analysis + integer-closed SSM in cryptography), the challenges MUST be **attacked using the adsmt project itself** — its CAS delegation (ideal-membership / factorization / primality-Pratt / GF(pⁿ) native arithmetic), the `*Like` families ([[numberlike_family_design]] — ComplexLike/IntegerLike/RealLike), the GF(p)/IntModulo/GFPower rings ([[cas_integration_proposal]] P1.10/P1.11), Singular / `integer_ring` Gröbner ([[verus_integer_ring_setup]]), the `cas-backend-numtheory` + live CAS-delegation just built, and the abductive engine — as the concrete instruments.

**Why:** the user reacted strongly ("반드시 adsmt를 활용해야 해!!!!") when I started a pure literature/ML analysis. The challenges are a way to EXERCISE adsmt on real algebraic/number-theoretic obligations, with adsmt playing BOTH roles: the VERIFIER (discharge exactness/primitivity/rank/irreducibility obligations) AND the ATTACKER (e.g. abduce a linear recurrence = the cryptanalysis of a linear SSM).

**How to apply:** for each challenge sub-question, (1) formulate the underlying claim as an algebraic obligation adsmt can discharge (ideal membership / determinant vanishing / factorization / primality / order), (2) actually RUN adsmt (build `lu-smt --features cas`, craft `.smt2`, use Singular/numtheory backends, GFPower, verus/integer_ring) to produce concrete "시도 과정 + 결과", (3) document the runs. Deliverable when asked: a **Typst** (`.typ`) feature-article manuscript under `<adsmt root>/.reports/` covering the attempt processes AND results. Push/report conventions unchanged.
