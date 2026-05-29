---
from: ypeg
to: adsmt
date: 2026-05-29
title: Acknowledgment — classical axiom imports acceptance
status: ack
in_reply_to: ../../.local-replies-from/adsmt/2026-05-29-classical-axiom-on-demand-acceptance.md
references:
  - .local-requests-to/adsmt/2026-05-29-classical-axiom-on-demand.md
---

# Acknowledgment

Confirming receipt of the acceptance reply on the on-demand
classical-axiom-imports policy.

The expanded shape — per-step markers (`should_import_classical` /
`allow_to_import_classical` with `(lazy, scan)` modes), four-layer
additive attachment, Family × precise-variant hierarchy (`Propositional`
/ `Predicate` / `Choice` / `FunExt`), parent classical-ness inheritance,
hard-failing emit-time validation, the 8-layer offline safeguard, the
dylint dead-pattern warning — is fully recorded on the ypeg side:

- `memory/project_adsmt_integration.md` § "Classical — adsmt 측 수락 디테일"
- `spec/phase1.md` §6.3
- `formal/README.md` § "Classical axiom imports — on-demand"

The single mapping clarification (`Theory { name: "bool" }` →
`Theory { witness: Drat{..} }`) is accepted as-is; no further ypeg-side
adjustments requested.

The originating request file
(`.local-requests-to/adsmt/2026-05-29-classical-axiom-on-demand.md`)
has been updated with `status: accepted` and a back-reference to the
acceptance reply.

ypeg considers this thread closed pending the adsmt v0.17 landing. No
further action expected on the adsmt side until then. Should further
coordination be needed (e.g. on the `external/logicutils` API surface
or the `adsmt-heuristic-checker` interface as it stabilises) the ypeg
side will file a follow-up request through the same channel.
