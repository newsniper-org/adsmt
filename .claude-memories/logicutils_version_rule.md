---
name: Logicutils v0.x-smt version rule
description: Versioning relationship between adsmt and the logicutils v0.x-smt branch
type: project
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
The logicutils `v0.x-smt` branch (the SMT-extension fork that lives at
`external/logicutils/`) tracks adsmt's minor version offset by +2:

  logicutils v0.x-smt minor = adsmt minor + 2

Examples:
- adsmt v0.1.x  ⇔  logicutils v0.3.x
- adsmt v0.5.x  ⇔  logicutils v0.5+2 = v0.7.x
- adsmt v0.9.x  ⇔  logicutils v0.11.x

**Why:** keeps a consistent offset so anyone reading either repo can
infer the matching counterpart without inspecting Cargo.toml. Adopted
2026-05-12 by user decision after adsmt-class/quant/abduce/parser
v0.1 was wired up.

**How to apply:**
- When bumping adsmt's version, also bump
  `external/logicutils/Cargo.toml` `[workspace.package].version` to
  `(new_adsmt_minor + 2).patch`.
- The comment above that field documents the rule inline.
- This applies only to the `v0.x-smt` branch in the submodule; the
  upstream `main` branch is unaffected.
