---
name: Ask before writing copyright notices
description: User explicitly instructed that copyright/attribution notices in LICENSE / file headers / NOTICE must be confirmed before being written
type: feedback
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
Never invent or guess a copyright holder name in LICENSE files,
per-file SPDX/copyright headers, NOTICE files, README badges, or
package metadata. Always ask first.

**Why:** On 2026-05-16 I drafted `LICENSE-BSD.txt` with "the adsmt
project contributors" as the copyright holder without checking with
the user. The user immediately corrected with their actual name
("Honey-Be / Yeun Byung-Ik") and instructed: "저작권 표기에 관해서는
내게 먼저 물어보도록." Copyright notation is legally meaningful and
the user wants it explicit — placeholder names create maintenance
burden and can be misread as authoritative.

**How to apply:**
- Before writing or staging any of:
  * `LICENSE-*` / `COPYING-*` / `NOTICE` files
  * `Copyright (c) ...` lines in source headers
  * `authors = [...]` in Cargo.toml / pyproject.toml / etc.
  * README badges naming a copyright holder
  * Any commit message that asserts copyright on the user's behalf
  ask the user explicitly which name (and what spelling /
  romanization / order) to use.
- For Korean names specifically, ask about preferred romanization
  (e.g. "Yeun Byung-Ik" vs "Yeun, Byungik" vs "Byung-Ik Yeun")
  rather than guessing.
- If a contribution is shared (multiple authors), ask whether to
  list them individually, use "and contributors", or some other
  form.
- Copyright year follows the actual creation/modification year
  (the current calendar year is fine for new files); this part
  doesn't need a question unless the user has a specific policy.
