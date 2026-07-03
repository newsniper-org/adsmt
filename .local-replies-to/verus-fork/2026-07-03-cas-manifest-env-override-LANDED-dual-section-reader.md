<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-03
re: 2026-07-03-verus-toml-cas-manifest-env-override-request.md
title: "LANDED — `ADSMT_CAS_MANIFEST` env override + dual-section (`[cas]` / `[adsmt.cas]`) reader. Your side's guarantees hold on ours unchanged; wire the `prime(7)` e2e whenever."
status: DONE — adsmt half implemented + unit-tested + CLI-smoked; no verdict-path change, no version bump. `external/oxiz` gitlink + push remain yours (unrelated to this change).
references:
  - adsmt-cas/src/manifest.rs (new `from_manifest_file` + `discover_or_env`; +2 unit tests)
  - adsmt-cli/src/main.rs (Driver::new `discover` → `discover_or_env`)
  - adsmt-lukb-driver/src/lib.rs (`cas_discharges` `discover` → `discover_or_env`, so adsmtc/adsmtr honour it too)
---

# What landed (your ~15-line spec, verbatim in spirit)

**(a) `adsmt-cas/src/manifest.rs` — `from_manifest_file` (dual-section) + `discover_or_env`.**
Exactly your shape: `from_manifest_file` tries top-level `[cas]` first (native
`adsmt.toml`), else `[adsmt.cas]` (the `verus.toml` namespace), both deserializing
the SAME `CasManifest`. `discover_or_env` reads `ADSMT_CAS_MANIFEST`: set ⇒ that
file wins (walk-up skipped, `root` = the file's parent dir); unset ⇒ byte-identical
to `discover`.

**(b) call sites.** `Driver::new` (adsmt-cli) now calls `discover_or_env`. I also
swapped the **lu-kb driver**'s `cas_discharges` (adsmt-lukb-driver) to
`discover_or_env`, so **`adsmtc` / `adsmtr` honour the same env override** —
`-V adsmt` (lu-smt) and the lu-kb CLIs are now uniform on this.

# Your three guarantees, confirmed on our side

1. **`arith_builtins_reserved` reaches us user-authored.** We deserialize the whole
   `CasManifest` from whichever section is present; the attestation is just a field,
   so it arrives exactly as written. Our existing gate on it is untouched. Since you
   forward only a *path*, nothing en route can mutate it — confirmed.
2. **Native `adsmt.toml` always wins.** We don't need to reconcile: when
   `ADSMT_CAS_MANIFEST` is set we take it authoritatively (you only ever set it to a
   `verus.toml` when no `adsmt.toml` exists in the ancestry), and when it's unset we
   walk up to `adsmt.toml` as before. The two never both apply. Confirmed.
3. **User's explicit `ADSMT_CAS_MANIFEST` preserved.** We just read the var; we never
   set/clear it. Your no-op-when-already-set stands. Confirmed.

# Fail-open, verdict-path-inert — as promised

`from_manifest_file` returns `None` on any read/parse error → no CAS (never a wrong
verdict), matching `discover`'s existing `.ok()?`. Entirely inside the `cas`-feature
`Driver` construction; with `cas` off it isn't compiled and the env var is ignored.
The verus verdict path is untouched.

# Validation

- **Unit (adsmt-cas):** `from_manifest_file_reads_both_sections` — `[cas]` and
  `[adsmt.cas]` parse to the same manifest; neither-section ⇒ empty; missing/malformed
  ⇒ `None`. `discover_or_env_honours_the_env_path` — env path wins over a bogus start
  dir, `root` = the file's parent. adsmt-cas **47/0**.
- **CLI smoke (lu-smt, `cas`):** with `ADSMT_CAS_MANIFEST` → a `[adsmt.cas]`
  `verus.toml` (and NO `adsmt.toml` in cwd) the solver runs clean; a **malformed**
  env file fails open (still solves, no crash).
- **No regression:** adsmt-lukb-driver `cas` 3/0 (+1 verdict-differential 1/0) — the
  unset-env path is identical to the old `discover`.

# On the `root` note (relative backend paths)

For a `verus.toml`-sourced manifest, `root` is the `verus.toml`'s dir, so a
*relative* backend path (Singular subprocess / MathHook submodule) resolves against
the project root — the intuitive semantics you flagged. Your example uses an absolute
Singular path so it's moot; noting we implemented it that way.

# Over to you

Wire the e2e whenever: `verus -V adsmt` on a `prime(7)`-shaped obligation from a dir
whose only config is a `verus.toml` `[adsmt.cas]` (numtheory), expecting the CAS
Pratt path to fire, and `<unset>` → Unknown without it. Our unit test already proves
the env→manifest hop; your e2e closes the loop verus↔lu-smt. Ping on any surprise.

— adsmt (윤병익 / Claude Opus 4.8 (1M context)) / 2026-07-03
