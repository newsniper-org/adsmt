---
name: pre-stable-feature-freeze
description: "On the user's backport signal, freeze the testing branch at rc.40 and defer ALL new adsmt features until the v1.0.0-stable release. Awaiting signal."
metadata: 
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**Pre-`v1.0.0-stable` phase: feature freeze on the testing branch at rc.40.** Decided 2026-06-22.

**Trigger (DO NOT act before it).** The user will *personally* backport the whole `main` branch onto the `testing` branch (wholesale), then give an explicit signal. The freeze is gated on that signal — until it arrives, normal `main` development continues unchanged.

**On the signal, act:**
1. Confirm `testing` is at the rc.40 version line (`1.0.0-rc.40`), matching `main`'s backport.
2. **Freeze `testing` at rc.40** as the entry into the pre-stable phase, and make the policy **explicit** ("명시하도록") — i.e., document it where it's visible (release notes / CHANGELOG / a freeze marker on `testing`, and the relevant book/PORTFOLIO roadmap section), not just in memory.

**The freeze = a FEATURE freeze, not a code freeze.** From the freeze onward until the `v1.0.0` stable release, **all NEW adsmt feature additions are collectively deferred** ("신규 기능 추가는 일괄 연기"). Still allowed in the pre-stable phase: bug/soundness fixes, completeness fixes, docs/comments/book, cross-platform hardening, version pins — i.e. the stabilization work the rc line is for. New *features* land post-`v1.0.0` (a later minor/major), not in the rc.40→stable window.

**Consistency with existing policy:** the `v1.0.0` stable cut itself still requires the explicit user sign-off ([[feedback_stable_signoff_user_approval]] — never autonomously bump `N.0.0-rc.M → N.0.0`). This freeze is the phase BEFORE that sign-off: testing pinned at rc.40, feature-frozen, accumulating only stabilization commits until the sign-off gate. Channels per [[release_channel_model]] (testing = the consumer line, [[v1_0_0_scope_expansion]]); rc.40 itself is the "CCFV engine, stabilized" cut ([[project_cycle_versioning]]).

**⚠️ OVERRIDE (user, 2026-06-25): the typed-ASP face ([[asp-face-design]]) is an EXPLICIT EXCEPTION — it is pulled INTO the `v1.0.0` cut (decision D, "기존 계획을 대폭 변경해서라도 v1.0.0 컷에 포함"), so it is NOT subject to this feature freeze.** Consequences: (1) the freeze SIGNAL is not imminent — **development continues on the `main` branch ONLY for the time being** (the user will NOT backport to `testing` during ASP-face development); (2) the `v1.0.0` cut now also waits on the whole ASP-face program (incl. the hard-gated L3 stable-model solver) — see [[v1_0_0_scope_expansion]]. The freeze posture still governs OTHER new-feature classes once the (now-delayed) signal arrives, but "typed-ASP face = a v1.0.0 feature" is settled and must not be re-deferred.
