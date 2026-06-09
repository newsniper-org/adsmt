---
name: ho-sld-nonpattern-deferral
description: Higher-order SLD covers only the Miller Lλ pattern fragment; non-pattern flex-head unification (constraint postponement) is deferred to v2.0.0-rc.1+
metadata: 
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

adsmt's higher-order abductive SLD (rc.32, `adsmt-abduce/src/rule_base.rs`)
implements **only the Miller Lλ pattern fragment**: a flexible rule
head `F b₁ … bₙ` unifies with a goal `t` iff `F` is schematic and the
args `b₁ … bₙ` are **distinct variables**, giving the MGU
`F ↦ λb̄. t`. `flex_pattern` returns `None` (→ `false`) for every
**non-pattern** flex head — rigid/non-variable args (`F(g(a))`,
`F(c)`) and repeated args (`F(x, x)`) — and that `None` must NOT fall
through to structural descent (which would misread `F(x,x)` as the
unifiable `(F x) x`, unsound).

**Decision (2026-06-08, user):** leave it as-is for now; handling
non-pattern flex heads via **constraint postponement** (the
λProlog / ELPI residual-constraint approach — option (b)) is
**deferred to v2.0.0-rc.1+**.

**Why the boundary is there:** full higher-order unification (Huet)
is *undecidable* and has *no MGU* (incomparable unifiers via
imitation/projection branching → candidate blow-up + non-terminating
SLD). The Miller pattern fragment is decidable with MGUs, so the
current `false` is *sound* ("this rule can't discharge this goal", not
a wrong answer) and the engine stays terminating. The other paths
(Huet imitation/projection, option (a)) are unfit for an SLD loop;
decidable extensions (option (c)) cover little extra.

**Note for whoever picks up v2.0.0-rc.1+:** our SLD matches a flex
head in the *rule head* against a *rigid goal*, so flex-flex pairs
barely arise — postponement's main payoff (deferring flex-flex) is
muted here; the real non-pattern cases are repeated/rigid args. A
postponement design would thread residual constraints through
`Candidate` and resolve (or drop the candidate) when later bindings
make them ground/pattern. See [[project_cycle_versioning]] (rc.32 row)
for where the pattern fragment landed.
