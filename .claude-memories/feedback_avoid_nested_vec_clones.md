---
name: don-t-gratuitously-clone-nested-vec-container-types
description: "For container types that nest a Vec inside a Vec (e.g. CtorSpecs = Vec<(String, Vec<Term>, Vec<Term>)>), avoid unnecessary .clone() when you only need to read, or when it is the value's last use — prefer borrowing (&) or moving (into_iter). Hash-consing makes Term::clone O(1) (an Arc bump), but cloning the OUTER container still reallocates the Vec(s) + Strings, so the clone is not free even when the elements are. User tip, 2026-06-25, prompted by the adsmt-ir-smtlib CtorSpecs in the datatype face slice."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

When a type nests a `Vec` inside a `Vec` — `Vec<Vec<_>>`, or
`Vec<(_, Vec<_>, Vec<_>)>` like `CtorSpecs` / `CtorTriples` (the inductive
constructor spec) — a `.clone()` of it reallocates the **outer** `Vec` and every
inner `Vec`/`String`, even though, after hash-consing, each `Term` inside clones
in O(1) (an `Arc` refcount bump). So "the elements are cheap to clone" does **not**
make the container cheap to clone. Be careful that such clones aren't sprinkled
in where a borrow or a move would do.

**Why:** the user flagged this on the `adsmt-ir-smtlib` datatype face slice
(`CtorSpecs = Vec<(String, Vec<Term>, Vec<Term>)>`). It is the cousin of
[[feedback_hashcons_hot_paths]] (which says *use* the O(1) `Arc::ptr_eq`/clone in
hot paths): hash-consing made the *terms* cheap, which can lull you into cloning
whole nested-`Vec` containers freely — but the container structure is still real
work.

**How to apply:**

- **Read-only ⇒ borrow.** If a function only reads a nested-`Vec`, take `&[...]`
  / `&T`, don't clone to pass it. Iterate with `.iter()`, not `.clone()` then
  iterate.
- **Last use ⇒ move.** If the value is consumed at its last use, `into_iter()` /
  move the fields out instead of `.iter().map(|m| m.field.clone())`. Example fix:
  `inductive.rs::declare_mutual` recorded the AOT-bank journal with
  `members.iter().map(|m| IndSpec { params: m.params.clone(), …, ctors: m.ctors.clone() })`
  — but `members` is dead afterward, so it became
  `members.into_iter().map(|m| IndSpec { params: m.params, …, ctors: m.ctors })`,
  dropping a second clone of every member's params/indices/ctors
  (`adsmt-ir` `7ddbf9f`).
- **Necessary clones are fine.** A clone out of a `&` borrow that feeds a
  *consuming* admitter (e.g. `bank.rs::replay` cloning `&IndSpec` fields into
  `declare_inductive_indexed`, which must own them) is unavoidable — don't
  contort to remove those. When two owners genuinely both need the data (e.g.
  `declare_inductive_indexed` gives the journal a clone and `register_inductive`
  the original), one clone is the minimum.
- **Watch implicit clones too** (`.to_vec()`, `.collect()` over a borrowed
  iterator, `vec.clone()` in a struct-literal field) — not just literal
  `.clone()` calls.
- **The face elaborator stays clean by this rule:** it builds a `CtorSpecs` once
  in `parse_ctors` and **moves** it into `declare_*`, never re-cloning it.
