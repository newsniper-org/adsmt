# Q1 sort-gate battery — is the `Eq ∨ Lt ∨ Gt` trichotomy clause gated?

verus-fork's Q1 (2026-07-21): the trichotomy tautology added at the Tseitin
choke-point for #428 changes the encoding of EVERY equality-bearing
obligation. If it were emitted on a sort where trichotomy does NOT hold
(uninterpreted / datatype / BV / FP, or across an Int↔Real coercion), it
would be the one path that could silently manufacture `unsat` in the ~200
rows a diff-based sweep cannot see.

**Source answer**: gated at BOTH emission sites —
`oxiz-solver/src/solver/encode.rs:2056-2058` (the choke-point) and `:2618-2620`
(the older syntactic pre-pass) — on `lhs.sort ∈ {int_sort, real_sort}`. Bool
equality never reaches the theory path (it splits off at the `is_bool` branch
above). The gate reads only `lhs`, which is sufficient for a well-sorted term
but leaves the coercion boundary and parser leniency as a residual.

**Measured answer**: this battery. Each script places an equality of the
sort under test in the exact syntactic position the bug lived in (the
antecedent of an `Implies`), and is built so its TRUE answer is `sat` — a
wrongly-emitted `Lt ∨ Gt` would exclude `a = b` and turn it `unsat`.

| script | sort | expected | @ oxiz `88c2679` |
|---|---|---|---|
| `q1-uninterp` | uninterpreted `U` | not unsat | `sat` |
| `q1-bv` | `(_ BitVec 8)` | not unsat | `sat` |
| `q1-datatype` | recursive datatype | not unsat | `sat` |
| `q1-bool` | `Bool` | not unsat | `sat` |
| `q1-array` | `(Array Int Int)` | not unsat | `sat` |
| `q1-string` | `String` | not unsat | `sat` |
| `q1-int-real-coerce` | `(= (to_real x) y)` | not unsat | `unknown` |
| `q1-POSCTL-int` | `Int` — trichotomy DOES hold, must fire | **`unsat`** | `unsat` |
| `q3-illsorted-int-vs-U` | Int lhs ↔ `U` rhs (z3 REJECTS the term) | not unsat | `sat` |
| `q3-illsorted-int-vs-bv` | Int lhs ↔ BV rhs (z3 rejects) | not unsat | `sat` |
| `q3-illsorted-int-vs-dt` | Int lhs ↔ datatype rhs (z3 rejects) | not unsat | `sat` |

The `q3-*` trio targets the `lhs`-only residual directly: z3 refuses these
terms outright (`Sorts Int and U are incompatible`), oxiz accepts them, and
the trichotomy still manufactures nothing.

A mis-designed first attempt is recorded here so it is not repeated: a BV
probe of the form `(=> (= x b) false)` plus `(assert (= x b))` is a
PROPOSITIONAL contradiction, so its `unsat` says nothing about sorts. Every
script in this battery has `sat` as its true answer, except the positive
control.

Run: `oxiz <script>` (build with `cargo build --release -p oxiz-cli` inside
`external/oxiz`).

What this does NOT close: verus-fork's §6 point that a row whose verdict did
not change can still have its proof now resting on the new clause. That is
invisible to a diff sweep and this battery only widens the sample.
