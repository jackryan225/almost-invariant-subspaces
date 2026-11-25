# Build record

`clean-build.log` is the record of one run on 25 November 2026: this repository was copied to an empty folder and built
with Lean 4.34.1 and the pinned Mathlib. The machine name and the home folder are replaced by `<host>` and `<home>`.

| Step in the log | Command | Result |
|---|---|---|
| 0 | checksums of the source files | equal |
| 1 | `lake exe cache get && lake build` | exit 0 |
| 2 | `lake env lean Check/Axioms.lean` | 11 results, each with `propext`, `Classical.choice`, `Quot.sound` only |
| 3 | `lake env lean Check/AxiomsFull.lean` | 9 results, each with the same three axioms only |
| 4 | `lake build Challenge`, then `Check/SameStatement.lean` and `Check/SameStatementFull.lean` | each statement is equal to its proved twin, as terms; no `sorryAx` |
| 5 | `lake env lean Check/Contains.lean` | exit 0; 2 results with the same three axioms only |
| 6 | search for `sorry`, `native_decide` and `axiom` in the proof files | no line |
| 7 | `lake env leanchecker` on the ten proof modules | exit 0 |
| last | `lean4export`, then `lean4lean`, for the five single-orbit theorems and for the five theorems of the full statement | 53073 and 19247 declarations checked; the only axioms in the exports are the same three |

`leanchecker` comes with Lean and checks the compiled proofs again with the kernel. `lean4lean` is a kernel written in
Lean, a separate program.
