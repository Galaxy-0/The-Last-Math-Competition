# Disprove conjecture 00000002718: the tetrahedron boundary is shellable but not 2-collapsible

- **Claim refuted.** The first conjunct: every shellable d-dimensional complex is d-collapsible. Refuting it refutes the conjunction; the clauses "not conversely", "minimal separating complex" and "separation spectrum" are not addressed.
- **Witness.** The boundary of the tetrahedron: all proper subsets of Fin 4, a pure 2-dimensional simplicial complex with 15 faces.
- **Shellable.** The order 012, 013, 023, 123 is a shelling: B₂ = ⟨01⟩, B₃ = ⟨02, 03⟩, B₄ = ⟨12, 13, 23⟩ are each pure of dimension 1 (Björner's definition, retrieved).
- **Not 2-collapsible.** Wegner's d-collapse in Tancer's exact form (arXiv:0808.1991, quoted): every non-maximal face lies in at least 2 triangles (edges in 2, vertices in 3, the empty face in 4), so no face of dimension ≤ 1 lies in a unique maximal face, no collapse step can start, and the complex cannot reach ∅.
- **Robustness.** `stuck_of_no_free_face`: any move that needs a free face is stuck at the first step, which covers Whitehead's simplicial and elementary collapses (so the complex is not collapsible to a point either).
- **Readings.** d is the dimension of the complex; two nonstandard readings of the gloss "matched contractions of d-faces" (deleting a facet on its own; edge contractions) are not covered and are named in the risk note.
- **Main theorems.** `C2718.conjecture2718_false` (quantified over all n, d and K : Finset (Finset (Fin n))) and `C2718.counterexample`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 237 lines; finite facts by `decide` on Finset (Finset (Fin 4)). Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2718/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002718.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2718.conjecture2718_false`, `C2718.counterexample`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002718 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
