# Disprove conjecture 00000000238: D₇ is not the densest 7-dimensional lattice packing

- **Claim refuted.** The densest lattice packings in dimensions 5, 6 and 7 are given by the D lattices. The dimension-7 case fails, which refutes the conjunction.
- **Witness.** Unit balls centred at the ℤ-span of the rows 1000111, 0101011, 0011101, 2e₄, 2e₅, 2e₆, 2e₇, a sublattice of Construction A on the [7,3,4] simplex code (an integral model of √2·E₇): minimum distance 2, covolume 16, centre density 1/16.
- **Comparison.** Every unit-ball packing centred at a similar copy c·φ(D₇) (any scale c ≠ 0, any isometry φ) has covolume 2|c|⁷ ≥ 16√2, since non-overlap forces |c| ≥ √2; so it is strictly less dense (centre density ≤ 2^{−9/2} ≈ 0.0442).
- **Definitions.** A lattice packing is a discrete, full-rank ℤ-submodule of Euclidean ℝⁿ with pairwise disjoint open unit balls; density is ball volume / `ZLattice.covolume`, proved equal to the filled fraction of any fundamental domain (`LatticePacking.filled_fraction`); D_n = {x ∈ ℤⁿ : Σxᵢ even}.
- **Computation.** Covolumes via `ZLattice.covolume_eq_det_mul_measureReal` and triangular determinants (16 and 2); |det φ| = 1 for isometries; codeword weights by `decide` on the finite code.
- **Not addressed.** n = 5, n = 6, and the clause about settling the question through Voronoi cell volumes (a statement about method).
- **Main theorems.** `C238.exists_packing_denser_than_D7`, `C238.conjecture_238_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 360 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture238/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000238.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C238.exists_packing_denser_than_D7`, `C238.conjecture_238_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000238 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
