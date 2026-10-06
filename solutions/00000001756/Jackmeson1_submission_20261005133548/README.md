# Disprove conjecture 00000001756: d(3) = 2, but three partitions of 3 have pairwise coprime hook lengths

- **Main theorem.** `C1756.conjecture_1756_false : d3 = 2 ∧ hookCount 3 = 3 ∧ d3 ≠ hookCount 3`, stated on the actual objects.
- **d(3).** Every S₃ character table is a row/column permutation of [[1,1,1],[1,−1,1],[2,0,−1]]. That matrix has a 2×2 minor equal to −1, and every 3×3 submatrix has determinant ±6, so the largest order of a ±1-determinant square submatrix is 2.
- **Hook count.** Computed on Mathlib `Nat.Partition 3` and the Ferrers `YoungDiagram`: Lean proves the partitions of 3 are exactly (3), (2,1), (1,1,1), and their hook lengths are 3,2,1 / 3,1,1 / 3,2,1, all pairwise coprime, so the formula gives 3. The Ferrers construction is adapted, with credit, from the accepted solution 00000000428.
- **Character table, derived in Lean.** The trivial, sign and standard (sum-zero plane) representations are built as `FDRep ℂ (Perm (Fin 3))`, with characters 1, sgn and fix − 1. Lean proves they are irreducible (`FDRep.simple_iff_char_is_norm_one`), pairwise non-isomorphic, and that every irreducible complex representation is isomorphic to one of them (`FDRep.char_orthonormal` + class-function equations). `d3` is computed on the table of these characters, and `conjecture_1756_false_any_table` gives the same refutation for every character table (`IsCharTable`, any row/column order).
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 431 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #214 by orionsheep was closed without merging. The reviewer accepted the mathematics but rejected the formalization: "the capstone theorem conjecture_refuted : ¬((3:Nat) = 2) connects none of them: the refutation is assembled only in prose. Happy to re-review a version whose main theorem states d(3) = 2 ≠ 3 on the actual hook/partition objects." This submission's main theorem `conjecture_1756_false : d3 = 2 ∧ hookCount 3 = 3 ∧ d3 ≠ hookCount 3` is stated on the actual objects. `d3` is the supremum of the orders of ±1-determinant square submatrices of the S_3 character table, whose rows are the characters 1, sgn and fix−1 evaluated on conjugacy-class representatives. It is certified as class functions with the orthogonality relations and exactly 3 conjugacy classes. `hookCount n` counts Mathlib `Nat.Partition n` whose Ferrers `YoungDiagram` has pairwise coprime hook lengths, with the hooks computed from the cells. The file also proves that the partitions of 3 are exactly (3), (2,1) and (1,1,1).

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1756/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001756.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1756.conjecture_1756_false`, `C1756.conjecture_1756_false_any_table`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001756 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
