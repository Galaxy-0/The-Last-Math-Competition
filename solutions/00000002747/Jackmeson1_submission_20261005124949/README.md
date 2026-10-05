# Disprove conjecture 00000002747: the capacity of M_m(M_n) exceeds (m−1)n²+n whenever mn ≥ 3, and is 0 ≠ 1 at m = n = 1

- **Witness.** Over any field K, the singular subspace of M_m(M_n(K)) ≅ M_{mn}(K) made of matrices with one zero scalar row has dimension (mn)² − mn, which exceeds (m−1)n² + n for all m, n ≥ 1 with mn ≥ 3 (at m = n = 2: 12 > 6).
- **m = n = 1.** The determinant is the single entry, so the capacity is 0, not 1.
- **Objects in Lean.** `BlockMat K m n` = M_m(M_n(K)) with `blockDet` through Mathlib's block isomorphism `Matrix.comp`; singular spaces are `Submodule`s on which `blockDet` vanishes; `capacity` is the supremum of their `finrank`.
- **Main theorems.** `C2747.conjecture_false` (the conjunction fails for any statement of the classification clause), `formula_lt_capacity`, `capacity_one_one`, `capacity_two_two`.
- **Scope.** Only a lower bound on capacity is used; the classification clause is not analysed.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 186 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #198 by orionsheep was closed without merging. Its mathematics (capacity 0 ≠ 1 at m = n = 1; a 12-dimensional singular zero-row subspace of M_2(M_2) = M_4, so capacity ≥ 12 > 6) is the same as here. The reviewer rejected the formalization: "no matrix space, determinant, or linear subspace in Lean (theorems are 0≠1 and 12>6); the decisive facts — det(λ)=λ on scalars and the 12-dimensional row-zero subspace being identically singular — are prose only." This submission formalizes the actual objects over an arbitrary field K. `BlockMat K m n` is M_m(M_n(K)), with determinant `blockDet` taken through Mathlib's block isomorphism `Matrix.comp`. Singular spaces are `Submodule`s on which `blockDet` vanishes, and `capacity` is the supremum of their `finrank`. It proves `capacity_one_one : capacity K 1 1 = 0`. It proves that the zero-row subspace is singular of `finrank` (mn)² − mn. It proves `formula_lt_capacity`: the formula fails for every m, n ≥ 1 with mn ≥ 3. The main theorem `conjecture_false` refutes the conjunction "capacity = (m−1)n² + n ∧ Classif m n" for an arbitrary formalization `Classif` of the classification clause.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2747/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002747.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2747.conjecture_false`, `C2747.formula_lt_capacity`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002747 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
