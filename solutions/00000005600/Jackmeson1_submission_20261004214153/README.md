# Prove conjecture 00000005600: same determinant, non-isomorphic echelon forms, noncommuting unimodular pair

The conjecture is an existence claim: there are two matrices with the same determinant but non-isomorphic echelon forms, and an explicit pair of noncommuting unimodular transformations realizes the separation.

**Witnesses.**
- The matrices are `M = [[1,-4],[0,4]]` and `N = [[2,0],[-2,2]]`, both of determinant 4.
- The transformations are `U = [[1,1],[0,1]]` and `V = [[1,0],[1,1]]` in `GL₂(ℤ)`. Both have determinant 1, and `UV ≠ VU`.
- `UM = diag(1,4)` and `VN = diag(2,2)` are the Hermite normal forms of `M` and `N`, and they differ.

**Stronger separation.** The cokernels `ℤ²/rowspace` are `ℤ/4` and `(ℤ/2)²`, so they are not isomorphic. This holds for every `H₁` row-equivalent to `M` and every `H₂` row-equivalent to `N`, so it does not depend on the echelon-form convention. In addition, no `P, Q ∈ GL₂(ℤ)` satisfy `PNQ = M`.

**Second reading.** The submission also proves a second reading, in which the separation comes from applying `UV` and `VU` to a single matrix.

This builds on the accepted solution of the near-duplicate 00000006330, which is credited (GPL-3.0).

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture5600/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000005600.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture5600.conjecture_5600`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000005600 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
