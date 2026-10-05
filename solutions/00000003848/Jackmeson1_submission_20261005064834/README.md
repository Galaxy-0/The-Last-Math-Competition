# Disprove conjecture 00000003848: the affine cell-core left-cell formula fails for every n

- **Claim refuted:** there is a bijection between the two-sided cells of the affine 0-Hecke monoid of type A_n^(1) and the (n+1)-cores, such that the number of left cells in a cell equals the number of distinct parts of the core after removing (n+1)-hooks.
- **Every n:** the empty partition is an (n+1)-core with 0 distinct parts, but every two-sided cell contains at least one left cell.
- **Non-degenerate case, n = 1:** the monoid ⟨π₀, π₁ | π_i² = π_i⟩ is J-trivial, so every cell contains exactly one left cell. Each staircase (k, …, 1) is a 2-core with k distinct parts, so for every bijection the formula fails at infinitely many non-empty cores.
- **Lean 4 / Mathlib v4.33.1, faithful objects:**
  - the monoid is a `PresentedMonoid` with absorption and braid relations from the Ã_n Coxeter matrix;
  - Green's J- and L-relations are proved to be equivalence relations;
  - partitions are `YoungDiagram`s, with hook lengths and t-cores.
- **Main theorems:** `not_cellCoreDictionary` (all n), `affineA1_jTrivial`, `affineA1_failures_infinite`, `not_cellCoreDictionary_one`.
- **Hook removal:** the argument uses only that the removal operation fixes the empty partition, or fixes cores (a core has no hook to remove). Every reading of the removal satisfies this.
- **Axioms:** propext, Classical.choice, Quot.sound only; no `sorry`, no `native_decide`.
- **Credit:** the Green's-relation set-up adapts the accepted solution of 00000003843 (orionsheep, GPL-3.0).

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3848/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003848.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3848.not_cellCoreDictionary`, `C3848.affineA1_failures_infinite`, `C3848.not_cellCoreDictionary_one`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000003848 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
