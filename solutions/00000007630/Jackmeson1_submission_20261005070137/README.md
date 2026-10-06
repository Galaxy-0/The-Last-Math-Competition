# Prove conjecture 00000007630: Cl(0,1,0) ≅ ℂ and Cl(0,0,1) ≅ ℝ[ε] have the same idempotents but different zero divisors

This proves the conjecture with the signature pair Q₁(t) = −t² (signature (0,1,0)) and Q₀(t) = 0 (signature (0,0,1)) on ℝ¹.
- **Same idempotents.** Via `CliffordAlgebraComplex.equiv` and `CliffordAlgebraDualNumber.equiv`, both Clifford algebras have exactly the idempotents {0, 1}, so `ncard` is 2 in each.
- **Different zero divisors.** In `Cl(Q₁)` the only zero divisor is 0. In `Cl(Q₀)` the zero divisors are the whole line ι(ℝ), with ι(1) ≠ 0 and ι(1)² = 0. In particular the two algebras are not isomorphic.
- **Main theorem:** `separation`.
- **Scope.** Q₀ is degenerate. Mathlib's `CliffordAlgebra` allows degenerate forms, and the Sylvester signature includes the null count r.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7630/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007630.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture7630.separation`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007630 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
