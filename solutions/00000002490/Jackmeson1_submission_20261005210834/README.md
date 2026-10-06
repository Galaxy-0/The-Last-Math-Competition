# Prove conjecture 00000002490: subspace counts over F_q are Gaussian binomials, with q-Pascal and interval closure

- **Classical theorem, formalized.** For every finite field F with q elements, the number of k-dimensional subspaces of Fⁿ equals the Gaussian binomial [n k]_q, for all n and k (including n = 0, k = 0).
- **Proof.** Count ordered linearly independent k-tuples two ways (Mathlib `card_linearIndependent`); then [n k]_x·∏(x^k − x^i) = ∏(x^n − x^i) holds in any commutative ring, and we cancel in ℤ.
- **Gaussian binomial.** Defined in ℕ[q] by the q-Pascal recursion; its equality with the textbook product formula is proved (`gaussBinom_mul_qDen`), and the formula determines the polynomial uniquely (`qDen_X_ne_zero`).
- **"Closes under".** The counts satisfy both q-Pascal rules, N(n+1,k+1) = N(n,k) + q^{k+1}N(n,k+1) and (for k ≤ n) N(n+1,k+1) = N(n,k+1) + q^{n−k}N(n,k); and every interval [U, T] of the subspace lattice is counted by [dim T − dim U, k − dim U]_q (via V/U and restriction to T).
- **Scope.** "Partitions" appears only in the heading and is not formalized; other meanings of "closes under" are left open. The companion conjecture 00000002478 (Gauss expansion) is treated in its own package.
- **Source.** Wikipedia, "Gaussian binomial coefficient" (retrieved; quotes machine-checked).
- **Main theorem.** `C2490.conjecture_2490`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 365 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2490/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002490.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2490.conjecture_2490`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002490 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
