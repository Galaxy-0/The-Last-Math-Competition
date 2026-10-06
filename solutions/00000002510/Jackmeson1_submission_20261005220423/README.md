# Prove conjecture 00000002510: bounded-rank tensors are not closed, so the W tensor has no best rank-2 approximation and approximating summands diverge

- **Known theorem.** de Silva–Lim (arXiv math/0607647, retrieved): "unlike matrices, tensors of order 3 or higher can fail to have best rank-r approximations". Formalized self-contained for real 2×2×2 tensors with the sup norm; rank = CP rank (least r with T a sum of r tensors a⊗b⊗c).
- **Unlike matrices (R1).** For all m, n, r the set of real m×n matrices with `Matrix.rank ≤ r` is closed, so best rank-≤r approximations exist (via `isOpen_setOfPred_nat_le_rank`).
- **Governed by closure (R2).** For every r, every tensor has a best rank-≤r approximation iff `rankLE r` is closed (a general lemma for proper metric spaces).
- **Not closed (R3).** W = e₁⊗e₁⊗e₂ + e₁⊗e₂⊗e₁ + e₂⊗e₁⊗e₁ is the limit of the rank-2 tensors (n+1)(e₁ + e₂/(n+1))^{⊗3} − (n+1)e₁^{⊗3}, but `tensorRank W = 3` (Cramer's rule on the slices and a vanishing 2×2 determinant force a contradiction W₁₀₀ = 0); so `infDist W (rankLE 2) = 0` and no best rank-≤2 approximation exists.
- **Limiting divergence (R4).** For any sequence of two-term decompositions converging to W, the norm of each summand tends to infinity (rebalance the factors, extract a convergent subsequence, get a two-term decomposition of W — impossible).
- **Scope.** The vague meta-claim is fixed as R1–R4; "not closed" is shown for real 2×2×2 tensors of rank ≤ 2; the best-approximation statements use the sup norm (closedness and divergence are norm-independent).
- **Main theorem.** `C2510.conjecture_2510`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 340 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2510/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002510.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2510.conjecture_2510`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002510 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
