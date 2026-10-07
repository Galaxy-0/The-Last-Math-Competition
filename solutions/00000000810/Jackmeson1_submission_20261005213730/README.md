# Disprove conjecture 00000000810: no metric star minimizes the first positive Kirchhoff eigenvalue at fixed length and vertex count

- **Reading.** The first eigenvalue is the smallest positive eigenvalue of the standard (Kirchhoff) Laplacian in strong form (−f″ = λf on each edge, continuity at vertices, outgoing derivatives summing to zero). The star is K_{1,n−1} with any positive edge lengths summing to L.
- **Stars.** For n = k+1 ≥ 4, no metric star of length L has an eigenvalue in (0, π²/L²]: on each edge the eigenfunction is a cosine, and continuity plus Kirchhoff at the centre reduce to a trigonometric system that strict superadditivity of tan on (0, π/2) forces to vanish.
- **Path.** P_n of length L (k edges of length L/k) has the eigenvalue π²/L² (eigenfunction cos(πt/L)), so no star attains the minimum among metric graphs with n vertices and length L.
- **Among stars only.** Lengths (a, a, ε, …) give the eigenvalue (π/2a)², which beats any given star, so no star is minimal even when degree-2 vertices are excluded.
- **Scope.** Lean refutes the consequence "λ₁(S) ≤ every positive eigenvalue of every competitor"; one labelling/orientation of the star is fixed (relabelling invariance argued in proof.tex). The λ₀ = 0 reading (uniqueness fails trivially) is argued on paper only. Only the first conjunct is refuted, for n ≥ 4.
- **Main theorems.** `C810.not_star_minimizer`, `C810.not_star_minimizer_among_stars`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 430 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture810/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000810.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C810.not_star_minimizer`, `C810.not_star_minimizer_among_stars`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000810 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
