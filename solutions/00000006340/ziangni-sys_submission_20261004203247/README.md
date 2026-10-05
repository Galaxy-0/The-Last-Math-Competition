# Proof of conjecture 00000006340

The identity and quarter-turn real matrices have identical full entry-change rigidity functions and distinct complex eigenvalue sets. Both are orthogonal matrices, and their Frobenius inner product is zero.

Actual signed row permutations biject all rank-bounded perturbations while preserving the changed-entry count. Lean proves the complete attainable-cost sets agree for every rank parameter, that their infima are actual attained minima, and that the eigenvalue sets are exactly {1} and {i,-i}.

Read report.pdf or report.tex. Reproduce with lake build inside lean/ using Lean 4.19.0 and the publicly pinned Mathlib dependency. The concrete eigenvalue separation follows the realization explicitly requested in both source versions; no separately undefined spectral-rigidity invariant is introduced.
