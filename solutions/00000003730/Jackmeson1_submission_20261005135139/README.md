# Disprove conjecture 00000003730: complete bipartite graphs do not maximize energy, and paths do not minimize it among trees

- **Energy.** The sum of |eigenvalues| of Mathlib's adjacency matrix (`IsHermitian.eigenvalues`); Σλ² = tr A² is proved from the spectral theorem.
- **Values.** E(K_n) = 2(n−1) and E(K_{a,b}) = 2√(ab) ≤ a+b for all parameters; E(K_{1,3}) = 2√3 and E(P_4) = 2√5.
- **Maximum claims.** For every n ≥ 3, K_n beats every complete bipartite graph on n vertices; among bipartite graphs, P_4 (energy 2√5 > 4) beats every K_{a,b} with a+b = 4.
- **Tree claim.** Among trees on 4 vertices, the star K_{1,3} has less energy than the path P_4, so the path is not the minimizer.
- **Scope.** The tree claim is refuted at n = 4 only (a "sufficiently large n" reading is not covered); comparisons within a fixed edge count are not treated.
- **Main theorem.** `C3730.main : ¬MaxIsCompleteBipartite ∧ ¬MaxBipartiteIsCompleteBipartite ∧ ¬MinTreeIsPath`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 386 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #226 by orionsheep ("K5 energy 8 exceeds best complete bipartite 2*sqrt(6)") was closed without merging. The reviewer's reason: "the Lean proves 4*5 = 5*4, 'True := trivial', 8 = 4+4, 64 > 24; adjacency matrices, eigenvalues, energy, and complete bipartite graphs appear nowhere in Lean." This submission defines graph energy as the sum of |eigenvalues| of Mathlib's `SimpleGraph.adjMatrix`, using `Matrix.IsHermitian.eigenvalues`. It proves sum(lambda_i^2) = tr(A^2) from the spectral theorem. It proves E(K_n) = 2(n-1) for all n >= 1 and E(K_{a,b}) = 2 sqrt(ab) for all a, b (with `completeBipartiteGraph`), and E(K_{1,3}) = 2 sqrt 3 and E(P_4) = 2 sqrt 5 (with `pathGraph`). It shows both graphs on 4 vertices are trees (`IsTree`). It then refutes, in Lean, (i) "maximum energy is attained by a complete bipartite graph", over all graphs for every n >= 3 and over bipartite graphs at n = 4, and (ii) "among trees, the path has minimum energy", at n = 4. Part (ii) was not formalized in #226.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3730/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003730.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3730.main`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000003730 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
