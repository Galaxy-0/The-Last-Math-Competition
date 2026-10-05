# Disprove conjecture 00000002167: C5 and K_{1,4} both attain the maximum spectral radius 2 among 5-vertex graphs of girth ≥ 5

The conjecture ends with a uniqueness clause: for every n ≥ 5, the graph of girth ≥ 5 with maximum spectral radius is unique up to isomorphism. That clause already fails at n = 5. So the conjunction fails whatever "Moore-approximate (Brown/PC-lab type)" means.

**Bound.** Let G have girth ≥ 5 and n vertices. For every vertex i, ∑_{l~i} deg l ≤ n − 1: the sets N(l)∖{i} are pairwise disjoint (no 4-cycle), and they avoid {i} ∪ N(i) (no triangle). Apply this to A²v = λ²v at a coordinate where |v_i| is largest. This gives |λ| ≤ √(n−1) for every eigenvalue λ.

**Two extremal graphs.** C5 (Mathlib `cycleGraph 5`) and the star K_{1,4} both have girth ≥ 5. The forest K_{1,4} has girth ∞ by the standard convention, which is also Mathlib's `egirth`. Both graphs are connected and have eigenvalue 2 = √4, with eigenvectors (1,1,1,1,1) and (2,1,1,1,1). So both attain the maximum. They are not isomorphic: C5 has 5 edges and K_{1,4} has 4.

**Lean.** Everything is proved in Lean 4 with Mathlib. The spectral radius is Mathlib's `spectralRadius ℂ` of the adjacency matrix, and girth is `SimpleGraph.egirth`. The general bound is `spectralRadius_le_sqrt`. The main theorem `C2167.conjecture_false` refutes uniqueness both among all graphs and among connected graphs. Only the axioms propext, Classical.choice and Quot.sound are used. The build is clean with warnings treated as errors.

**Not formalized.** The same failure occurs at n = 10 (Petersen graph vs K_{1,9}) and at n = 50 (Hoffman–Singleton graph vs K_{1,49}). These are remarks only.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2167/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002167.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2167.conjecture_false`, `C2167.main`, `C2167.spectralRadius_le_sqrt`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000002167 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
