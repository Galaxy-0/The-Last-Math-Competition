# Disprove conjecture 00000001543: n collinear points on an irreducible curve determine only n−1 distances

- **Curve.** The line y = 0 is the zero set of the irreducible (prime) polynomial Y, so it is an irreducible real algebraic curve, and the statement as written does not exclude lines or circles.
- **Distances.** The points (0,0), …, (n−1,0) on it determine at most n−1 distinct Euclidean distances.
- **Failure.** For every c > 0 and every n > c⁻³, n−1 < c·n^{4/3}, so no positive constant works, whether uniform or depending on the curve, even if the bound is only required for large n.
- **Remark.** The statement omits the line/circle exception of Pach–de Zeeuw's theorem (arXiv:1308.0177, retrieved); with that exception the claim is a known theorem, which is not refuted.
- **Objects in Lean.** The Euclidean plane, irreducible polynomials in `MvPolynomial (Fin 2) ℝ` and their (infinite) zero sets, and the distinct-distance count as the card of the image of `dist` on pairs of distinct points.
- **Main theorems.** `C1543.xAxis_violates`, `C1543.not_uniform`, `C1543.not_per_curve_eventually`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 173 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #221 by orionsheep (closed, not merged) used the same counterexample: n equally spaced points on the line y = 0 determine only n - 1 distinct distances. The review rejected it because the Lean was vacuous: "no_constant is pure N arithmetic; the actual counterexample (collinear points determine n-1 distances) is never formalized - curves, points, and distances appear only in prose/Python." This submission formalizes the conjecture's objects in Lean. The plane is `EuclideanSpace R (Fin 2)`. An irreducible real algebraic curve is the infinite zero set of an irreducible `MvPolynomial (Fin 2) R`, and the x-axis is proved to be one via `X_prime`. Point sets are finite subsets of the curve, and the number of distinct distances is the cardinality of the image of `dist` on ordered pairs of distinct points. The Lean proves that the n collinear points determine at most n - 1 distances, and that for every c > 0 and all large n this is less than c n^(4/3). It refutes both a uniform constant and a curve-dependent constant with the bound required only for large n.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1543/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001543.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1543.xAxis_violates`, `C1543.not_uniform`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001543 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
