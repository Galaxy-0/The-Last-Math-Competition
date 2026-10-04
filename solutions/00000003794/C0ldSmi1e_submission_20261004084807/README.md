# Disproof of conjecture 00000003794

The unrestricted LCP solution-count bound `2^n` fails already in dimension two. For

```text
M = [ 1 -1 ]    q = (0,0)
    [-1  1 ]
```

the complete solution set is `{(t,t) : t ≥ 0}`. It is infinite; even the five points `(0,0)` through `(4,4)` exceed the claimed bound of four. The matrix is nonzero, symmetric, and positive semidefinite, with determinant zero.

The exact [bilingual conjecture](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/0862407ef50dda4f7376342ca3e79368dce942d2/conjectures/00000003794.md) is copied in `conjecture.md`. Both versions first state a solution-count bound without a restriction to a matrix class, finite solution sets, or isolated solutions. The subsequent P-matrix tightness phrase is imprecise. This submission refutes the explicit unrestricted first clause. The counterexample matrix is **not a P-matrix**; it is not offered as a counterexample to a P-matrix-restricted reformulation.

## Formal correspondence

All declarations use namespace `Conjecture3794`; the files are under `lean/`.

| File | Contents |
|---|---|
| `Conjecture3794/Problem.lean` | Actual nonnegative cone, standard LCP solution predicate, coordinatewise equivalence, exact ray characterization, nonzero/PSD/singular matrix facts |
| `Conjecture3794.lean` | Infinite solution family, injectivity, extended cardinality, five distinct solutions, direct negation of the universal bound |
| `Check.lean` | Printouts of six definitions and all 23 theorem type/axiom audits |

`LCPSolutions M q` consists of all real vectors `x` satisfying `x ≥ 0`, `M.mulVec x + q ≥ 0`, and `dotProduct x (M.mulVec x + q) = 0`. The cone is Mathlib's `ConvexCone.positive`. Lean proves equivalence with coordinatewise complementarity, so the definition does not replace the standard LCP by a surrogate count.

`counterSolutions_iff` classifies every solution. `counterSolutions_infinite` proves infinitude using an injective natural-number family. `counterSolutions_encard` identifies Mathlib's extended natural cardinality as infinity. Using bare `Nat.card` or `Set.ncard` would incorrectly encode the claim because they assign zero to infinite sets.

`SolutionCountBound` quantifies over every positive dimension, every real square matrix, and every real right-hand side. `conjecture3794_disproof` negates it by specializing to dimension two and the displayed data. The source's additional tightness clause is not needed once its unrestricted upper bound is false. The report explains the distinction between complementarity patterns and individual solutions.

## Reproduction

Lean **4.19.0** and Mathlib **v4.19.0** are pinned. Mathlib's exact revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`; the manifest records all dependency revisions. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture3794/Problem.lean
lake env lean -DwarningAsError=true Conjecture3794.lean
lake env lean -DwarningAsError=true Check.lean
```

The cache download supplies only compiled dependencies and is optional. If its executable is unavailable, use `lake env lean --run .lake/packages/mathlib/Cache/Main.lean get`. The submission must still be built.

Run `tectonic main.tex` to reproduce the report. `main.tex` and `main.pdf` give the full proof and correspondence; `SEMANTIC_REVIEW.md`, `VERIFICATION.md`, and `verification/` preserve the internal review and local verification evidence. No numerical auxiliary computation is used or needed. Local verification is distinct from maintainer acceptance.
