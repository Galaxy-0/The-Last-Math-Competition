# Disproof of conjecture 00000000973

Every nonempty bounded complex set fails the conjecture's stated spectral-set property already in dimension two. Choose a point `λ` in the set and a finite bound `B` on its moduli. The Jordan matrix with diagonal `λ` and upper-right entry `R = |B| + |λ| + 1` has spectrum `{λ}`. For the polynomial `p(z) = z − λ`, its Euclidean operator norm is exactly `R`, while the actual supremum of `|p|` on the set is at most `|B| + |λ|`.

This applies to every union of two positive-radius disks, for any centers and radii, whether the disks are open or closed. Since `2 < 15`, it refutes the explicit low-order assertion in the exact bilingual [conjecture](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/0862407ef50dda4f7376342ca3e79368dce942d2/conjectures/00000000973.md), copied in `conjecture.md`. The disproof does not need to interpret the separate “minimal order” wording or decide the order-33 clause.

The source imposes spectrum containment alone. It does not impose normality, contractivity, or a resolvent bound. The report distinguishes this stated all-matrices definition from the usual operator-relative meaning of a spectral set.

## What Lean proves

All definitions are in namespace `Conjecture973`. The full predicate `SpectralSetOrder K n` quantifies over all complex `n × n` matrices with actual spectrum contained in `K` and all complex polynomials. The norm is explicitly the continuous linear operator norm on `EuclideanSpace ℂ (Fin n)` through `Matrix.toEuclideanCLM`. Polynomial evaluation is Mathlib's `Polynomial.aeval`, and the bound uses the genuine real `sSup` of polynomial moduli on `K`.

| File | Role |
|---|---|
| `Conjecture973/Jordan.lean` | Resolvent determinant, actual matrix and operator spectra, polynomial evaluation, exact Euclidean operator norm |
| `Conjecture973/BoundedSet.lean` | Full spectrality predicate, strict counterexample witness for every nonempty bounded set, negation of order-two spectrality |
| `Conjecture973.lean` | Nonempty bounded unions of disks; final negations for open and closed disks |
| `Check.lean` | Six definition printouts and 17 theorem type/axiom audits |

These files are under `lean/`. The final `conjecture973_disproof_closed` and `conjecture973_disproof_open` negate `SmallOrderClaim`, the necessary explicit clause asserting the inequality at every positive order below 15. The matrix witness is unrestricted by anything beyond the source's required spectrum containment.

The report's numerical example with centers 0 and 3, radii 1, and off-diagonal entry 5 illustrates the general proof; it is not a separate computational test or separately named Lean theorem. No numerical approximation or auxiliary computational program is used or needed.

## Reproduction

Lean **4.19.0** and Mathlib **v4.19.0** are pinned. Mathlib resolves to exact commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all dependency revisions are recorded in `lean/lake-manifest.json`. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture973/Jordan.lean
lake env lean -DwarningAsError=true Conjecture973/BoundedSet.lean
lake env lean -DwarningAsError=true Conjecture973.lean
lake env lean -DwarningAsError=true Check.lean
```

The cache download is optional; it only supplies compiled dependencies. If the cache executable is unavailable, use `lake env lean --run .lake/packages/mathlib/Cache/Main.lean get`. The submission itself must still be built.

The report can be reproduced with `tectonic main.tex`. `main.tex` and `main.pdf` give the complete proof and formal correspondence. `SEMANTIC_REVIEW.md` records independent internal semantic scrutiny, and `verification/` contains local build and audit evidence. These checks are distinct from official maintainer acceptance.
