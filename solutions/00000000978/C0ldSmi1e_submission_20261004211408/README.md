# Disproof of conjecture 00000000978

For the complex matrix `A = [[0,2],[0,0]]`, the actual Kippenhahn curve has infinitely many real points: its real affine chart is the unit circle. The actual numerical range is the closed unit disk, and its real algebraic boundary is the same circle. This contradicts the conjectured finite bound; for dimension two, `n(n-1)/2 = 1`. The characteristic polynomial is `X²`, so the only eigenvalue also has algebraic multiplicity two.

The source in both languages counts real points without restricting the count to isolated points, singular points, or components. The disproof addresses that literal statement. It uses extended cardinality (`Set.encard`), which retains infinity, and does not use the natural-valued cardinality that assigns zero to an infinite set.

## Contents and reproduction

The submission includes the exact bilingual `conjecture.md`, complete `main.tex`, matching `main.pdf`, the pinned Lean project, and execution and independent semantic-review records. From `lean/`, with the pinned toolchain available:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture978/Pencil.lean
lake env lean -DwarningAsError=true Conjecture978/DualCurve.lean
lake env lean -DwarningAsError=true Conjecture978/NumericalRange.lean
lake env lean -DwarningAsError=true Conjecture978/Boundary.lean
lake env lean -DwarningAsError=true Conjecture978.lean
lake env lean -DwarningAsError=true Check.lean
```

Lean 4.19.0 and Mathlib v4.19.0 are pinned; the manifest fixes all nine dependency revisions. The default build imports every proof module. `Check.lean` prints all 20 submitted definitions and checks all 50 theorem types and transitive axiom dependencies. There are no unnamed or private proof declarations. The report uses standard LaTeX packages; its matching PDF is exported with Tectonic 0.17.0.

## Correspondence with the conjecture

- `Pencil.lean` defines the actual matrix and its conjugate-transpose Hermitian parts. It constructs the determinant polynomial and links its evaluation to the matrix pencil. For the witness, it proves `p(u,v,w)=w²-u²-v²`, computes the actual formal gradient, and proves homogeneity, degree two and projective smoothness. Nilpotence and characteristic polynomial `X²` are also proved.
- `DualCurve.lean` defines the complex algebraic closure as the common zero locus of the actual vanishing ideal. Its dual cone comes from all nonzero scalar multiples of gradients at nonzero smooth polynomial zeros. The affine chart uses last coordinate one. The complex chart is the conic `x²+y²=1`, and its real chart is the real unit circle; neither is assigned by definition.
- `NumericalRange.lean` uses the actual Hermitian quadratic form and the sum of squared coordinate norms as its unit-vector condition, with a proved equivalence to `v* v = 1`. It proves both inclusions in the closed unit disk, including an explicit unit-vector witness for every disk point, and identifies the topological boundary.
- `Boundary.lean` uses the real Zariski closure of that topological boundary. The circle is already a real polynomial zero locus, so this closure fixes it. An injective rational parametrization proves infinitude, and the actual dual chart and algebraic boundary coincide for the witness. The root module states the resulting counterexample and negates the necessary two-dimensional bound.

The raw gradient construction is used for the projectively smooth determinant pencil of this witness. The formal necessary specialization explicitly restricts to that subclass; it does not claim that raw gradients of arbitrary nonreduced determinant polynomials define their reduced curves' duals. A universal bound would have to hold for the smooth witness as well. The equality between the dual chart and the algebraic boundary is proved for this matrix; no general equality for all matrices is assumed.

The report cites Paparella, Ramirez and Wang, [A proof of the elliptical range theorem via Kippenhahn's theorem](https://arxiv.org/abs/1807.04268), for projective-dual conventions and background. All matrix, numerical-range, closure and counting calculations used in the disproof are proved in Lean. No numerical approximation or auxiliary mathematical program is needed.

`VERIFICATION.md` describes the recorded checks. `SEMANTIC_REVIEW.md` is an independent internal review, and `verification/SHA256SUMS.json` hashes the submitted files except itself. Local validation and internal review are distinct from maintainer acceptance.
