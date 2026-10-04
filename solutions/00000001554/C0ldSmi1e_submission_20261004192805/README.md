# Disproof of conjecture 00000001554

Color the ordinary Euclidean plane in alternating half-open horizontal strips of width `sqrt(3)/2`. No three points of a single color have all three pairwise Euclidean distances equal to one. This refutes the explicit unit-equilateral-triangle assertion in both language versions of the conjecture.

The construction is classical, recorded in Jelínek–Kynčl–Stolař–Valla, *Monochromatic triangles in two-colored plane*, Section 1, p. 2 ([arXiv:math/0701940](https://arxiv.org/abs/math/0701940)). The submitted proof is self-contained and does not import that result as an assumption. It covers the full plane, every triangle orientation, negative heights, equal vertex heights, and strip boundaries.

## Contents

- `conjecture.md`: exact bilingual source copied from the repository.
- `main.tex` and `main.pdf`: complete argument and attribution.
- `lean/`: Lean 4.19.0 project with Mathlib v4.19.0 and all dependency revisions pinned in its manifest.
- `VERIFICATION.md` and `verification/`: build, source replay, declaration/axiom audit, PDF and eligibility evidence.
- `SEMANTIC_REVIEW.md`: independent scrutiny of the final definitions and theorem.

## Reproduction

From this submission's `lean` directory, with the pinned Lean toolchain available:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture1554/Geometry.lean
lake env lean -DwarningAsError=true Conjecture1554/Coloring.lean
lake env lean -DwarningAsError=true Conjecture1554.lean
lake env lean -DwarningAsError=true Check.lean
```

`Check.lean` prints all nine named definitions/abbreviations, all eighteen theorem types, and all eighteen theorem axiom dependencies. The verification record gives the exact source hashes and the independent execution results. The project has no custom axioms, admitted proofs, `native_decide`, or auxiliary numerical programs.

The report can be compiled with a standard LaTeX installation supporting its declared packages; the submitted PDF was exported with Tectonic 0.17.0 and both pages were visually inspected.

## Correspondence to the statement

`Plane` is `EuclideanSpace ℝ (Fin 2)`, with its actual Euclidean metric. `unitEquilateral` requires all three actual distances to equal one. `stripeColor` is a total function from this plane to `Bool`; `stripeColor_surjective` proves that both colors occur.

`Geometry.lean` derives the height identity from the three squared-distance equations and bounds adjacent height gaps by the strip width while bounding the total height span below by that width. `Coloring.lean` proves the floor/parity assertions for all real heights using integer floor. The main module handles all six weak height orders. It proves `stripeColor_has_no_monochromatic_unit_triangle` and then `unit_triangle_ramsey_false : ¬ UnitTriangleRamsey`, where the latter claim quantifies over every two-coloring of the entire plane.

The source's additional assertion about deriving the unit version from similarity images cannot rescue its false first assertion. We do not formalize unspecified “rational-affine combinatorial closure,” and we do not claim that monochromatic equilateral triangles of arbitrary other side lengths are absent.

All verification supplied here is local. Maintainer acceptance is a separate decision.
