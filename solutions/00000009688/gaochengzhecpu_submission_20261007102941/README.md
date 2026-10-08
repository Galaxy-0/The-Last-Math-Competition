# Conjecture 00000009688: exponent intersections do not determine common zeros

The pairs `(exp(z)-1, exp(3z)-exp(2z))` and `(exp(z)-1, exp(3z)+exp(2z))` have identical full exponent sets `{0,1}` and `{2,3}`. The first pair has infinitely many common zeros `2πik`; the second has none. All coefficients are rational. This directly refutes the claimed dependence of common-zero count on the exponent-set intersection.

## Files and reproduction

- `main.tex`, `main.pdf`: complete mathematical disproof and formalization correspondence.
- `SOURCE.md`: exact source bytes, with provenance under `verification/`.
- `lean/`: portable Lean 4.19.0 project with Mathlib and all transitive commits pinned.
- `verify.py`: supplementary exact integer polynomial calculations.
- `verification/BUILD.json`, logs, and review records: actual verification evidence.

Inside `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. On a new machine, `lake exe cache get` can retrieve official dependency artifacts. The submitted project contains no local dependency paths. From the submission directory run `python verify.py` and `tectonic main.tex`.

## Formalization and limits

`expPoly` evaluates a genuine rational polynomial at the actual `Complex.exp z`. The support theorems compute `Polynomial.support`; the displayed analytic formulas follow from the exponential law. `zeroAt_injective` and `infinitely_many_common_zeros` establish a genuinely infinite family, while `no_common_zeros` excludes every complex common root of the comparison pair.

`no_intersection_count_formula` universally negates every intersection-only count function with values in extended naturals. `no_positive_zero_separation` separately rules out a positive distance between zero sets. The first contradiction does not depend on interpreting the source's unspecified separation constant or inserting an unstated finiteness assumption. All three exponential polynomials are nonzero, and their exponents and rational coefficients meet the stated domain.

Fresh validation builds this submission without its own previously compiled artifacts; only official, unmodified, commit-pinned dependency artifacts are reused. The proof audit permits only the standard Lean axioms. The auxiliary calculation checks coefficient supports and factorization exactly; it does not numerically infer infinitude. Every PDF page is visually reviewed. The built-in LaTeX editor/compiler is attempted, with its actual outcome recorded, and the existing Tectonic installation exports the PDF.

The authoring agent self-reviews the mathematics. The parent agent performs a separate adversarial review and fresh upstream duplicate/source checks before publication. No external independent review is claimed, and the authoring agent makes no GitHub writes.
