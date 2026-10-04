# Disproof of conjecture 00000000367

The nondegenerate recurrence `u_n = 2^n + (1/3)^n` has exact distance `(1/3)^n` from the integers at every positive index. This distance is positive but eventually smaller than `n^(-C)` for every real exponent C. Thus even an eventual version of the conjectured lower bound is false. The sequence has true minimal order two and tends to infinity.

A supplemental example, `v_n = 2^n + 3^n`, has integer coefficients and integer initial data. It is also nondegenerate of minimal order two, but every term is an integer. The source does not exclude such sequences. The main example additionally refutes the assertion for nonintegral terms under the standard rational-coefficient convention.

The exact bilingual source is included as `conjecture.md`. The report states the coefficient and nondegeneracy conventions explicitly and cites a primary reference. Failure of the existence of any lower-bound exponent suffices to refute the stronger assertion that an explicit exponent is determined by root-modulus gaps.

## Reproduce the Lean verification

Lean 4.19.0 and Mathlib v4.19.0 are pinned, with all nine dependency revisions locked in the manifest. From `lean/`, after installing the pinned toolchain and fetching the pinned dependencies:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture367/Definitions.lean
lake env lean -DwarningAsError=true Conjecture367/Recurrence.lean
lake env lean -DwarningAsError=true Conjecture367/Distance.lean
lake env lean -DwarningAsError=true Conjecture367/Asymptotics.lean
lake env lean -DwarningAsError=true Conjecture367.lean
lake env lean -DwarningAsError=true Check.lean
```

`Check.lean` prints all seven definitions and checks the types and transitive axiom dependencies of all 35 named theorems. Only the usual `propext`, `Classical.choice`, and `Quot.sound` occur. There are no admitted proofs, custom axioms, native decision proofs, or auxiliary numerical computations.

## Contents

- `lean/Conjecture367/Definitions.lean`: actual recurrence family, minimality, complex-root nondegeneracy, distance to the integer set, and eventual lower-bound assertion.
- `lean/Conjecture367/Recurrence.lean`: satisfaction of the recurrence, its actual characteristic polynomial and complete complex roots, minimality, nondegeneracy, and rational/integer coefficient certificates.
- `lean/Conjecture367/Distance.lean`: bridge from `Metric.infDist` to the nearest integer, exact distances, nonintegrality, rationality, and divergence to infinity.
- `lean/Conjecture367/Asymptotics.lean`: exponential decay beats every real power along the full sequence.
- `lean/Conjecture367.lean`: final eventual inequality and two unconditional disproofs, `conjecture_false` and `conjecture_false_integer_example`.
- `main.tex` and `main.pdf`: matching report. Standard LaTeX packages only; compile with `pdflatex main.tex` twice or `tectonic main.tex`.
- `VERIFICATION.md`, `SEMANTIC_REVIEW.md`, and `verification/`: exact execution, identity, eligibility, and independent internal semantic-review records.

The execution records document a fresh build in a separate project directory, reusing the pinned dependency cache but no compiled submission outputs. Local validation and internal review are distinct from official maintainer acceptance.
