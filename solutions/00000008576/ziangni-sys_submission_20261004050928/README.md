# Disproof of conjecture 00000008576

The actual Jordan operator `T(x,y)=(x+y,y)` on the Euclidean Hilbert space `ℂ²` has minimal positive isometry order 3, exceeding its complex dimension 2. This refutes the explicit minimal-order dimension-bound conjunct in both source languages.

## Contents

- `proof.tex`, `proof.pdf`: complete proof and Hilbert-space correspondence.
- `lean/Main.lean`: actual complex matrix powers, full binomial Gram identities at orders 1, 2, 3, genuine orthonormal-basis star-algebra representation on EuclideanSpace, continuity, transported operator identities, positive-order minimality and actual dimension.
- `lean/`: publicly pinned Lean 4.19.0 / Mathlib project configuration.
- `verification/`: original source, strengthened eligibility checks, compilation logs, dependency audits and PDF QA.

## Reproduce

From `lean/`, run:

```text
lake update
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

The proof contains no sorry, admit, native_decide or custom axioms. Standard logical axioms are the only audited dependencies. No auxiliary computations are needed.

The standard m-isometry condition is the actual binomial adjoint identity `Σ(-1)^(m−j) choose(m,j) (T^j)* T^j=0`, for positive m. Matrix conjugate transpose is the adjoint in the standard orthonormal basis. The formalization verifies this correspondence through Mathlib's genuine star-algebra equivalence `LinearMap.toMatrixOrthonormal` on `EuclideanSpace ℂ (Fin 2)`. It does not treat the default Pi supremum norm as a Hilbert norm. Continuity of the actual operator is also proved.

Order-one and order-two sums are nonzero full matrices; the order-three full matrix sum vanishes. These identities transport to the actual Hilbert-space operator, so positive minimality is 3. The ambient complex finrank is exactly 2. No assertions about the conjecture's separate spectral or decomposition clauses are required.

The built-in LaTeX source editor/compiler was attempted but encountered its existing platform-directory error. Tectonic compiled the delivered two-page PDF, and both final pages were rendered and visually inspected. Ignored local junctions and build products are not committed.
