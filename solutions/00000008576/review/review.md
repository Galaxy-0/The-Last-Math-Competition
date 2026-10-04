# Solution Review — Conjecture 00000008576 (PR 409)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004050928`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- Read the complete bilingual conjecture. Base metadata marks it unsolved. The PR adds only its own submission directory.
- Read the full LaTeX source and both pages of the shipped PDF. Recompiled twice in a fresh directory; both passes exited 0. The rebuilt PDF has the same mathematical content; raw text differences are only compiler-specific spacing/ligature extraction artifacts.
- Fresh Lean 4.19.0/Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` project. Dependencies checked out with `MATHLIB_NO_CACHE_ON_UPDATE=1`, official cache artifacts unpacked with `leantar`, and final full `lake build` exited 0 at `[2796/2797] Built Main`. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0.
- No forbidden Lean construct occurs. All seven principal theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- No auxiliary computation is needed.

## Counterexample

Let `H=EuclideanSpace ℂ (Fin 2)` and let `T` be represented in the standard orthonormal basis by

`J = [[1,1],[0,1]]`.

For the standard positive-order m-isometry identity

`Σ_{j=0}^m (-1)^(m-j) C(m,j) (T*)^j T^j = 0`,

a direct calculation gives `(J^j)* J^j = [[1,j],[j,j^2+1]]`. Consequently:

- order 1: `[[0,1],[1,1]] ≠ 0`;
- order 2: `[[0,0],[0,2]] ≠ 0`;
- order 3: `0`.

Thus the least positive m for which the identity holds is 3. Meanwhile `Module.finrank ℂ H=2`. The conjectured law “minimal m ≤ dimension” therefore fails.

The Lean project formalizes all of these calculations as full matrix identities and transports them through Mathlib's star-algebra equivalence `LinearMap.toMatrixOrthonormal` on the actual Euclidean Hilbert space. It proves the operator is continuous, has exact order 3, has no positive smaller order, and lives in complex dimension 2. `dimension_bound_fails` combines these facts for the same operator and space.

This single counterexample decisively refutes the explicit dimension-upper-bound conjunct, so the full conjecture is false. The other spectral/unitary/decomposition conjuncts do not need to be addressed.

**Disposition: APPROVED.**
