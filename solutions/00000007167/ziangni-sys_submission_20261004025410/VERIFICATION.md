# Verification evidence

Date: 2026-10-04. Lean 4.19.0; Mathlib pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b.

## Actual mathematical objects

The witness is Mathlib's bounded complex-linear identity on the complex Hilbert line. Its operator norm is Mathlib's standard continuous-linear-map norm. Numerical radius is defined as the real supremum of norms of actual complex inner products over all unit complex vectors. The entire value set is proved equal to the singleton {1}, with both containment and the unit-vector witness checked. Thus the computed ratio is 1, not an asserted datum.

The final theorem refutes the exact claimed universal upper bound 1/2 for positive-norm bounded operators. A universal equivalence bound must apply on this Hilbert space. The second source conjunct concerning rotations is not needed.

## Formal checks

- Fresh project lake build passed.
- Direct lake env lean Main.lean passed.
- Axiom audits for operator norm, entire value-set equality, numerical radius and final negation list only propext, Classical.choice, Quot.sound.
- No sorry, admit, native_decide or added axioms appear.
- Pinned dependency revisions are public Git commits; ignored local cache junctions and build outputs are not submitted.

## Report checks

- Built-in source editor opened. Native compiler returned the known standard-platform-directory lookup error.
- Tectonic compiled report.pdf successfully without overfull boxes or unresolved references.
- Poppler confirmed a one-page A4 PDF.
- Entire final page rendered and visually inspected; no clipping, overlap or missing glyphs.
- No auxiliary computational verification is required.
- git diff --check passed; only the personal submission directory is committed.
