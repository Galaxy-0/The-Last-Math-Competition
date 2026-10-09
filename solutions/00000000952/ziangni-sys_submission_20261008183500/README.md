# Disproof of 00000000952

Four tetrahedral vectors with coordinates ±1/2 form a redundant
Parseval equiangular tight frame in real dimension3. Deleting one
vector produces an actual frame-operator defect with eigenvalue3/4,
hence operatornorm at least3/4, exceeding k/n=1/3.
The report also explains why the same relative deviation survives
unit-norm tight normalization.

Includes `proof.tex`, compiled `proof.pdf`, and the pinned project `lean/`.
Use Lean4.19.0. In `lean/`, run `lake update` if dependencies are absent,
then `lake build`. Public Mathlib is pinned by lakefile and manifest to
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
Local validation used ignored junctions to this exact shared cache.
Run `tectonic proof.tex` to reproduce the PDF.

One full final lake build passed2026-10-08 after fixing a failed draft.
Printed audits for dimension, all innerproducts, tight operator identity,
erased eigenvector and final false erasure bound contain only
propext, Classical.choice and Quot.sound.
No sorry, admit, native_decide, custom axioms or unsafe declarations.
Final two-page PDF compiled and both rendered pages were visually
inspected once, without clipping, overlap or missing glyphs.

Actual vectors live in EuclideanSpaceℝ(Fin3); each rankone map is a
continuouslinear operator constructed from the genuine innerproduct.
The defect is the difference between the actual four-vector fullframe
operator and the three-vector remainingframe operator. The final proof
uses its actual operatornorm, rather than an assumed scalar deviation.
