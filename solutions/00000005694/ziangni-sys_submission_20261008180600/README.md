# Disproof of 00000005694

The conjecture reverses the standard Frobenius-Schur indicator signs.
The trivial complex one-dimensional representation of C2 is irreducible
and admits the nondegenerate invariant symmetric form B(x,y)=xy.
Its actual trace character is1 and its normalized indicator sum is1,
contradicting the asserted orthogonal value-1.

Includes `proof.tex`, compiled `proof.pdf`, and `lean/`.
Use Lean4.19.0, pinned in `lean-toolchain`. In `lean/`, run `lake update`
if public dependencies are absent and then `lake build`.
The manifest/lakefile pin public Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
Local validation used ignored junctions to this exact cache.
Run `tectonic proof.tex` to reproduce the PDF.

Full final lake build passed2026-10-08. Final theorem
`orthogonal_sign_counterexample`, character computation, indicator
computation and irreducibility audits contain only propext,
Classical.choice and Quot.sound. No sorry, admit, native_decide,
custom axioms or unsafe declarations.
The final one-page PDF compiled and its rendered page was inspected
once: no missing glyphs, overlap or clipping.

Semantic coverage: actual Mathlib Representation.trivial, group
Multiplicative(ZMod2), LinearMap.trace character, finite normalized
Frobenius-Schur sum, complex-bilinear form, invariance, symmetry,
nondegeneracy and absence of proper nonzero subspaces. The first
false sign clause suffices to refute the conjunction. The report
identifies the standard representation-theoretic convention explicitly.
