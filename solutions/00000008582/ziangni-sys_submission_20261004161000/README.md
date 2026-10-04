# Counterexample to 00000008582

On the actual complex Hilbert space H = l²(N; C²), let T act on coordinate block n by multiplication by i·2^(-n). This is a compact, nonselfadjoint operator with infinitely many distinct nonzero eigenvalues, each admitting two independent eigenvectors. Thus the source's finite-exception clause fails. The example is normal, which is allowed; it does not challenge a separate assertion of generic simplicity.

The proof constructs T as a summable series in the Banach space of continuous linear operators. Each block projection factors through C² and is compact; compactness survives the operator-norm limit. Actual coordinate embeddings give independent eigenvector pairs, and the selfadjoint inner-product identity fails at the first coordinate vector.

`MultipleEigenvalue` explicitly means that there exist two linearly independent eigenvectors with that eigenvalue. This implies geometric multiplicity at least two, and hence algebraic multiplicity at least two, since ordinary eigenvectors belong to the generalized eigenspace. The proof does not assume spectral data or classify the whole spectrum.

## Reproduce

Use Lean 4.19.0. In `lean/`, run `lake update`, `lake exe cache get`, and `lake build`. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Public dependencies use Git; ignored local cache junctions are not part of the submission.

Compile `report.tex` using a LaTeX engine supporting its standard packages. The included PDF was generated with Tectonic. Recorded verification is in `VERIFICATION.md`.
