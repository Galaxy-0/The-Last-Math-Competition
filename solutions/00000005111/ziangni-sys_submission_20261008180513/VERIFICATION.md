# Validation

- Full `lake build` passed with Lean4.19.0 and the pinned Mathlib dependency.
- Eleven principal printed audits use only `propext`, `Classical.choice`, and `Quot.sound`.
- No proof placeholders, native evaluation, custom axioms or unsafe declarations occur.
- Genuine complex matrix spectrum and canonical `NormedSpace.exp` are used. Nilpotency proves the defining series has finite support, allowing its exact sum to be evaluated.
- The lower error bound covers every vector in the actual one-dimensional complex Krylov subspace. The initial vector's Euclidean norm is1, the compression is0, and the Arnoldi output/error are proved exactly.
- The final theorem supplies an example exceeding every real finite bound while preserving the spectrum, dimensions and time.
- The final two-page Tectonic PDF compiled without layout warnings and both Poppler renders were visually checked. The native LaTeX compiler was unavailable due to the platform standard-directory issue.
- Public dependency revisions are pinned; local cache junctions are ignored and excluded.
