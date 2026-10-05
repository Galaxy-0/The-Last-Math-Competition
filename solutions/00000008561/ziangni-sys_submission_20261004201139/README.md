# Counterexample to 00000008561

On the genuine Euclidean Hilbert space C², the diagonalizable nonnormal operator T = [[1,3],[0,-1]] has norm between 3 and 4. Every actual eigenbasis condition number is at least 3, including the infimum over all rescalings. At epsilon = 10 its actual resolvent pseudospectrum lies in the radius-14 disk, so its complex Lebesgue area is at most 196 pi, strictly less than the asserted lower bound of at least 900 pi.

The report targets the universal area inequality in both language versions. It uses a diagonalizable operator with a finite eigenbasis condition number and the ordinary Euclidean operator norm. No small-epsilon restriction appears in the source. The separate Jordan, connectivity and direct-sum clauses are not needed.

Lean constructs actual continuous linear maps, verifies the adjoint obstruction and an explicit diagonalizer with two-sided inverse, bounds all eigenbasis condition numbers and their real infimum, and proves the disk inclusion using Mathlib's spectrum/resolvent. The final area is the actual complex Lebesgue measure, with finiteness proved before its real-valued interpretation. Adjoining the spectrum only enlarges the source's resolvent-defined set; the stronger upper bound therefore applies to both conventions.

## Reproduce

Use Lean 4.19.0. In `lean/`, run `lake update`, `lake exe cache get`, then `lake build`. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Public dependency configurations are included; local build files and dependency junctions are ignored.

Compile `report.tex` with standard LaTeX packages. The included one-page PDF was produced by Tectonic. See `VERIFICATION.md` for the build, axiom and PDF checks.
