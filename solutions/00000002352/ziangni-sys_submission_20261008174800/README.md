# Disproof of 00000002352

The genuine free polynomial F(X)=X solves interpolation at distinct scalar
nodes 0 and 1/2 with targets 0 and 1/2. Its free Szego Pick matrix is the
2-by-2 all-ones matrix, which is singular. Thus strict positive definiteness
is not necessary for solvability in the standard norm-at-most-one Schur
class. The report explains the distinction from positive semidefiniteness
and from a uniformly strictly contractive multiplier class.

Files: `proof.tex`, compiled `proof.pdf`, and the pinned project `lean/`.

## Reproduction

Use Lean 4.19.0 (as pinned by `lean-toolchain`). In `lean/`, run
`lake update` if dependencies are absent, then `lake build`.
The public manifest and lakefile pin Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
Local validation used ignored junctions to this exact dependency cache.
Compile the report with `tectonic proof.tex`.

## Validation

One successful full final `lake build` completed on 2026-10-08 after
fixing a failed draft. Printed audits for analyticity, graded contractivity,
intertwining compatibility, the kernel series, interior nodes,
interpolation, and failure of `Matrix.PosDef` contain only
`propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, `native_decide`, custom axioms or unsafe declarations.
The report compiled with Tectonic; both rendered pages were inspected
once and have no clipping, overlap, or missing glyphs.

The Lean representation uses continuous complex-linear endomorphisms of
complex Euclidean spaces, hence the actual matrix operator norm at every
size. The Pick matrix is derived from the actual scalar restriction of
the free Szego kernel; it is not supplied as an assumed zero certificate.
