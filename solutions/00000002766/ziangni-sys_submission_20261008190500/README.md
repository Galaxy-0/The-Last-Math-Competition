# Disproof of 00000002766

The source allows rank bound r = 0. At every ambient matrix size,
rank at most zero forces the matrix to be zero. The nonzero polynomial
X has degree 1 and evaluates to zero on this entire actual variety,
contradicting the proposed minimum degree 2r+2 = 2.

Includes `proof.tex`, compiled `proof.pdf`, and the project `lean/`.
Use Lean 4.19.0, pinned by `lean-toolchain`. In `lean/`, run `lake update`
if dependencies are absent, then `lake build`. Public Mathlib is pinned
to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` by the lakefile and
manifest. Local validation used ignored junctions to that exact cache.
Compile the document using `tectonic proof.tex`.

One full final lake build passed on 2026-10-08. Printed audits for
the rank-zero equivalence, genuine matrix polynomial evaluation,
nonzero polynomial, degree and final false minimum-degree claim contain
only propext, Classical.choice and Quot.sound.
No sorry, admit, native_decide, custom axioms or unsafe declarations.
The final one-page PDF compiled and its rendered page was visually
inspected once, with no clipping, overlap or missing glyphs.

The proof uses Matrix.rank and its actual linear map range, and actual
Polynomial.eval₂ with the scalar-to-matrix algebra map. It covers
every square matrix size, rather than replacing the matrix variety by
a scalar example. The report explicitly limits the disproof to the
stated r = 0 scope and does not address a modified positive-rank claim.
