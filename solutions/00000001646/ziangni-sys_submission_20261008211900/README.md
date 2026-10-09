# Disproof of conjecture 00000001646

For every group G, genuine ordinary group cohomology with trivial rational coefficients satisfies H^0(G; Q) ≅ Q. Its dimension is one. Degree zero belongs to the asserted stable range for every genus g ≥ 1, so the dimensions for mapping class groups cannot tend to zero.

Lean constructs the actual degree-zero inhomogeneous differential, cocycle kernel, zero boundary image and cohomology quotient, then proves the linear equivalence and dimension. The nondecay theorem covers every group family and hence all mapping class groups. The report explicitly distinguishes ordinary rational cohomology in the conjectured formula from the introductory l²-Betti terminology.

## Reproduce

Run `lake build` in `lean/` using Lean 4.19.0. The public Mathlib dependency is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Local ignored cache junctions are not submitted.

The full build and final theorem axiom audits passed using only standard Lean axioms. The final PDF was compiled with Tectonic, rendered with Poppler and visually checked.
