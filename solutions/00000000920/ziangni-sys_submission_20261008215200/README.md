# Disproof of conjecture 00000000920

The actual homogeneous C*-algebra C = C({point}, M1(C)), an AH algebra via its constant identity system, has real rank zero: self-adjoint scalars are approximable by self-adjoint invertibles. Its projections are only zero and one, each at norm distance 1/2 from the self-adjoint scalar 1/2. Thus its projection semilattice is not norm dense.

Lean constructs the point function algebra and equivalence, records the constant-system universal property, proves the genuine star/invertible approximation, classifies projections and computes the exact norm gap. The report explains the literal projection semilattice/semigroup interpretation, including finite additive sums, and distinguishes the valid finite-spectrum or real-linear-combination criterion.

## Reproduce

Run `lake build` in `lean/` with Lean 4.19.0. Public Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Ignored local cache junctions are not submitted.

One full build passed, with seven standard-only final theorem axiom audits. The final PDF was compiled with Tectonic, rendered with Poppler and visually checked.
