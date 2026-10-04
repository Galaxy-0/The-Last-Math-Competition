# Counterexample to 00000008430

The full Grassmannian Gr(1,3), equivalently chains 0 < L < F_q^3 of dimensions0,1,3, has counting polynomial q²+q+1. It is the full Schubert variety, not a single affine Schubert cell. Its polynomial is monic but has the nonreal root(-1+i√3)/2, refuting the source's integer-root assertion.

The formalization counts actual one-dimensional Submodules of `Fin 3 → k` for every finite field k, using Mathlib's proved projectivization equivalence and cardinality theorem. It additionally proves that the counting polynomial is unique by evaluating on infinitely many actual prime fields. Monicity, the exact complex root equation, and exclusion from every integer cast are all kernel-verified.

- `report.tex` / `report.pdf`: full proof and source correspondence.
- `lean/Main.lean`: actual objects and proofs.
- `verification.txt`: validation evidence.

Lean4.19.0; Mathlib pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From `lean/`:

```text
lake exe cache get
lake build
lake env lean Main.lean
```

The final theorem is `SchubertCount8430.conjecture_00000008430`. The independently audited `count_lines`, `counting_polynomial_unique`, and `countPolynomial_monic` provide the general count, uniqueness and leading coefficient. All audited proofs use only standard logical axioms. No auxiliary code is required. Compile the report with `tectonic report.tex`.
