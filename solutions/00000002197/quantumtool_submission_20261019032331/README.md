# Disproof candidate for conjecture 00000002197

**Submitter: [quantumtool](https://github.com/quantumtool).** AI-assisted mathematical work and formalization.

This submission gives two distinct inclusion-maximal antichains in the partition lattice of a four-element set. The interpretation boundary matters: the conjecture says “maximal antichain” without defining whether “maximal” means inclusion-maximal or maximum-cardinality. The supplied disproof uses the standard order-theoretic meaning, inclusion-maximal. It does not claim to settle a reformulation about uniqueness of a maximum-cardinality antichain.

The proof and its scope are in `main.tex` and `main.pdf`.

## Reproduce

```sh
cd lean4
lake build
lake env lean Check.lean
```

The project uses Lean 4.33.1 and only Lean's `Std` library. `Check.lean` reports the axiom dependencies of the main theorems. There are no `sorry`, `native_decide`, or custom axioms.

## Files

- `main.tex`: proof, definitions, and interpretation boundary.
- `main.pdf`: compiled report.
- `lean4/`: self-contained Lean project.
- `verification.txt`: commands, compiler output, and source hash.
