# Counterexample to 00000008411

For every v >= 5, the complements of individual points form a simple 3-(v,v-1,v-3) design. Every point permutation is an automorphism, and any ordered triple of distinct points can be sent to any other. Different v give nonisomorphic designs. Thus there are infinitely many isomorphism classes with fixed t=3.

These are complete designs, often called trivial designs in classification terminology. The source's explicit incidence definition does not exclude them. The parameters satisfy 3 < k < v. This submission does not address a different claim restricted to noncomplete designs; only t is fixed in the original claim, so v, k and lambda may vary.

The Lean proof uses actual finite point sets, finite block families, incidence counts, block-preserving permutations, embeddings for ordered triples, and block-preserving point bijections for isomorphism. It proves that the actual quotient of this family by isomorphism is infinite. No parameter table or abstract transitivity assertion is assumed.

Files: `report.tex` and `report.pdf` contain the complete disproof; `lean/Main.lean` contains the formalization; `verification.txt` records checks.

Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned. From `lean/`:

```text
lake exe cache get
lake build
lake env lean Main.lean -DwarningAsError=true
```

The final theorem is `TransitiveDesigns8411.conjecture_00000008411`. Its dependencies use only standard logical axioms. Compile the report using `tectonic report.tex`. No auxiliary code is required.
