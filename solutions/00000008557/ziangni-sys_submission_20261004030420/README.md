# Conjecture 00000008557: disproof

The three-element chain C3 has exactly two atoms in its congruence lattice, exceeding the real bound log_2(3). This refutes the atom-count upper-bound conjunct in both language versions. The subdirect-factor clause is not needed.

## Contents

- report.tex and report.pdf: complete proof, definitions, formal correspondence.
- statement.md: original bilingual source.
- lean/: Lean 4.19.0 project, Mathlib v4.19.0 pinned to commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
- verify.py: independent exhaustive test of all 512 binary relations and actual congruence atoms.
- verification/: actual build, theorem audit and auxiliary-check results.

## Reproduce

```text
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
cd ..
python verify.py
tectonic report.tex
```

Lean uses the actual Fin 3 lattice and full equivalence plus two-argument compatibility with minimum and maximum. It classifies all congruences, proves exactly alpha and beta satisfy the minimal non-bottom inclusion condition, and computes the actual atom set's cardinality. The concluding theorem negates the real-logarithm upper bound for this lattice. Every audited theorem depends only on standard logical axioms propext, Classical.choice and Quot.sound. No added axioms, incomplete proofs, or native decision shortcuts occur.

On Windows, use a short checkout path if dependency paths exceed the platform limit. Local ignored .lake/packages junctions were used to reuse the pinned shared cache; a fresh checkout fetches dependencies through its public manifest. Do not run lake clean on shared junctions. No build products or cache files are submitted.

This solution was constructed independently. C3 also appears in another solved conjecture about Boolean congruence lattices, but 00000008557's atom-count upper bound is a distinct unsolved claim.
