# Conjecture 00000004294: disproof

C_2 and C_3 are abelian groups of prime-power order. Each has exactly the trivial and whole subgroups, giving isomorphic two-element subgroup lattices. Their unequal cardinalities exclude a group isomorphism.

## Scope

The prime varies over the stated class of prime-power-order groups. This does not refute a different assertion restricted to one fixed prime p. All proposition-valued subgroups are covered, and the lattice maps preserve meet and join.

The complete argument and the correspondence between the mathematical objects and Lean definitions are in [main.pdf](main.pdf) and [main.tex](main.tex). [SOURCE.md](SOURCE.md) reproduces both language versions and pins their source commit.

## Reproduce the formal verification

Use Lean **4.19.0**. The project imports only `Std`, has no Mathlib dependency, and treats warnings as errors.

```text
cd lean
lake build
cd ..
```

The final package was built in a new directory, and the accompanying scripts were rerun. `lean-verification.txt` records the build and printed axiom dependencies; `verification.json` records the exact file hashes. `auxiliary-results.json`, where present, records independent script output. Scripts write their own result files and do not overwrite the package verification record.

Rebuild the report with `tectonic main.tex`. The compiled PDF was rendered and visually checked. The proof-to-statement correspondence was also checked by a separate AI-assisted review.

## Submission

AI-assisted submission by **gaochengzhecpu**, prepared for independent maintainer review. Local verification is not organizer acceptance. This directory contains only materials for conjecture 00000004294.
