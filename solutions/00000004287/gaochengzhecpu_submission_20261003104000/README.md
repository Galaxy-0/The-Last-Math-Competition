# Conjecture 00000004287: disproof

For a normal subgroup H, G/H is torsion-free exactly when x^n in H with n > 0 implies x in H. This property survives every nonempty directed union. Therefore no chain of any length has the claimed failure of purity.

## Scope

Uses exactly the source's definition of purity as a torsion-free quotient. The proof constructs the actual coset quotient and works for arbitrary groups and normal subgroups, including all subgroups in the abelian setting.

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

AI-assisted submission by **gaochengzhecpu**, prepared for independent maintainer review. Local verification is not organizer acceptance. This directory contains only materials for conjecture 00000004287.
