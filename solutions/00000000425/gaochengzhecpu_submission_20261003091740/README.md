# Conjecture 00000000425: disproof

The cubic MacMahon polynomial F2 has initial coefficients 1, 1, 3, contradicting scalar log-concavity. Across box sizes, the coefficient of q^28 in F2^2 - F1 F3 is -1, contradicting coefficientwise log-concavity. Both contradictions are derived from the actual MacMahon products in Lean.

## Scope

Diagonal specialization means equal box side lengths. The proof covers both numerical coefficient log-concavity for a fixed cubic box and coefficientwise log-concavity across successive cubic box sizes. Lean constructs the actual infinite quotients, proves their full numerator/denominator equations, and proves the finite-prefix correspondence needed for the negative coefficient.

The complete argument and the correspondence between the mathematical objects and Lean definitions are in [main.pdf](main.pdf) and [main.tex](main.tex). [SOURCE.md](SOURCE.md) reproduces both language versions and pins their source commit.

## Reproduce the formal verification

Use Lean **4.19.0**. The project imports only `Std`, has no Mathlib dependency, and treats warnings as errors.

```text
cd lean
lake build
cd ..
python verify.py
```

The final package was built in a new directory, and the accompanying scripts were rerun. `lean-verification.txt` records the build and printed axiom dependencies; `verification.json` records the exact file hashes. `auxiliary-results.json`, where present, records independent script output. Scripts write their own result files and do not overwrite the package verification record.

Rebuild the report with `tectonic main.tex`. The compiled PDF was rendered and visually checked. The proof-to-statement correspondence was also checked by a separate AI-assisted review.

## Submission

AI-assisted submission by **gaochengzhecpu**, prepared for independent maintainer review. Local verification is not organizer acceptance. This directory contains only materials for conjecture 00000000425.
