# Conjecture 00000007292: disproof

The five partitions of 4 have ranks 3, 1, 0, -1, -3 and cranks 4, 0, 2, -2, -4. Thus the frequency of value 4 is zero for rank and one for crank, refuting equidistribution.

## Scope

Uses Dyson rank and the standard Andrews-Garvan crank on actual integer partitions. No modulus is specified by the source. The example at n=4 avoids the exceptional n=1 crank convention; all partitions of 4 are formally classified.

The complete argument and the correspondence between the mathematical objects and Lean definitions are in [main.pdf](main.pdf) and [main.tex](main.tex). [SOURCE.md](SOURCE.md) reproduces both language versions and pins their source commit.

## Reproduce the formal verification

Use Lean **4.19.0**. The project imports only `Std`, has no Mathlib dependency, and treats warnings as errors.

```text
cd lean
lake build
cd ..
node verify.cjs
```

The final package was built in a new directory, and the accompanying scripts were rerun. `lean-verification.txt` records the build and printed axiom dependencies; `verification.json` records the exact file hashes. `auxiliary-results.json`, where present, records independent script output. Scripts write their own result files and do not overwrite the package verification record.

Rebuild the report with `tectonic main.tex`. The compiled PDF was rendered and visually checked. The proof-to-statement correspondence was also checked by a separate AI-assisted review.

## Submission

AI-assisted submission by **gaochengzhecpu**, prepared for independent maintainer review. Local verification is not organizer acceptance. This directory contains only materials for conjecture 00000007292.
