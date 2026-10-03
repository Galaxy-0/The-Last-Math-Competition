# Conjecture 00000000126: disproof

For every length n >= 3, the base-four repunit factors into two integers greater than one by splitting 2^n modulo 3. The remaining lengths give 0, 1, and 5. Consequently the complete set of prime values is {5}, refuting the assertion for every base.

## Scope

Length n is k+1 in the source. The proof covers every natural-number length, not merely a bounded computation. Infinitude of a set of natural-number prime values is expressed equivalently as unboundedness.

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

AI-assisted submission by **gaochengzhecpu**, prepared for independent maintainer review. Local verification is not organizer acceptance. This directory contains only materials for conjecture 00000000126.
