# Conjecture 00000004274: disproof

Every automorphism of C_7 is multiplication by one of its six nonzero residues, and these automorphisms commute. The center of Aut(C_7) therefore has order 6, which is not a product of powers of 2 with nonnegative integer exponents.

## Scope

Power-of-two exponents use the usual nonnegative-integer/cardinal counting interpretation; the source does not specify the exponent domain.

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

AI-assisted submission by **gaochengzhecpu**, prepared for independent maintainer review. Local verification is not organizer acceptance. This directory contains only materials for conjecture 00000004274.
