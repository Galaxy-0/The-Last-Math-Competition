# Conjecture 00000003483: disproof

The Hajos join of two K_4 graphs has seven vertices, eleven edges, and is four-critical, so 3e = 5v - 2. Deleting adjacent vertices 0 and 2 leaves a triangle and chromatic number 3, not 2. Thus equality does not imply double-criticality.

## Scope

Double-critical uses its standard definition: deleting the endpoints of every edge lowers chromatic number by two. Neither language of this source gives a conflicting definition. The necessary double-critical clause already fails, regardless of the undefined nearly-four-regular condition.

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

AI-assisted submission by **gaochengzhecpu**, prepared for independent maintainer review. Local verification is not organizer acceptance. This directory contains only materials for conjecture 00000003483.
