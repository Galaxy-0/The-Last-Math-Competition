# Conjecture 00000006334: disproof

The 7 x 7 circulant matrix with first row (1,-1,-1,0,-1,0,0) has entries in {0,1,-1} and satisfies WW^T = 4I_7. This odd-order W(7,4) contradicts the source's explicit even-order requirement; it also satisfies 4 + 2 <= 7.

## Scope

Directly refutes the source's explicit assertion that the matrix order is even, using a fully verified W(7,4). This main disproof does not depend on an interpretation of the undefined existence window. The previous W(4,3) witness remains as a separate window-bound observation.

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

AI-assisted submission by **gaochengzhecpu**, prepared for independent maintainer review. Local verification is not organizer acceptance. This directory contains only materials for conjecture 00000006334.
