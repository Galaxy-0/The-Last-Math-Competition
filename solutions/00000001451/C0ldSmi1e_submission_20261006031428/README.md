# Conjecture 00000001451: disproof of the printed rate

Both official language versions give the positive exponent `ε^((d−1)/2)`. In dimension two, no natural number can stay between fixed positive multiples of `√ε` for every sufficiently small positive error. The submission refutes literal equality, a positive leading asymptotic constant, and the weaker positive two-sided order claim.

The formalization uses Euclidean convex polytopes, actual exposed codimension-one facets, symmetric-difference Lebesgue volume, bijective finite counts, and attained minima. Finiteness of all polytope facets and equivalence between existence of an approximant and an attained minimum are proved. The argument is symbolic and covers arbitrary positive errors; it does not rely on numerical sampling.

The constant is finite, positive, and independent of the error, as usual for a leading or optimal-order constant. The sign-corrected negative-exponent problem and a bare one-sided upper bound are outside the result.

## Contents

- `ORIGINAL.md`: unchanged bilingual conjecture.
- `report.tex` and `report.pdf`: matching three-page mathematical report.
- `lean/`: complete Lean 4.19.0 / Mathlib v4.19.0 project and compiled-declaration auditor.
- `verify.py`: portable fresh-build and integrity checker using Python's standard library.
- `test_verify.py`: seven rejection controls and one acceptance control for the inventory validator.
- `VERIFICATION.md` and `verification/`: verification scope, exact input identities, complete recorded command outputs, and independent pre-submission reviews.

## Reproduce

Install the pinned Lean toolchain with Elan, then from this submission directory:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean
cd ..
python3 -B -m unittest -v test_verify.py
python3 -B verify.py
```

Use the supplied `lake-manifest.json` to preserve all nine dependency revisions. The verifier requires the dependencies downloaded by the cache command. It creates a new temporary project, copies only the seven frozen source/configuration files, and reuses only the checked standard dependency directories. It accepts `--lake /absolute/path/to/lake` and `--output /new/output/directory` if desired. Keep the pinned toolchain on `PATH` when selecting an executable directly.

The final theorems, in namespace `TLMC1451`, are `conjecture_exact_false`, `conjecture_asymptotic_false`, and `conjecture_order_false`. Their supporting dimension-two theorems are in `Solution.lean`. `Audit.lean` enumerates every declaration originating in the three mathematical modules, including generated/private declarations, and rejects added axioms or unsafe declarations.

Local verification and independent pre-submission review are recorded here. Maintainer acceptance is not asserted.
