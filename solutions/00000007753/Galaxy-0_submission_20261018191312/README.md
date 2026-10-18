# Disproof of TLMC 00000007753

The exceptional-parameter bound fails at n = 1. The two rational (indeed integer) parameters c = -2 and c = -6 give

- X² - X - 2 = (X - 2)(X + 1)
- X² - X - 6 = (X - 3)(X + 2)

Thus at least two parameters make the original dynatomic polynomial reducible, exceeding 2^(1-1) = 1. No claim about the separate special-value Galois-group clause is needed.

## Contents

- `solution.tex`, `solution.pdf`: full proof and formalization correspondence
- `lean/Main.lean`: rational polynomial operations, general evaluation lemmas, nonunit proofs, factorizations and cardinality-bound contradiction
- `lean/Audit.lean`: dependency audit of the main theorems
- `lean/lakefile.toml`, `lean/lean-toolchain`: standalone Lean 4.31.0 project
- `verify.py`: optional independent exact-rational coefficient check
- `build-pdf.sh`: LaTeX build helper

## Verification

With Lean 4.31.0 available:

    cd lean
    lake build
    lake env lean Audit.lean
    lake env leanchecker Main

The last command independently kernel-checks the compiled module. The audit reports only `propext`, `Classical.choice` and `Quot.sound`; no custom axioms, proof holes or native decision procedures are used. `decide +kernel` performs kernel reduction.

From the submission root:

    python3 verify.py
    ./build-pdf.sh

A normal TeX Live installation is sufficient for the PDF. No network dependencies are required for Lean.
