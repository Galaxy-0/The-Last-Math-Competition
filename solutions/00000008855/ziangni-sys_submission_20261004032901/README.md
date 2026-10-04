# Disproof of conjecture 00000008855

The scalar nonzero-count sparsity penalty has unique proximal value 2 at input 2, and unique proximal value 0 at input 1 (unit proximal parameter). No fixed nonnegative soft threshold can give both.

Lean defines the actual penalty and objective and proves global minimizer characterizations by comparing all real competitors. It does not assume a hard-thresholding formula.

## Reproduction

Lean 4.19.0, pinned Mathlib:

    cd lean
    lake update
    lake exe cache get Mathlib/Data/Real/Basic.lean Mathlib/Tactic/Linarith.lean Mathlib/Tactic/NormNum.lean
    lake build
    lake env lean Main.lean

Compile report.tex with Tectonic. See VERIFICATION.md.
