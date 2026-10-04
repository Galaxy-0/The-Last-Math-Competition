# Disproof of conjecture 00000008873

Actual short combinatorial game values are countable, not continuum-sized. Finite descriptions encode arbitrary finite Left/Right option lists. Lean interprets them as actual Mathlib PGame objects, proves every interpretation short, and proves every actual Short PGame is represented up to legitimate relabeling. This gives a proved surjection onto the full subtype of short values in the actual Game quotient, hence a cardinal bound strictly below the continuum.

The representation theorem handles arbitrary finite move-index types and every successor. Countability of syntax alone is not used as a substitute for coverage of all short games. Infinite binary paths are outside the source's finite inductive class. The leaf-depth clause is not needed because the cardinality clause is false.

## Reproduction

Lean4.19.0 and the public Mathlib Git revision are pinned. From lean/:

    lake update
    lake exe cache get Mathlib/SetTheory/Game/Short.lean Mathlib/SetTheory/Cardinal/Continuum.lean Mathlib/Tactic/DeriveCountable.lean
    lake build
    lake env lean Main.lean -DwarningAsError=true

Compile report.tex with Tectonic. See VERIFICATION.md for observed checks. No auxiliary computation is required.
