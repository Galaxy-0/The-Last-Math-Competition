# Conjecture 00000003461

Local-only counterexample to the prism minimality clause: the planar four-cycle has ordinary chromatic number 2 and DP-chromatic number 3.

Read `SOURCE.md` and `main.tex`. The Lean proof covers arbitrary DP covers, arbitrary lists of at least three colors, the exact twisted two-cover obstruction, and a square embedding certificate with arbitrary interior parameters.

Lean 4.19.0, no Mathlib. From `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. Actual validation results and hashes are in `RESULT.json`.
