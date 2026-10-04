# Conjecture 00000002610

Local-only proof package. The exact bilingual source is in `SOURCE.md`; the mathematical argument and scope are in `main.tex`.

Lean 4.19.0, no Mathlib. Run `lake build` and `lake env lean -DwarningAsError=true Main.lean` from `lean/`. The checked declarations print their axiom dependencies. Actual validation commands, results, and hashes are recorded in `RESULT.json`.
