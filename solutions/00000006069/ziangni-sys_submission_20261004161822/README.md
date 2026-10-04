# Disproof of conjecture 00000006069

For the three nontrivial first-order equations x₀=x₁, x₂=x₃, x₄=x₅, an actual most-general substitution maps even-indexed variables to their odd partners. All six variables occur. Every image is a variable, giving zero-/one-based depths0/1, both below half the variable count3. Even the changed-variable support has cardinality3, and one-based depth1 is below3/2.

The Lean proof defines actual inductive terms, recursive substitution application and occurrence sets, proves universal most-general factorization for every unifier on every term, and proves full idempotence. It targets only the explicit depth lower bound.

Run lake build in lean/ with Lean4.19.0. Public dependencies are pinned, including Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. The complete argument appears in report.tex/report.pdf and lean/Main.lean.
