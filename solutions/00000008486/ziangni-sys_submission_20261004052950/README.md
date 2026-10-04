# Counterexample to conjecture 00000008486

The source explicitly uses the density exp(-f/t) but predicts the uniform measure on the maximum orbit. On the compact discrete system {0,1}, with the identity map and f(0)=0, f(1)=1, the maximum set is the fixed orbit {1}. Relative to counting measure, the normalized Gibbs family instead converges weakly to the distinct Dirac measure at 0.

`report.pdf` and `report.tex` give the complete argument and source correspondence. `lean/Main.lean` constructs actual probability measures, verifies the Gibbs point masses and normalization, and proves convergence in Mathlib's actual weak topology and failure of convergence to the maximum-orbit measure. This refutes the maximum-orbit clause; the other clauses need not be resolved.

## Reproduce

Use Lean 4.19.0. From `lean/`, run `lake update`, `lake exe cache get`, `lake build`, and `lake env lean Main.lean -DwarningAsError=true`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Build the report with `tectonic report.tex`.

See `VERIFICATION.md` for validation and exact scope.
