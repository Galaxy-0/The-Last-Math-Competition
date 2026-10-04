# Counterexample to 00000008476

For the compact two-point identity system and zero continuous potential, the source's actual pressure is identically zero and hence analytic at every real parameter. The two distinct Dirac measures are both invariant ergodic probability measures attaining that pressure at every parameter. This refutes the asserted equivalence between phase transitions (defined as nonanalytic points) and equilibrium nonuniqueness.

The entropy is not assumed. Every finite measurable partition is represented by a setoid on Fin 2; its quotient classes form genuine nonempty measurable disjoint atoms covering the space. The code defines their Shannon entropy, the common refinement of pulled-back partitions, its normalized entropy rate, and the supremum over all partitions. Identity dynamics leaves every nonempty-time refinement unchanged, so the actual rate tends to zero for every partition and the entropy supremum is zero.

The proof verifies actual measures, ergodicity, Bochner integrals, pressure supremum, and `AnalyticAt`. The source imposes no mixing/transitivity hypothesis; the report states this scope. No claim is made against theorems with additional assumptions.

## Reproduce

With Lean 4.19.0, run `lake update`, `lake exe cache get`, then `lake build` in `lean/`. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Public configuration uses Git dependencies; ignored local cache junctions are not submitted.

Compile `report.tex` using a LaTeX engine supporting its standard packages. Existing Tectonic generated the included PDF. See `VERIFICATION.md` for recorded checks.
