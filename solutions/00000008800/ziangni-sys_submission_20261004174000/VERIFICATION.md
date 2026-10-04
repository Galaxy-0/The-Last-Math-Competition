# Verification

- Lean 4.19.0; Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
- Final full `lake build` passed 2331 targets without warnings after development simplification fixes.
- Ten printed axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
- No sorry, admit, native_decide, unsafe declarations, or custom axioms.
- Formal coverage: actual uniform two-point seed PMF, matrix diagonal sampling and trace, one-run expectation and variance, every finite product probability law, exact coordinate marginals, iIndepFun of seeds and estimator outputs, identical distributions, full all-positive-m expectation and variance formulas, genuine ratio convergence and negation of every eventual positive reciprocal-root lower bound.
- The final lower-bound theorem is stronger than merely disproving an exact finite-count formula: no c>0 eventually satisfies c/sqrt(m) ≤ Var(average_m). The standard-deviation rate is distinguished in the report.
- Built-in LaTeX compilation encountered the known platform-directory error. Existing Tectonic compiled the final PDF once; both pages were rendered and visually checked without clipping. PDF size: 42220 bytes.
