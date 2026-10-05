# Validation

Final full lake build succeeds (2131 targets). Thirteen printed axiom audits cover actual Euclidean gradient, smoothness, actual Hessian derivative, stationarity, nondegeneracy, negative and positive curvature, strict-saddle local-extremum exclusions, every finite iterate, nonstationary starts, all-time ball nonescape, actual limit and every-radius counterexample. Only standard propext, Classical.choice and Quot.sound occur; no admitted statements or added axioms.

Existing Tectonic compiled the two-page report.pdf (35743 bytes) without box warnings. Both rendered pages were visually checked and are clean. Built-in editor/compiler was attempted and encountered its platform-directory error. The global Lipschitz observation in the report follows from the explicit Hessian and is supplementary; the formal safe-step inequalities are numerical.

Public Lean4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b pins are unchanged. No shared cache extension was needed. UTF-8 LF text and scoped diff check pass. Scope is unqualified ordinary deterministic gradient escape from a saddle neighborhood, not perturbed, randomized or generic-start guarantees. Nonstationary starts are arbitrarily close to the saddle.
