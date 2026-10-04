# Validation

The final full lake build succeeds (2225 targets). Ten printed axiom audits cover real analyticity, actual gradient, stationarity, nonlocal minimality, the flow's initial value, actual derivatives at every forward time, its actual limit, basin interval inclusion, actual Lebesgue measure and the combined counterexample. Only standard propext/Classical.choice/Quot.sound occur; no sorryAx or added axioms.

The basin definition requires an actual differentiable gradient trajectory for all nonnegative real times and its limit at infinity. Explicit trajectories represent every positive start. Actual Lebesgue measure monotonicity and the interval-measure formula prove measure at least1 without assuming the basin is measurable.

Tectonic compiled the two-page report.pdf (35,602 bytes) without box warnings. Both rendered pages were visually inspected without clipping or overlap. The built-in editor/compiler was attempted and encountered its platform-directory error; existing Tectonic supplied the PDF.

Public Lean4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b dependencies are pinned. No shared cache extension was needed. Text is UTF-8 LF and the scoped diff check passes. Scope is explicitly continuous gradient flow and the source's stationary-nonminimum definition; smoothing/Morse-index clauses are unused.
