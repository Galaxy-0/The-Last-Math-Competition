# Validation

The final full lake build succeeds (2262 targets). Eleven printed axiom audits cover maximality, unique actual resolvent, all iterates, actual conditional-expectation martingale differences, adapted trajectories, stochastic updates, pointwise and expected square summability, actual expected trajectory, empty convergence event, failed almost-sure convergence and the combined counterexample. Only standard propext/Classical.choice/Quot.sound occur; no sorryAx or added axioms.

Tectonic compiled the two-page report.pdf (38,611 bytes) without box warnings. Both rendered pages were visually inspected without clipping or overlap. The built-in editor/compiler was attempted and encountered its platform-directory error; existing Tectonic supplied the PDF.

Public Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b dependencies are pinned. The coordinated targeted Filtration cache extension succeeded and was released without changing versions. Text is UTF-8 LF and the scoped diff check passes. The source's final unqualified convergence clause is refuted; missing zero existence is explicit and the expected-rate clause is unused.
