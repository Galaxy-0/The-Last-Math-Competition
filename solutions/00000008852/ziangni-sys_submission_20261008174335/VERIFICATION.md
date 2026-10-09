# Validation

- Full `lake build` passed with Lean 4.19.0 and the pinned public Mathlib dependency. Only optional tactic style warnings were emitted.
- Seven principal theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`.
- No proof placeholders, native evaluation, custom axioms or unsafe declarations are used.
- The maximality proof quantifies over all monotone graph extensions. Actual continuous linear maps and operator norms are used; the optimality of the strong monotonicity constant is proved.
- The final statement negates the precise necessary-and-sufficient conjunct for individual perturbations. The report distinguishes this from a uniform sufficient guarantee.
- Tectonic produced the final two-page PDF without layout warnings. Both Poppler-rendered pages were visually inspected for intact formulas, readable typography and page flow. Native LaTeX compilation was unavailable due to a platform standard-directory error.
- Local cache junctions are ignored. The dependency manifest uses public Git repositories with exact revisions.
