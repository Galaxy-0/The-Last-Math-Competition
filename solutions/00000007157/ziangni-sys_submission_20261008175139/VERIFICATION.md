# Validation

- Full `lake build` passed with Lean 4.19.0 and pinned Mathlib. Only optional tactic style suggestions were emitted.
- Six principal theorem axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
- No placeholders, native evaluation, custom axioms or unsafe declarations occur.
- Nonnormality is proved from conjugate-transpose products; the spectrum is obtained through actual matrix invertibility and determinant. The numerical-radius supremum is proved nonempty, bounded and strictly positive using the unit vector (3/5,4/5).
- The final theorem excludes every complex center and every unit-complex orientation, rather than assuming an origin-centered semicircle.
- The final two-page report compiled with Tectonic without layout warnings and both pages were rendered by Poppler and visually inspected. Native LaTeX compilation failed due to the platform standard-directory issue.
- Public dependency revisions are pinned; ignored local cache junctions are not submitted.
