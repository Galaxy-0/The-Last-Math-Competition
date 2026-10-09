# Disproof of conjecture 00000003689

A fixed one-node self-loop dataflow graph on the complete lattice N infinity
has monotone successor transfer fixing top. Its actual bottom-start orbit
at round r is r, so no finite round stabilizes. Finite chain truncations
have actual orbit min(r,m) and first stable round m, ruling out every
uniform node/depth-only coefficient. The report distinguishes this from
valid height-dependent bounds for a fixed finite lattice.

Complete report: proof.tex, compiled proof.pdf. Lean project: lean/,
Lean 4.19.0, Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
Reproduce: cd lean; lake update; lake build. Report: tectonic proof.tex.

Validation: one successful final full lake build after draft rewrite fixes.
Eight printed audits use only propext/Classical.choice/Quot.sound, with the
quiver itself axiom-free. The one-page PDF compiled, was rendered and
visually inspected. Ignored local dependency junctions and build products
are excluded from the submission.
