# Verification record

On 2026-10-06, the root agent read the full source and independently ran
`lake build` on the completed project. It succeeds (3025 jobs), without
warnings. Lean 4.33.1 and the pinned Mathlib commit are used.

The printed audits of actual faces, face rank/dimension, connectedness,
purity, face counts, transformed polynomial, negative g-entry, and combined
`actual_counterexample` have only `[propext, Classical.choice, Quot.sound]`.
There are no unfinished proofs, native evaluations, or custom axioms.

The face counts come from actual clique faces of K_2. The transform uses
the actual empty-face count as well as vertex and edge counts, and the
g-vector's index type is exactly `Fin (complexRank / 2 + 1)`.
The only finite enumerations concern four faces, not a long search.

The LaTeX report is compiled by Tectonic and the desktop compiler, and
the exported PDF is rendered and visually checked before publication.
