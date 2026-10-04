# Local verification record

This records author-side execution and independent internal scrutiny, not official maintainer acceptance.

## Mathematical coverage

Both contribution guides and the exact bilingual conjecture were checked at upstream `4cc82278ba1e5becc4d20b1e2a68dede094e2b8d`. The disproof attacks the explicit lattice-evenness criterion with the standard Gram-determinant convention. It formalizes no unstated theta modularity or character assertion.

- The A2 and diagonal constructions are actual real subspaces of `EuclideanSpace ℝ (Fin 3)`, with the inherited positive-definite inner products. Explicit linear equivalences from two-dimensional real coordinate space give genuine real bases.
- Each lattice is the integer span of its real basis. `Basis.restrictScalars ℤ` produces an actual integer basis. `DiscreteTopology` and `IsZLattice ℝ` are constructed, and both real and integer ranks are proved equal to two.
- A2 integrality and evenness quantify over every actual lattice vector, using its integer basis coordinates and an integer pairing proved equal to the inherited Euclidean inner product. Its actual real and integer Gram matrices have determinant 3.
- The diagonal lattice has integral inner products for every pair of lattice vectors and actual Gram determinant 2. Its first integer basis vector has squared length 1, disproving evenness.
- `IntegerEven` uses an integer witness, not the vacuous real-number `Even` predicate. The universal necessity and sufficiency assertions range over genuine Euclidean inner-product spaces with finite real bases and integral integer spans. Finite real bases automatically yield discrete full lattices.
- `determinant_not_necessary`, `determinant_not_sufficient`, and `both_directions_fail` refute the two implications. `conjecture_false` negates their characterization. The final negations have no unproved witness hypotheses.

## Fresh independent execution

A separate verification agent copied only the five final Lean files and three configuration files to `/private/tmp/tlmc9028-independent`. No compiled submission outputs were copied. The existing cache of pinned dependencies was reused; this is not a rebuild of all Mathlib dependencies from source.

| Check | Result |
|---|---|
| Lean compiler | 4.19.0, exact commit `6caaee842e9495688c1567e78c0e68dbb96942aa` |
| Mathlib | v4.19.0, exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| All nine dependency revisions | Exact manifest matches; tracked sources clean before and after |
| Fresh complete `lake build` | Exit 0 |
| Direct strict replay of all five Lean files | All exit 0, warnings treated as errors |
| Actual definition/instance printouts | All 28 present |
| Actual type and transitive-axiom audits | All 47 present: 43 theorems and four instances |
| Allowed axiom dependencies | Only `propext`, `Classical.choice`, `Quot.sound` |
| Proof-bypass scan | No raw or code matches |
| Source/config identity | All eight files identical and unchanged across both directories |

`verification/strict-replay.json` records exact commands, outputs, compiler identity, source hashes, dependency revisions and parsed audit results. `verification/build.txt` and `verification/axioms.txt` preserve the actual outputs. Every strict replay used `lake env lean -DwarningAsError=true`. All expected names are matched against actual declaration-type, definition and axiom output. No numerical auxiliary computation is needed: the lattice identities and determinant arithmetic are kernel-checked in Lean.

## Report and independent review

The exact final `main.tex` compiles successfully with the desktop editor compiler and Tectonic 0.17.0. The exported PDF has two substantive pages; both were rendered with Poppler and visually inspected in full. The entire A2 proof fits on page one; the diagonal proof, formal scope and references fit on page two. No clipping, overlap, missing glyphs, blank pages or orphan reference page was found. The TeX log contains no warnings or overfull/underfull boxes. Text extraction additionally checks key contents after Unicode ligature normalization.

`verification/pdf.json` records exact source/PDF hashes and the visual inspection scope; `verification/report.txt` preserves the TeX log with trailing whitespace removed. `SEMANTIC_REVIEW.md` records a separate agent's full mathematical/source/report scrutiny and the exact reviewed identities. That review is internal and is distinct from the compilation performed by the separate verification agent and from the coordinating agent's PDF visual inspection.

## Eligibility and submission identity

`verification/eligibility.json` preserves the initial upstream source/rule identity, unsolved metadata, all-state PR and comment searches, topic-match classification, and current/historical solution path checks. It found no prior or competing submission for 00000009028. The initial all-state scan covers 528 PRs through #532; 46 broad topic matches were unrelated. No prior-error account is applicable to the checked records. The final live refresh is preserved separately in `verification/prepublication.json`.

Only the personal submission directory is changed. The package contains no dependency folders, compiled Lean artifacts, or scratch probes. `verification/SHA256SUMS.json` covers every other submitted file; its hashes are checked against the exact staged Git bytes before commit. Timestamps are evidence of checks performed, not guarantees against subsequent repository changes.
