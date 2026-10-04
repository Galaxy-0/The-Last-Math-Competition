# Local verification record

This records author-side execution and independent internal scrutiny, not official maintainer acceptance.

## Mathematical coverage

Both contribution guides and the exact bilingual conjecture were checked at upstream `fe1d06d431b0591b65d759c60035b1d2e293a819`. Both source languages impose a pairwise spherical-distance bound of pi/2 and propose a closed hemisphere as the extremal set. The disproof refutes that necessary first clause.

- The ambient type is actual `EuclideanSpace ℝ (Fin 3)`, with its Euclidean inner product and norm. The sphere is `Metric.sphere 0 1` and sphere membership is proved equivalent to norm one.
- The distance is actual `InnerProductGeometry.angle`. The formal bridge reduces it to arccos of the inner product on unit vectors. It is the great-circle distance in the source, not the ambient chord metric.
- Every unit pole has a perpendicular unit vector constructed from an actual orthonormal basis of its orthogonal complement. The dimension hypothesis is proved from the actual three-dimensional ambient space.
- That vector and its negative lie in the closed hemisphere and have actual spherical distance pi. Thus the constraint fails for every orientation, not only a nominated coordinate hemisphere.
- The interior construction uses the actual vectors `(3/5)v+(4/5)w` and `(3/5)v-(4/5)w`. Their norms are one, their pole inner products are 3/5, and their mutual inner product is -7/25. Their actual angle exceeds pi/2. The root module supplies the perpendicular witness for every pole, discharging the conditional construction's hypotheses.
- `Admissible` quantifies over all pairs of points and requires the set to lie in the actual sphere. `IsAreaMaximizer` includes admissibility explicitly, as well as comparison with all admissible competitors. The no-maximizer result is proved for every objective measure and then specialized to actual two-dimensional Hausdorff measure.
- The Hausdorff measure uses Mathlib's diameter-cover normalization. No exact surface-area normalization formula is assumed or claimed; infeasibility is independent of every measure and hence of its normalization.
- `conjecture_false` is the unconditional negation of `ConjectureFirstClause`. Refuting the first clause refutes the full conjunction. The proof does not invent the unspecified second-extremizer definition, compute a correct optimum, or claim a result about every almost-everywhere modification of a hemisphere.

## Fresh independent execution

A separate verification agent copied only the five final Lean files and three configuration files to `/private/tmp/tlmc1561-independent`. No compiled submission outputs were copied. The pinned dependency cache was reused; this is not a source rebuild of all Mathlib dependencies.

| Check | Result |
|---|---|
| Lean compiler | 4.19.0, exact commit `6caaee842e9495688c1567e78c0e68dbb96942aa` |
| Mathlib | v4.19.0, exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| All nine dependency revisions | Exact manifest matches; tracked sources clean before and after |
| Fresh complete `lake build` | Exit 0 |
| Direct strict replay of all five Lean files | All exit 0, warnings treated as errors |
| Actual definition/abbreviation printouts | All 12 present |
| Actual type and transitive-axiom audits | All 21 named theorems present |
| Allowed axiom dependencies | Only `propext`, `Classical.choice`, `Quot.sound` |
| Proof-bypass scan | No raw or code matches |
| Source/config identity | All eight files identical and unchanged across both directories |

`verification/strict-replay.json` records exact commands, outputs, compiler identity, source hashes, dependency revisions and parsed audit results. `verification/build.txt` and `verification/axioms.txt` preserve the actual outputs. Every strict replay used `lake env lean -DwarningAsError=true`. All expected names are matched against actual emitted definitions, theorem types and axiom lists. The geometric identities and inequalities are proved in Lean; there is no auxiliary numerical program.

## Report and independent review

The exact final `main.tex` compiles successfully with the desktop editor compiler and Tectonic 0.17.0. Both pages of the exported PDF were rendered with Poppler and visually inspected in full. Page one contains the scope and complete antipodal proof; page two contains the complete interior proof, formal scope and primary reference. Text, equations and references are legible. No clipping, overlap, missing glyphs, blank page or orphan reference page was found. The TeX log contains no warnings or overfull/underfull boxes. Text extraction supplies a secondary content check.

`verification/pdf.json` records the exact source/PDF hashes and visual inspection scope; `verification/report.txt` preserves the TeX log with trailing whitespace removed. `SEMANTIC_REVIEW.md` records a separate agent's mathematical/source/report scrutiny and exact reviewed identities. That internal semantic review is distinct from the fresh compilation performed by the verification agent and the coordinating agent's PDF visual inspection.

## Eligibility and submission identity

`verification/eligibility.json` preserves the initial source/rule identity, unsolved metadata, all-state PR/comment and topic searches, and current/historical solution-path checks. Its snapshot covers 545 PRs through #549 and found no prior or competing submission for 00000001561. Both guides changed only their leaderboard sections relative to the earlier rule audit. No prior-error account applies to the checked records. The final live refresh is preserved separately in `verification/prepublication.json`.

Only the personal submission folder is changed. The package contains no dependency folders, compiled Lean artifacts or scratch probes. `verification/SHA256SUMS.json` covers every other submitted file; all hashes are checked against exact staged Git bytes before commit. These records establish checks at stated times, not guarantees against future repository changes.
