# Independent internal semantic review — conjecture 00000001561

**Verdict: PASS for the exact necessary first clause in both source languages. No mathematical or formal-semantic correction is required in the reviewed files.** This is an internal author-side review, not an official competition review or maintainer acceptance.

## Scope and source interpretation

I read every line of the five frozen Lean files, all three project configuration files, the complete final LaTeX report, README and VERIFICATION document, the exact bilingual conjecture, and both complete contribution guides. I also inspected the actual fresh-build output, emitted definition/type/axiom output and associated execution records. The mathematical argument was assessed independently of the fact that Lean compilation succeeded.

The English statement specifies subsets of the unit sphere whose pairwise spherical distances are at most pi/2 and identifies a closed hemisphere as an extremizer. The Chinese statement imposes the same pairwise bound and identifies the same closed hemisphere. A maximizer of a constrained problem must belong to the feasible class. Thus exhibiting a violating pair in every closed hemisphere disproves a necessary clause of the full conjecture. There is no need to define the source's second-extremizer terminology, classify the true optimum, or calculate the proposed area ratio. The final theorem is explicitly named and documented as the negation of this first clause, rather than a formalization of an invented second clause.

The ordinary spherical conventions are supported by B. Klartag's author-hosted [*Isoperimetric inequalities in high-dimensional convex sets*, Lecture 1, Section 1.3, pp. 9–10](https://www.weizmann.ac.il/math/klartag/sites/math.klartag/files/uploads/lecture1.pdf), read during the semantic assessment: distance on the unit sphere is arccos of the Euclidean inner product, and hemispheres are intersections with central halfspaces. This reference supports the definitions; the elementary contradiction does not depend on an external extremal theorem.

## Actual geometric objects and quantifiers

1. **Ambient geometry and distance.** `Space` is actual `EuclideanSpace ℝ (Fin 3)`, carrying the Euclidean inner product and norm. It is not a coordinate function space with a sup norm. `sphereS2` is actual `Metric.sphere 0 1`, and `sphereS2_mem_iff` proves the norm-one characterization. `sphericalDistance` is Mathlib's actual `InnerProductGeometry.angle`, whose implementation is arccos of the inner product divided by the product of norms. The proved unit-vector bridge gives exactly arccos of the inner product. No Euclidean chord distance is substituted for the spherical distance, and zero-vector conventions cannot affect the sphere arguments.

2. **All hemisphere orientations.** A hemisphere is the actual intersection of this sphere with the halfspace `0 ≤ inner v x`, where the pole is quantified over the entire sphere. For every such pole, `exists_unit_orthogonal` proves the pole is nonzero, establishes the actual ambient finrank equation `3 = 2 + 1`, and takes a vector from `OrthonormalBasis.fromOrthogonalSpanSingleton`. I inspected that Mathlib API: its codomain is the orthogonal complement of the span of the pole, with its inherited norm. The basis vector is therefore an actual unit vector in the actual orthogonal complement. Orthogonality is constructed, not left as an unproved hypothesis.

3. **Closed-hemisphere violation.** The vector and its negative both satisfy sphere membership and the closed-halfspace condition. `angle_self_neg_of_nonzero` proves their actual spherical distance is pi. The proof uses the strict inequality pi/2 < pi and contradicts the all-pairs condition in `Admissible`. This covers every orientation, not just a coordinate example or a finite sample. Both witness points are genuine points of the source's set.

4. **Interior strengthening.** The frozen interior vectors are `(3/5)v + (4/5)w` and `(3/5)v - (4/5)w`. Lean proves both norms are one, both pole inner products are 3/5, and their mutual inner product is -7/25. The actual angle consequently exceeds pi/2. The root module supplies the perpendicular unit vector for every pole, so its final open-hemisphere result has no undisclosed orthogonality or existence assumption. This shows that deleting the equator does not repair the proposed extremizer. It does not assert anything about every almost-everywhere modification; the report correctly disclaims that stronger statement.

5. **Optimization and measure.** `Admissible A` requires both `A ⊆ sphereS2` and the exact bound for every pair of points of A. `IsAreaMaximizer μ A` explicitly includes `Admissible A`, followed by comparison with all admissible competitors. `no_hemisphere_extremizer` is universal over actual `Measure Space` values and negates the existence of any unit pole whose closed hemisphere is such a maximizer. The final `conjecture_false` specializes this to actual `Measure.hausdorffMeasure 2`; this is not an assigned numerical area or a proxy formula.

6. **Normalization and measurable-domain scope.** Mathlib's Hausdorff measure is constructed from powers of covering diameters; I inspected its definition and normalization documentation. The report accurately declines to claim an exact normalization identity with a separately defined surface-area measure. That bridge is unnecessary: the contradiction proves infeasibility before using any value of the measure. The same obstruction applies if the optimization domain is restricted to measurable feasible sets or a different surface-area convention is chosen. Although the formal comparison predicate is written for all sets, the proof does not infer infeasibility from that enlarged comparison class; it directly violates the source's pairwise constraint.

## Report correspondence and trust evidence

The complete report, README and VERIFICATION document match the source. The report's antipodal and rational interior calculations are all covered by Lean theorems. It does not claim to determine the true optimal area or to establish the second clause separately. There are no auxiliary numerical computations on which the proof depends.

The separate verification agent performed a fresh project build in `/private/tmp/tlmc1561-independent` after copying only the five Lean files and three configurations. I inspected that execution's records rather than rerunning compilation. The recorded compiler is Lean 4.19.0, exact commit `6caaee842e9495688c1567e78c0e68dbb96942aa`; Mathlib is pinned at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine dependency revisions and clean tracked source states were checked before and after. This execution reused a pinned dependency cache and did not rebuild all dependencies from source.

The fresh complete build and all five direct replays with warnings treated as errors exited successfully. I independently reparsed the actual `axioms.txt` output against `Check.lean`: all 12 definition/abbreviation printouts, all 21 theorem types, and all 21 transitive-axiom lists match exactly. Their axiom union is only `propext`, `Classical.choice`, and `Quot.sound`. I also verified that the output equals the emitted Check replay recorded in the JSON. The recorded bypass scan has no raw or code matches; source inspection found no admitted theorem, custom axiom, native decision proof or bypass mechanism. I independently recomputed all eight proof/config hashes and checked equality with both the fresh-copy bytes and the recorded identities.

I read the final TeX source in full and checked its hash and the PDF hash against `pdf.json`; I also inspected the preserved TeX log, which has no warning or overfull/underfull box entry. The coordinating agent, not this reviewer, performed native/Tectonic compilation and visual inspection of both rendered PDF pages. The PDF record reports two pages and successful rendering/inspection. This semantic review does not misattribute that visual inspection or the separate agent's compilation to its author.

## Rules and eligibility scope

Both complete guides require a faithful, complete disproof, LaTeX/PDF/Lean materials, no duplicate solved submission, and changes confined to the personal submission folder. The reviewed artifact set and evidence address the mathematical and execution requirements. The source statements and both complete guides match the final recorded upstream revision `fe1d06d431b0591b65d759c60035b1d2e293a819` byte for byte. Relative to the earlier reviewed revision, only guide leaderboard content changed; contribution and review rules are unchanged.

I inspected the frozen final `prepublication.json`: its snapshot completes at 2026-10-04 18:36:07 UTC, retains unsolved metadata, covers 545 all-state PRs through #549, and records no candidate ID/topic/comment match or current/historical solution path. No previous-submission error account is indicated by that evidence. These are time-bounded, search-scoped findings; they do not establish the absence of inaccessible or future submissions. Final staged-file scope, publication and maintainer acceptance remain separate from this source review. No official review folder, metadata or leaderboard change is authorized or implied by this document.

## Exact reviewed identities

SHA-256 values below were computed from the reviewed bytes after the execution and eligibility records were finalized. Proof paths are relative to `/private/tmp/tlmc1561-proof` (packaged under `lean/`). Report/document paths are relative to `/private/tmp/tlmc1561-package`. Eligibility and verification records come from the correspondingly named `/private/tmp/tlmc1561-*` directories. The exact bilingual source also matches the managed worktree's `conjectures/00000001561.md`.

| Reviewed file | SHA-256 |
|---|---|
| `lean/Conjecture1561/Definitions.lean` | `ff98abc40f083df4804e8a9b8ea41ce9333fcf0d74a1b9bd321d45b4f433d999` |
| `lean/Conjecture1561/Boundary.lean` | `84ea7adf14e9cd713c7b1b8b7254767ed8918a858eedf6f17f562e331455ea91` |
| `lean/Conjecture1561/Interior.lean` | `d796b6306bec6c22a79ac0cbd5b98fc5e41fc378c3d1480bb4ed38d1dcdbad55` |
| `lean/Conjecture1561.lean` | `1e7055409110d7a56ca89714b68408ddd7b08372a8943eb5abfaaa67a0901642` |
| `lean/Check.lean` | `4b25b016714ca45db499d6f1272c02c190a3e498053dbb28b4fe7883f7c121be` |
| `lean/lakefile.toml` | `d3ac9d84bdb3bcd27ce71f59920b4fb014aa9e708df8b140825f685b21b35324` |
| `lean/lake-manifest.json` | `a8c9be678435340e9e27372ff4dfaf1b675735e146af02b0c73f6b30cdacd325` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `main.tex` | `e43770fb05f556184b7445558983ab82f86ac5861e71ddbeb80fa4da6dd6ecea` |
| `main.pdf` | `a86042cc960c316b5844066a75503e9e7f9439705101dc1a7d20e95e04264e5f` |
| `README.md` | `04238b1f3a29402285c34f56c6a55e5d546d2b9893de9b34c1ca9648847518ba` |
| `VERIFICATION.md` | `434f9803bedf504e46e79df05c1792b3b583f237d3edddb3aae95cbddcd72c4e` |
| `eligibility/conjecture.md` | `e506d5b0b4e39df790fa1439d54fc82faeea0b5c11feef7acca1284a5023c454` |
| `eligibility/upstream-README.md` | `cd54d17f51e08212ee9557ef74568f6f2c388279ac74339dc4a3bab7c283f27e` |
| `eligibility/upstream-README.zh-CN.md` | `ffedf1385079b9741fce4176c7aa1662720c29391116b34e5e78ba154b4fa244` |
| `eligibility/eligibility.json` | `72fc7c210b18b1a6f0b815644106b86b0d7e4c8687798b2b191b1e3933e32724` |
| `verification/strict-replay.json` | `2cbb4c1b83f83017c80ddd76a8858db9ddb6a285121a8ef6a444e9809c14ac6d` |
| `verification/build.txt` | `3fd220ee26e29d76139ff38816a583294eaefb46c048f7bc81a46102ef1299b6` |
| `verification/axioms.txt` | `7fe58d779307fe1d1474d845a712a6b1d08fa3e7222549a3d54282846952029a` |
| `verification/pdf.json` | `517fa2a82ed8fa49273ef98b80b97be28c2f82d3ff26d9c816b17261b32d6100` |
| `verification/report.txt` | `dde2dd5301310b55e1efde01e4feb05fa128f3081a9fcc28d4d91f2f2edfbe51` |
| `verification/prepublication.json` | `9ea20fd19751587559a259120f2e223f76d225c0e9f234589a3fbd111835d73e` |
