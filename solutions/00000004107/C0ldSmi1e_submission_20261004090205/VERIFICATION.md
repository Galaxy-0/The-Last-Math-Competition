# Local verification record

These checks and the independent internal semantic review are author-side evidence, separate from official competition review and maintainer acceptance.

## Mathematical coverage

The exact bilingual statement and both contribution guides were checked at upstream revision `0862407ef50dda4f7376342ca3e79368dce942d2`. The submission refutes the universal sign-alternation clause for subspace arrangements. It does not silently restrict the problem to hyperplanes or assume all members have the same dimension.

- `U` and `W` are actual real submodules of `Fin 3 → ℝ`, with explicit coordinate membership conditions.
- Explicit linear equivalences prove dimensions two and one. Actual zero-intersection, nonzero, properness and mutual noncontainment facts are proved.
- `IntersectionPoset A` is the reverse-inclusion subtype of actual submodules obtained as finite intersections of an arbitrary finite family. The empty subfamily gives the ambient space, and equal intersections are identified.
- A surjection from all finite subfamilies proves finiteness. The concrete poset is classified completely as ambient, plane, axis and origin.
- Exact intervals in this actual poset allow Mathlib's `IncidenceAlgebra.mu` recurrence to compute the Möbius values. The characteristic sum uses these values and actual `Module.finrank` exponents.
- The resulting polynomial identity is `X^3 - X^2 - X + 1`. Its actual adjacent coefficients at one and two are both negative. The final theorem negates the universal strict sign assertion and also proves failure of a weaker adjacent-sign condition. No zero-coefficient convention can repair the example.
- `SEMANTIC_REVIEW.md` independently checks these source/report correspondences against the standard primary definition.

## Independent build and trust audit

Only the five final Lean files and three project configuration files were copied to a fresh independent project. No submission build outputs were copied; only the cache of the pinned dependencies was reused.

| Check | Result |
|---|---|
| Lean compiler | 4.19.0, exact commit `6caaee842e9495688c1567e78c0e68dbb96942aa` |
| Mathlib | v4.19.0, exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| All nine dependency revisions | Match manifest; tracked sources clean before/after |
| Fresh `lake build` | Exit 0 |
| Strict replay of Geometry, Arrangement, Signs, root and Check | All five exit 0 |
| Definition printouts | 17 definitions/abbreviations |
| Theorem type and transitive axiom audits | All 47 checked |
| Allowed axiom dependencies | Only `propext`, `Classical.choice`, `Quot.sound` |
| Proof-bypass scan | No hits |
| Original and independent source/configuration hashes | All eight unchanged |

Strict replays used `lake env lean -DwarningAsError=true`. `verification/strict-replay.json` preserves exact commands, exit codes, file hashes, dependency identities and parsed audit results. `verification/build.txt` and `verification/axioms.txt` preserve build and definition/type/axiom output. The source scan checks for admitted proofs, user axioms, native evaluation and explicit kernel-check bypasses; the transitive axiom lists verify the theorem dependency boundary. No numerical auxiliary computation is needed.

## Report and file identity

The final TeX source compiles with both the built-in editor compiler and Tectonic 0.17.0. The exported PDF has two pages. Both were rendered with Poppler and visually inspected, including the source quote, subspace definitions, dimension/Möbius table, polynomial signs, full proof and formal correspondence. No TeX warnings, overlap, clipping, missing symbols, orphan-only or blank pages remain. Text extraction was additionally checked for key content.

`verification/pdf.json` records exact source/PDF hashes and the checks. `verification/report.txt` is the successful TeX log with trailing whitespace removed. The submitted source is byte-identical to the source used for the exported PDF and the independent semantic review.

The package changes only the personal submission directory. `verification/SHA256SUMS.json` covers every other submitted file; hashes are checked against exact staged Git contents. Build products, dependency directories and scratch probes/audits are excluded.

## Eligibility

`verification/eligibility.json` records unsolved metadata, exact statement and guide identities, all-state PR title/body/head searches, exact/short-ID comment searches, topic searches, and local/all-ref and upstream current/historical solution-path checks. Broad characteristic-polynomial matches were inspected and concern unrelated conjectures. No prior, removed, competing or successful submission for this conjecture was identified, so no prior-error account is applicable.
