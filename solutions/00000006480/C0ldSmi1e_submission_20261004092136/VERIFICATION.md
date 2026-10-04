# Local verification record

These checks and the independent internal semantic review are author-side evidence. They are separate from official competition review and maintainer acceptance.

## Mathematical coverage

The exact bilingual statement and both contribution guides were checked at upstream revision `0862407ef50dda4f7376342ca3e79368dce942d2`. The proof provides explicit finite processes with equal covariance and different maximum and joint distributions. The source does not require an infinite index set or an asymptotic limiting law.

- The actual uniform PMF measure on `Fin 8` is a probability measure. The eight outcomes enumerate all sign triples, and the processes are `X=(A,B,C)` and `Y=(A,B,AB)`.
- Measurability, coordinate integrability and centered covariance-product integrability are proved. The zero-mean and identity-covariance calculations use actual Bochner integrals, reduced by the uniform-PMF integral theorem.
- The joint and maximum laws are actual measure pushforwards, with probability-measure instances. Their respective singleton probabilities separate the laws. Full maximum-law equalities are proved: `(1/8) δ₋₁ + (7/8) δ₁` and `δ₁`.
- The maximum bounds every coordinate and is attained by one of the three indices.
- Every coordinate has an atom of mass one-half at `−1`. A Gaussian law with nonzero variance is atomless; one with zero variance is a Dirac measure. Thus both actual processes fail the standard Gaussian property, which requires an actual Gaussian law for every real linear combination.
- The final existential theorem combines the explicit probability space, both processes, the required measurability and integrability, equal covariance, both unequal laws and both non-Gaussian properties.

## Independent build and trust audit

Only the four final Lean files and three project configuration files were copied to a fresh independent project. No submission build outputs were copied; only the pinned dependency cache was reused.

| Check | Result |
|---|---|
| Lean compiler | 4.19.0, exact commit `6caaee842e9495688c1567e78c0e68dbb96942aa` |
| Mathlib | v4.19.0, exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| All nine dependency revisions | Match manifest; tracked sources clean before and after |
| Fresh `lake build` | Exit 0 |
| Strict replay of Processes, Gaussian, root and Check | All four exit 0 |
| Definition printouts | All 12 matched |
| Theorem/instance type and transitive-axiom audits | All 42 matched |
| Allowed axiom dependencies | Only `propext`, `Classical.choice`, `Quot.sound` |
| Proof-bypass scan | No hits |
| Original and independent source/configuration hashes | All seven identical and unchanged |

Strict replays used `lake env lean -DwarningAsError=true`. `verification/strict-replay.json` records exact commands, exit codes, source hashes, compiler and dependency identities and parsed audits. `verification/build.txt` and `verification/axioms.txt` preserve build and definition/type/axiom output. The source scan checks admitted proofs, user axioms, native evaluation and explicit kernel-check bypasses. The theorem dependency lists contain only the standard Lean axioms noted above. All mathematical computations are part of the Lean proof; no auxiliary numerical program is needed.

## Matching report and file identities

The final LaTeX source compiles successfully in the built-in editor and with Tectonic 0.17.0. The exported PDF has two pages. Both were rendered with Poppler and visually inspected, covering the statement, explicit model, covariance equations, maximum-law table, full proof, formal correspondence and references. No TeX warnings, clipping, overlap, missing glyphs, blank pages or orphan references remain. Text extraction also confirmed key content.

`verification/pdf.json` preserves exact TeX/PDF hashes and the inspection record. `verification/report.txt` is the successful TeX log with trailing whitespace removed. The submitted TeX/PDF pair is byte-identical to the pair used for these checks. The semantic review records hashes of the exact source files and report it inspected.

Only the personal submission directory is changed. `verification/SHA256SUMS.json` hashes every other submitted file, and those hashes are checked against the exact staged Git contents. Scratch audits, compiled submission artifacts and dependency directories are excluded.

## Eligibility

`verification/eligibility.json` records unsolved metadata, exact source and guide identities, all-state PR title/body/head searches, padded/short-ID comment searches, topic searches, and current/historical solution-path checks. Two broad substring matches concerned “disjointness” in unrelated conjectures and were individually classified. No previous, removed, competing or successful submission for this conjecture was identified; no prior-error account is applicable. The final refresh is saved separately in `verification/prepublication.json`.
