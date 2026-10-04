# Local verification record

These are author-side checks and independent internal scrutiny, not an official repository review or maintainer acceptance.

## Mathematical and semantic coverage

- The exact English and Chinese source was inspected at upstream `0862407ef50dda4f7376342ca3e79368dce942d2` and copied unchanged to `conjecture.md`.
- The refuted clause is the unrestricted `2^n` solution-count bound. The source does not state a P-matrix, nonsingularity, finite-solution, or isolation premise for that first clause. The later tightness wording is discussed explicitly. The example is singular and is not claimed to refute a P-matrix-restricted reformulation.
- `LCPSolutions` uses the actual positive cone, matrix-vector product and dot product. Lean proves equivalence with the usual coordinatewise inequalities and complementary products.
- Lean classifies the complete solution set as the nonnegative diagonal ray and proves a natural-number injection, infinitude, extended cardinality equal to infinity, and five distinct actual solutions.
- The matrix's nonzeroness, determinant zero, Hermitian symmetry, quadratic form identity and standard positive semidefiniteness are proved.
- The final theorem directly negates the universal bound for all positive dimensions, real matrices and right-hand sides.
- Independent source/report scrutiny is recorded in `SEMANTIC_REVIEW.md`.

## Fresh build, strict replay and axioms

An independent verifier copied only the three Lean source files and three project configuration files into a fresh directory. No submission build output was copied. Only the pinned shared dependency cache was reused.

| Check | Result |
|---|---|
| Lean version and exact compiler commit | 4.19.0, `6caaee842e9495688c1567e78c0e68dbb96942aa` |
| Mathlib revision | `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| All nine dependency revisions | Match the submitted manifest |
| Tracked dependency trees | Clean before and after verification |
| Fresh `lake build` | Exit 0 |
| Strict replay of `Conjecture3794/Problem.lean` | Exit 0 |
| Strict replay of `Conjecture3794.lean` | Exit 0 |
| Strict replay of `Check.lean` | Exit 0 |
| Definition/type audit | Six definitions and all 23 theorem types |
| All 23 transitive axiom audits | Only `propext`, `Classical.choice`, `Quot.sound` |
| Source/config identity | Original and independent copies unchanged |
| Proof-bypass scan | No hits |

The strict replays used `lake env lean -DwarningAsError=true`. `verification/strict-replay.json` records commands, exit codes, compiler identity, dependency revisions, complete source hashes and audit details. `verification/build.txt` and `verification/axioms.txt` contain the build and definition/type/axiom output. The scan covered admitted proofs, custom axioms, native evaluation and explicit kernel-check bypasses; the axiom audits provide the transitive evidence. No auxiliary numerical program is used or required.

## Report

The final `main.tex` compiles successfully with both the desktop editor's compiler and Tectonic 0.17.0. The exported two-page PDF was rendered with Poppler; both final page images were visually inspected for readable equations, matrix signs, source quote, scope statements, formal correspondence, references and layout. No TeX warnings, clipping, overflow, overlap or missing symbols remain. Extracted text was also checked for key content.

`verification/pdf.json` records the final TeX/PDF SHA-256 hashes, compiler results and visual checks. `verification/report.txt` preserves the successful TeX log with only trailing whitespace removed. The PDF was produced from the exact submitted TeX source.

## Eligibility and package integrity

Both current contribution guides were checked. `verification/eligibility.json` records unsolved metadata, the live bilingual source and guide identities, all-state PR title/body/head searches, exact/short-ID comment searches, topic searches, and current/historical solution-path checks. No prior or competing submission for this conjecture was found; unrelated broad keyword matches were classified. Consequently no prior-error account is applicable.

Only the personal submission folder is included. `verification/SHA256SUMS.json` hashes every other submitted file. Those digests are checked against the exact staged Git contents before publication. Build products, dependency directories and scratch files are excluded. The README contains reproduction commands.
