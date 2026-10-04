# Verification record for conjecture 00000005960

These are local verification records, distinct from maintainer acceptance.

## Independent execution of the complete Lean project

A separate execution agent copied only the five final Lean files and three project configuration files into a fresh directory, with no project build outputs. Its shared dependency cache was checked against all nine exact manifest revisions, with clean tracked sources before and after execution.

- Finished: `2026-10-04T19:49:49.261921+00:00`.
- Lean 4.19.0, exact compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`, verified before and after.
- Mathlib v4.19.0, revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Fresh `lake build`: exit 0, 13.056 seconds. Its default library target imports every implementation module and builds the final existential theorem.
- Direct `lake env lean -DwarningAsError=true` replays of all five Lean files, including `Check.lean`: all exit 0.
- All 101 named source declarations were independently inventoried. The actual emitted output contains all 21 definition/abbreviation printouts and all 80 type/axiom audits: 78 theorems plus the two named matrix measurable/Borel instances. No anonymous declarations were left outside coverage.
- Every audited axiom list is confined to `propext`, `Classical.choice`, and `Quot.sound`. The actual emitted names and counts match the source inventory.
- The proof-bypass scan found zero raw or code matches for admitted proofs, custom axiom declarations, `native_decide`, unsafe elaboration/execution bypasses, or kernel-trust modifications. The actual axiom output supplies a separate check.
- All eight source/configuration hashes and the declaration-inventory hash remained unchanged; the fresh copies match the reviewed originals. All nine dependency pins and clean tracked-tree checks passed again after execution.

The complete commands, outputs, declaration reconciliation, compiler/dependency identities and source hashes are in `verification/strict-replay.json`. The build log is `verification/build.txt`; the actual definition/type/axiom output is `verification/axioms.txt`. `Check.lean` is shipped so the audit can be reproduced. There are no auxiliary numerical programs or simulation-derived assumptions.

## Exact source identities

Paths below are relative to `lean/`.

| File | SHA-256 |
| --- | --- |
| `Conjecture5960/Family.lean` | `c1615f8bc27d9d2cc95543efc62c94699d2acfc380075d8705aa75dcd719484f` |
| `Conjecture5960/Eigenvectors.lean` | `2999a60476556cfcdb3150b8435514646f9046e687dc02758eb5dc690ad857d0` |
| `Conjecture5960/Ensembles.lean` | `854c515112a08c106fe3f947542fec1f1c87c5d3b3ad9fc79226001de551d53c` |
| `Conjecture5960.lean` | `28e491f6f771b536f6df17e434f9ad2e457942661c65e48accbb1227f9ca228a` |
| `Check.lean` | `7552003c6c8386d773ad67b2b068396bd50a04ca949666da5f586379f9241618` |
| `lakefile.toml` | `5c37fc093e35fa841517306238f78a8f3034509f33fde318b6fa9feabc49ac86` |
| `lake-manifest.json` | `def2a89f4a67281ff33c92f7aa020a040ff0708828085f07541614661b532cfb` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |

## Mathematical scope and independent review

The final theorem exhibits one explicitly defined all-real rational family and two explicit parameter maps on the same fair finite probability space. The family has actual symmetric matrices, the full actual characteristic polynomial and spectrum, continuity, and interval injectivity. Both realized matrix measures are non-Dirac. The equal spectral laws are actual characteristic-polynomial and spectrum pushforwards, preserving multiplicity through the characteristic polynomial.

The statistic is defined from the actual Euclidean eigenspace and its orthogonal projection. Its scalar formula is a derived theorem, with a further equality to the squared first coordinate of every normalized eigenvector for eigenvalue one. Actual measure-pushforward identities and measurability of the finite-domain observables justify the probability interpretation. No global measurable eigenvector choice or global measurability of an eigenvector-selection function is assumed.

The report's increasingly ordered eigenvalue list `(1,3)` follows from the degree-two characteristic polynomial with its distinct roots. Lean records the stronger explicit charpoly/spectrum certificates without introducing an assigned spectral list. The report distinguishes the two scalar laws at the event `{1}`, while the formal mass witnesses use `{0}`; the exact proved laws give mass one half versus zero at either event.

A separate semantic reviewer who authored none of the proof modules or report scrutinizes the complete bilingual source, final Lean project, report and documentation, and the actual emitted execution evidence. Its final hash-specific findings appear in `SEMANTIC_REVIEW.md`. The mathematical scrutiny, independent execution, and PDF author review are separately attributed.

## Matching report and PDF

The built-in LaTeX compiler reported success. Tectonic 0.17.0 exported the matching three-page PDF with exit 0, no warnings, and no overfull/underfull box diagnostics. The report-author agent rendered all three complete pages at 1500 pixels and visually inspected formulas, matrices, eigenspace/projection notation, probability laws, interval injectivity, theorem, bibliography, margins and page breaks. This was author visual QA, not the independent semantic review. A single trailing source space was removed, after which compilation/export/rendering and all-page inspection were repeated.

- `main.tex` SHA-256: `d32a20c3c523b848241d7117443fd350bf277ff310c6534960a7ac834dc534ca`.
- `main.pdf` SHA-256: `41c08fd25ec84239f9912f3957da42b9c2274b0edd9f63113f6c326ce6f79f9b`.
- PDF: 3 pages, 61255 bytes.
- `verification/pdf.json` records the artifact checks. `verification/report.txt` contains the compiler log with trailing whitespace removed and all diagnostic text retained.

## Contribution eligibility and package scope

The initial live check examined current upstream main, both complete contribution guides, the exact bilingual source, metadata, all 548 then-existing PR titles/bodies/head branches, exact/short-ID and topic/comment searches, and current plus historical solution paths. The source was unsolved and no prior or competing submission for 00000005960 was identified. Eighteen broad spectral-topic matches were individually classified as other conjectures; they were not treated as empty search results. `verification/eligibility.json` preserves that record, and `verification/prepublication.json` records the fresh eligibility check before packaging.

Only the personal submission directory is included. No repository conjecture description, guide, metadata, leaderboard or official review file is modified. The bundled conjecture is copied byte-for-byte from the official source. `verification/SHA256SUMS.json` covers every submitted file except itself. Local validation and this internal semantic review do not establish repository acceptance.
