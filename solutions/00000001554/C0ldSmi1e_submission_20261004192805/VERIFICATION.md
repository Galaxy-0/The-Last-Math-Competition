# Verification record for conjecture 00000001554

These are local execution and review records. They do not assert maintainer acceptance.

## Independent Lean execution

A separate execution agent copied only the four final Lean source files and three project configuration files to a fresh directory. There were no project build outputs in that directory. It reused an existing dependency cache only after checking every one of the nine manifest-pinned dependency revisions and confirming that their tracked sources were clean. It repeated those checks after execution.

- Finished: `2026-10-04T19:26:09.768843+00:00`.
- Lean: `4.19.0`, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`, checked before and after.
- Mathlib: `v4.19.0`, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Fresh `lake build`: exit 0 (8.881 seconds); the default library target imports both proof modules and builds the final theorem.
- Separate `lake env lean -DwarningAsError=true` replays of `Conjecture1554/Geometry.lean`, `Conjecture1554/Coloring.lean`, `Conjecture1554.lean`, and `Check.lean`: all exit 0.
- All nine definition/abbreviation printouts, eighteen theorem type checks, and eighteen theorem axiom audits were matched to an independent inventory of actual declarations. There are no named instances or unexamined anonymous declarations.
- Every theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- The proof-bypass scan found zero raw or code matches for admitted proofs, custom axiom declarations, `native_decide`, unsafe elaboration/execution bypasses, or kernel-trust modifications. Actual axiom outputs were also inspected.
- All seven source/configuration hashes were identical before and after execution and equal to their independent copies.

`verification/strict-replay.json` contains complete commands, outputs, dependency identities, source inventory, and name reconciliation. `verification/build.txt` records the fresh build; `verification/axioms.txt` records the actual definition/type/axiom output. `Check.lean` is shipped, so reviewers can reproduce the audit directly. No numerical sampling, finite search, or external computational result is required by the proof.

## Source identity

Paths below are relative to `lean/`.

| File | SHA-256 |
| --- | --- |
| `Conjecture1554/Geometry.lean` | `a137f1acf0dfde44dfd45b980e3aea8c5f8e8ff0a31b2e9a974d413375dd6b3c` |
| `Conjecture1554/Coloring.lean` | `9d41a40967e55f5aad5cfb0458bd5e29a01be2d330ee0d3a127630818fae03a9` |
| `Conjecture1554.lean` | `9417ea707ae6f233846a50bac0dd37ff4446531496f0f79f63e63f2e5374013b` |
| `Check.lean` | `8d0177256cfda351ecc92bab74bbb7e1254167fd2bcb2888878caf54397a5745` |
| `lakefile.toml` | `7d282829e1d43e14edf1523414741bb3cce14751ebdc3bd650fdb12741ffb2b8` |
| `lake-manifest.json` | `ea34271e98bdb5c5c27dd2f13591b203a40fcceee4738f9bb8628f5675e596a2` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |

## Statement fidelity and independent scrutiny

The source uses the actual metric on `EuclideanSpace ℝ (Fin 2)`. The three distance-one equalities imply noncoinciding vertices and derive the rotation-independent height identity. The coloring uses integer floor at every real height, so negative heights and exact strip boundaries are included. The six weak height orders cover ties. Both colors are attained. The final theorem negates precisely the source's explicit universal unit-triangle assertion.

A separate semantic reviewer, who authored none of these proof modules, reads the exact bilingual statement, all final Lean source, the full report, these records and the actual emitted declaration outputs. Its final hash-specific findings are supplied in `SEMANTIC_REVIEW.md`. This independent semantic scrutiny is distinct from the independent execution above. The classical construction is attributed in the report; its truth is proved within Lean, not assumed from the reference.

## Report and PDF

The built-in LaTeX compiler reported success. Export with Tectonic 0.17.0 exited 0 with no warnings or overfull/underfull box diagnostics. The resulting PDF has two pages and 50239 bytes. The root agent rendered and visually inspected both entire pages at 1500 pixels, checking formulas, floor brackets, cases, boundary inequalities, page breaks, margins, and references; no clipping or overlap was found. The semantic reviewer is not represented as having performed that visual check.

- `main.tex` SHA-256: `42f57277ef2d9477acc3a0c2558b7447abac44fade2b08953c249b7db0ec5626`.
- `main.pdf` SHA-256: `054b55f36f6e5135738134eee9ed12548ac371459c052469275557a9d3555602`.
- `verification/pdf.json` records these checks; `verification/report.txt` contains the export compiler log, with trailing line whitespace removed and all diagnostic text retained.

## Eligibility and contribution scope

The initial eligibility snapshot examined current upstream main, both full contribution guides, the exact bilingual source, metadata, all 547 then-existing PR titles/bodies/head branches, indexed exact/short-ID and topic/comment searches, and local/all-ref plus upstream-main solution-path history. Conjecture 00000001554 was unsolved, with no matching prior or competing submission. Topic hits PR38 (flat-torus eigenvalues), PR68 (Petersen graphs), and PR455 (Hilbert-space Borsuk partitions) concern other conjectures and were explicitly classified as unrelated. The initial record is `verification/eligibility.json`; a fresh check immediately before packaging is recorded in `verification/prepublication.json`.

The submission contains only its personal solution directory. No conjecture descriptions, repository guides, metadata, leaderboard, or official review files are changed. The bundled conjecture is byte-identical to the official source. `verification/SHA256SUMS.json` covers every submitted file other than the manifest itself.
