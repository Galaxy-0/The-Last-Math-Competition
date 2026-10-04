# Verification record

Locally verified on 2026-10-04 with Lean 4.19.0, Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and Tectonic 0.17.0. Internal verification is separate from official maintainer acceptance.

## Fresh build and strict source replay

The final four Lean sources and three project configuration files were copied into a fresh project without submission build outputs. Only the pinned dependencies and their compiled cache were reused. All nine dependency revisions matched the manifest, and their tracked source trees were clean before and after the build.

`lake build` rebuilt all three submission library modules successfully. The output is in `build.txt`. Each of the four Lean files then passed direct replay with `-DwarningAsError=true`. The three proof modules produced no output during direct replay; `axioms.txt` records `Check.lean` output. `strict-replay.json` contains exact commands, zero exit statuses, dependency revisions, source hashes, and timestamps.

The audit prints nine definitions and checks all 19 theorem types and their transitive axiom dependencies. Every list is a subset of the standard principles `propext`, `Classical.choice`, and `Quot.sound`. This is not a zero-axiom claim. Source inspection and scanning found no admitted proofs, custom axioms, `native_decide`, `unsafe`, or trust bypass.

All seven source/configuration files were compared byte for byte against the fresh checked copies. No numerical auxiliary program is used or required: the actual counting lower bound and the asymptotic obstruction are formal theorems.

## Semantic review

Independent internal scrutiny read the exact bilingual conjecture, every source file, the pinned Mathlib definitions, and the full report. It verified that the actual cycle partition includes fixed-point cycles, the subtype cardinality is the original permutation count, and the injection transports actual permutations to the exact `2*n`-element domain.

The review checked factorial growth against the exact expression, cofinality of the even subsequence, simultaneous eventual bounds, positive denominator conditions, the exact printed constant, and the connection to Mathlib's asymptotic-equivalence relation. The final theorem negates the primary source assertion unconditionally. The subsequent capacity-integral claim is not needed. `../SEMANTIC_REVIEW.md` identifies the audited source/report hashes and the review's limits.

## Report

The final LaTeX compiled successfully with the desktop editor's compiler and Tectonic. The final export log has no warnings or overfull/underfull boxes; `report.txt` preserves it with trailing whitespace normalized. A missing standard font was fetched during preparation before the successful final export.

All three final PDF pages were rendered and visually inspected for text, formulas, page boundaries and legibility. Extracted text was also checked. The submitted PDF is byte-identical to the inspected export; `main.tex` is the exact source used for that export.

## Eligibility and integrity

`eligibility.json` records fresh unsolved metadata, all-state PR searches, exact-ID/comment and keyword checks, and solution history. No prior, removed, or competing #141 submission was identified. The short-ID hit on PR141 concerns conjecture 58, not this problem. The copied bilingual conjecture matches the recorded source revision.

All changes are confined to `solutions/00000000141/C0ldSmi1e_submission_20261004083001/`. `SHA256SUMS.json` covers every other submitted file and was checked against exact staged Git contents before publication.
