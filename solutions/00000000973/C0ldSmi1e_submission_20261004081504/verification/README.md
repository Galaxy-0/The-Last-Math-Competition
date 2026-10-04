# Verification record

Locally verified on 2026-10-04 with Lean 4.19.0, Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and Tectonic 0.17.0. Internal verification is distinct from official maintainer acceptance.

## Fresh build and strict source replay

The final four Lean sources and three project configuration files were copied into a fresh project with no submission build outputs. Only the pinned dependencies and their compiled cache were reused. All nine dependency revisions matched the manifest, and their tracked source trees were clean both before and after the build.

`lake build` rebuilt all three submission library modules successfully. The exact output is in `build.txt`. All four Lean files, including `Check.lean`, then passed direct replay with `-DwarningAsError=true`. The three proof modules produced no output during direct replay. `strict-replay.json` records the full commands, zero exit statuses, hashes, dependency verification and timestamps. `axioms.txt` preserves the audit output.

The audit prints six defining objects/predicates and checks 17 theorem types and transitive axiom dependencies. Every axiom list contains only `propext`, `Classical.choice`, and `Quot.sound`, the standard logical, choice and quotient principles. Source inspection and scanning found no admitted proofs, custom axioms, `native_decide`, `unsafe`, or trust bypass. This is not a zero-axiom claim.

All seven source/configuration files were compared byte for byte with the fresh checked copies. No numerical auxiliary program is used or needed: every mathematical calculation needed for the general disproof is proved in Lean.

## Semantic review

Independent internal review read the exact English and Chinese conjecture, all Lean sources, the pinned Mathlib definitions, and the full LaTeX report. It checked the unrestricted matrix and polynomial quantifiers, actual complex spectrum, actual polynomial evaluation, Euclidean operator norm, and genuine supremum of the nonempty bounded set of polynomial moduli.

The review also checked nonemptiness and boundedness for every union of two positive-radius disks under both open and closed interpretations, and the final negation at order two of the explicit all-orders-below-15 clause. No normality, contraction, resolvent, attainment or compactness assumptions are introduced. The report identifies the separate numerical example as an illustration rather than a separately named Lean theorem. See `../SEMANTIC_REVIEW.md` for the signed-off source hashes and precise review scope.

## Report

The final LaTeX source compiled successfully with the desktop editor's compiler and Tectonic. The final export log has no warnings, overfull boxes, or underfull boxes. `report.txt` preserves the successful log with trailing whitespace normalized.

All three final PDF pages were rendered and visually inspected for complete text, formulas, margins, page breaks and references. Extracted text additionally confirmed the theorem names, version numbers and numerical illustration. The submitted PDF is byte-identical to the inspected export, and `main.tex` is the exact source used for that export.

## Eligibility and artifact integrity

`eligibility.json` records the current unsolved metadata, all-state pull-request searches, exact-ID/comment searches, relevant keyword checks and solution history. No previous or competing submission for #973 was identified. The copied bilingual source matches the upstream source at the recorded revision.

All changes are confined to `solutions/00000000973/C0ldSmi1e_submission_20261004081504/`. `SHA256SUMS.json` covers every other submitted file and was checked against the exact staged Git bytes before publication.
