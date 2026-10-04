# Verification record

Locally verified on 2026-10-04 with Lean 4.19.0, Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and Tectonic 0.17.0. These checks are separate from official maintainer acceptance.

## Fresh build and direct strict replay

The final seven Lean files and three project-configuration files were copied to a fresh project with no prior submission build outputs. Only pinned dependencies and their compiled cache were reused. All nine dependency revisions matched the manifest, and their tracked source trees had no modifications.

`lake build` rebuilt all six submission library modules successfully. The exact output is in `build.txt`. Each of the seven Lean sources, including `Check.lean`, then passed direct replay with `-DwarningAsError=true`. `strict-replay.json` records each file, zero exit status, and final check time. All six non-audit sources produced no output; `axioms.txt` contains the audit file's output.

The audit prints the actual law, density, log-concavity and isotropy predicates, admissible-law predicate, and one-dimensional consequence. It checks 24 public theorem/instance types and their axiom dependencies. Every axiom list contains only `propext`, `Classical.choice`, and `Quot.sound`.

All ten source/configuration files were compared byte for byte against the fresh checked copies. Source inspection and a scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `trustLevel` override. No numerical auxiliary program is used or required.

## Semantic scope

The independent review checks the actual pushed-forward exponential measure, its proved Lebesgue density, normalization, integrable mean-zero and unit-second-moment conditions, full density log-concavity including zero values and endpoint weights, and the exact open-right-tail probability derived from Mathlib's CDF theorem. It also checks event inclusion and the violation for every positive threshold constant, decay constant, and starting threshold.

Both source languages state a universal isotropic log-concave claim without excluding dimension one. Its one-dimensional consequence is necessary; the explicit qualifying counterexample and the negation of that consequence refute the first conjecture assertion. The report does not assert an exact formula for the absolute-value tail. See `../SEMANTIC_REVIEW.md` for the independent source review and its limits.

## Report

The submitted LaTeX compiled successfully with both the desktop editor's compiler and Tectonic. The final export log has no warnings, overfull boxes, or underfull boxes. `report.txt` preserves that successful log with trailing whitespace normalized.

All three PDF pages were rendered and visually inspected for complete text, formulas, margins, page breaks, and references. Extracted text was checked additionally. The submitted PDF is byte-identical to the inspected export, and the LaTeX source is the exact file used to compile it.

## Eligibility and artifact integrity

`eligibility.json` preserves the live unsolved metadata, all-state PR search, exact-ID and comment searches, keyword checks, and solution history. No prior, removed, or competing #7790 submission was identified. The exact bilingual source copy matches the repository file.

All changes are confined to `solutions/00000007790/C0ldSmi1e_submission_20261004075335/`. `SHA256SUMS.json` covers every other submitted file and was checked against the exact staged Git bytes before publication.
