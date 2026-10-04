# Verification record

Locally verified on 2026-10-04 with Lean 4.19.0, Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and Tectonic 0.17.0. These are internal checks, separate from maintainer acceptance.

## Fresh project and strict source replay

The two final Lean files and three configuration files were copied into a fresh project with no previous submission build outputs. Only pinned dependency checkouts and their compiled cache were reused. All nine dependency revisions matched the committed manifest.

`lake build` rebuilt the submission module successfully; see `build.txt`. Both sources then passed direct replay with warnings treated as errors:

```sh
lake env lean -DwarningAsError=true Conjecture1259.lean
lake env lean -DwarningAsError=true Check.lean
```

All three commands exited zero. The proof-module replay produced no output. `axioms.txt` records the printed substitution, counted matrix, cubic and predicate, the ten theorem types, and their ten axiom lists. The only axioms in those lists are `propext`, `Classical.choice`, and `Quot.sound`.

Every source/configuration file was compared byte for byte with the fresh checked copy. Source inspection and a scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `trustLevel` override. No auxiliary numerical program is used or needed.

Independent semantic scrutiny checked the exact bilingual statement, the substitution-to-matrix connection, the actual characteristic polynomial, real roots counted with multiplicity, degree three, the discriminant identity, and the transpose convention. The report explicitly identifies the necessary clause being refuted and does not invent a definition for the vague hull terminology. See `../SEMANTIC_REVIEW.md`.

## Report

The final submitted LaTeX compiled successfully with the desktop editor's compiler and with Tectonic. All three PDF pages were rendered and visually inspected. Formulas, text, page breaks, reproduction commands, and the source link are legible and complete. Extracted text was checked as an additional check, not a substitute for visual review.

The final TeX log has no warnings or box problems. `report.txt` preserves the log with trailing whitespace normalized. The submitted PDF is byte-identical to the inspected export, and the submitted LaTeX is the exact source used to compile it.

## Eligibility and scope

`eligibility.json` records the live unsolved metadata, all-state PR inspection, exact-ID searches, and solution history. No earlier or competing #1259 submission was identified. PR80's Tribonacci mention concerns the different conjecture #1260 about factor complexity.

The bilingual source copy matches the repository conjecture exactly. Changes are confined to `solutions/00000001259/C0ldSmi1e_submission_20261004072829/`. `SHA256SUMS.json` covers every other submission file, with hashes checked against the exact staged Git bytes before publication.
