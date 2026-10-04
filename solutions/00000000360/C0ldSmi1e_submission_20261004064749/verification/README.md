# Verification record

Locally verified on 2026-10-04 with Lean 4.19.0, Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and Tectonic 0.17.0. These are local results, not official maintainer acceptance.

## Fresh build and source replay

The final two Lean sources and three configuration files were copied into a fresh project directory with no existing submission build outputs. Only pinned dependency checkouts and their compiled library cache were reused. All nine dependency revisions were checked against the manifest.

`lake build` rebuilt `Conjecture360` successfully; see `build.txt`. Both Lean files were then directly replayed:

```sh
lake env lean -DwarningAsError=true Conjecture360.lean
lake env lean -DwarningAsError=true Check.lean
```

All three commands exited zero. The proof module produced no warnings or output. `axioms.txt` preserves the audit file's printed definitions, theorem types, and eleven axiom lists. Every list contains only `propext`, `Classical.choice`, and `Quot.sound`.

All five source/configuration files were compared byte for byte with the freshly checked copies. Source inspection and a scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `trustLevel` override. No auxiliary numerical computation is used or required.

An independent source review checked the actual matrix product and determinant, both coefficient classes, all dimensions and integer witnesses, the exact constant, the strictly positive uniform improvement, and the final negation. See `../SEMANTIC_REVIEW.md` for its scope.

## Report verification

The exact submitted LaTeX compiled with the desktop editor's compiler and Tectonic 0.17.0. The final export has no TeX warnings. `report.txt` contains its successful export log with trailing whitespace normalized.

All three PDF pages were rendered and visually inspected for complete text, formulas, margins, page breaks, and references. Extracted text was also checked. The submitted PDF is byte-identical to the inspected export, and the submitted source matches the exact compiled file.

## Eligibility and package integrity

`eligibility.json` records live unsolved metadata and a check of all 419 pull-request records, together with an exact-ID search. The only exact-ID search match was PR5's administrative scoring discussion; it was inspected and contains no earlier solution. No earlier submission was identified.

The bilingual source copy matches the repository file exactly. All submission changes are confined to `solutions/00000000360/C0ldSmi1e_submission_20261004064749/`. `SHA256SUMS.json` covers every other submission file, excluding itself; each recorded hash was checked against the exact staged Git bytes before publication.
