# Verification record

Locally verified on 2026-10-04 with Lean 4.19.0 (arm64-apple-darwin23.6.0, compiler commit 6caaee842e94), Mathlib v4.19.0 at c44e0c8ee63ca166450922a373c7409c5d26b00b, and Tectonic 0.17.0. These are local results, not an official maintainer review.

## Fresh build and direct source replay

The five submitted Lean sources and three project configuration files were copied into a fresh project directory with no existing submission build outputs. Only pinned dependency checkouts and their compiled library cache were reused. All nine dependency revisions were checked against the committed manifest.

`lake build` rebuilt all four proof modules successfully; see `build.txt`. All five Lean files were then directly replayed with warnings treated as errors:

```sh
for source in Definitions.lean RealBound.lean ComplexBound.lean Conjecture308.lean Check.lean
do
  lake env lean -DwarningAsError=true "$source" || exit 1
done
```

All commands exited zero. The four proof modules produced no warnings or output. `axioms.txt` preserves the audit file's definitions, full Gaussian bound, final theorem type, and eight axiom lists. Each list contains only `propext`, `Classical.choice`, and `Quot.sound`.

All eight source/configuration files were compared byte for byte with the successfully rebuilt copies. Inspection and a source scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `trustLevel` override. No auxiliary numerical computation is used or required.

An independent semantic review checked all quantifiers, complex coercions and division, denominator positivity, both coordinate cases, the actual real axis, and the final first-conjunct negation. The standard definition was checked against two primary research sources; see the report and `../SEMANTIC_REVIEW.md`.

## Report verification

The exact submitted LaTeX compiled with the desktop compiler and with Tectonic 0.17.0. `report.txt` is the successful export log, with trailing whitespace normalized; the final export has no TeX warnings.

The three-page PDF was rendered page by page and visually inspected for complete text, correct formulas, margins, page breaks, and references. Extracted text was checked as well. The submitted PDF is byte-identical to the inspected export, and its source matches the exact file used to compile it.

## Eligibility and package scope

`eligibility.json` records live metadata, exact-ID search, and PR-history checks immediately before submission. The conjecture was unsolved and no earlier submission was identified. The preserved bilingual statement matches the repository file exactly. The PR changes only `solutions/00000000308/C0ldSmi1e_submission_20261004063225/`.

`SHA256SUMS.json` covers every other submission file, excluding itself. All recorded hashes were checked against the exact staged Git bytes before publication. They identify the checked artifacts and supplement the proof build and semantic review.
