# Verification record

Locally verified on 2026-10-04 using Lean 4.19.0 (arm64-apple-darwin23.6.0, compiler commit 6caaee842e94), Mathlib v4.19.0 at c44e0c8ee63ca166450922a373c7409c5d26b00b, and Tectonic 0.17.0. This record is not an official maintainer review.

## Fresh proof build

The six submitted Lean files and three project configuration files were copied into a fresh project directory with no existing submission build outputs. Only pinned dependency checkouts and their compiled library cache were reused. All nine dependency Git revisions were checked against the committed manifest.

`lake build` rebuilt all five submission modules successfully; see `build.txt`. All six Lean files were then replayed directly with warnings treated as errors:

```sh
for source in Definitions.lean DensityBounds.lean DensityIntegral.lean Probability.lean Conjecture420.lean Check.lean
do
  lake env lean -DwarningAsError=true "$source" || exit 1
done
```

Every command exited zero. The five proof modules produced no warnings or output. `axioms.txt` preserves the output of `Check.lean`: the central definitions, full concluding theorem type, and twelve axiom lists. Every list contains only `propext`, `Classical.choice`, and `Quot.sound`.

All nine submitted source/configuration files were compared byte for byte with the independently rebuilt copies. Inspection and a source scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `trustLevel` override. No auxiliary numerical computation is used or required.

A separate semantic source review checked the actual density, interval, integral, probability measure, weak-convergence topology, and all quantifiers. See `../SEMANTIC_REVIEW.md`.

## Report checks

The final source compiled successfully with the desktop LaTeX compiler and with Tectonic 0.17.0. `report.txt` contains the successful export log, with trailing whitespace normalized. The final export has no TeX warnings.

The PDF has three pages. Every page was rendered and visually inspected for complete text, formulas, margins, and page breaks; extracted text was also checked. The submitted PDF is byte-identical to the inspected export, and the submitted LaTeX is the exact source used to produce it.

## Eligibility and file scope

`eligibility.json` records the latest metadata and exact-ID PR search immediately before submission. The conjecture was unsolved and no previous submission was identified. The copied bilingual statement matches the repository file exactly. The PR changes only `solutions/00000000420/C0ldSmi1e_submission_20261004061601/`.

`SHA256SUMS.json` covers all other submission files, including the sources, PDF, configuration, documentation, and verification records. Its own file is excluded. Each hash was checked against the exact staged Git bytes before publication. Hashes supplement the proof build and semantic review; they do not replace them.
