# Verification record

Verified locally on 2026-10-04 with Lean 4.19.0 (arm64-apple-darwin23.6.0, compiler commit 6caaee842e94), Mathlib v4.19.0 at c44e0c8ee63ca166450922a373c7409c5d26b00b, and Tectonic 0.17.0. These results are not an official maintainer review.

## Proof build and source replay

The five submitted Lean files and three project configuration files were copied to a fresh directory with no project build outputs. Only pinned dependency checkouts and their compiled library cache were reused. All nine dependency Git revisions were compared to the committed manifest and matched.

`lake build` rebuilt all four submission modules successfully; see `build.txt`. Every submitted Lean file was then directly replayed with warnings treated as errors:

```sh
for source in CycleFacts.lean CycleTrees.lean NumberTheory.lean Conjecture464.lean Check.lean
do
  lake env lean -DwarningAsError=true "$source" || exit 1
done
```

All five commands exited zero. The four proof modules produced no output or warnings. `axioms.txt` preserves the audit output from `Check.lean`: the actual central definitions, full final theorem type, and eleven theorem dependency lists. Every list contains only `propext`, `Classical.choice`, and `Quot.sound`.

All eight submitted source/configuration files were compared byte for byte with the successfully rebuilt independent copies. A source inspection and scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `trustLevel` override. There is no auxiliary numerical computation to rerun: the spanning-tree count and asymptotic contradiction are formally proved for all parameters.

An independent agent performed a complete semantic source audit and checked relevant Mathlib definitions; its conclusion is summarized in `../SEMANTIC_REVIEW.md`.

## Report checks

The final `main.tex` compiled successfully with the built-in desktop LaTeX compiler and was exported using:

```sh
tectonic --keep-logs --outdir OUTPUT_DIRECTORY main.tex
```

`report.txt` is the successful export log with trailing whitespace normalized. The final export has no TeX warnings. The resulting PDF has three pages; each page was rendered to an image and visually inspected for complete text, correct formulas, margins, and page breaks. Extracted text was checked against the report. The submitted PDF is byte-identical to that inspected export, and the submitted source is the source used to produce it.

## Eligibility and scope

`eligibility.json` records the live metadata and exact-ID PR search immediately before submission. The conjecture was unsolved and no earlier submission was identified. The preserved `conjecture.md` matches the repository statement. All submission files are confined to `solutions/00000000464/C0ldSmi1e_submission_20261004055513/`; no official review, conjecture, metadata, leaderboard, or README outside that directory is changed.

`SHA256SUMS.json` covers every other file in the submission, including the PDF, LaTeX, all Lean sources/configuration, and verification records. Its own file is excluded. Hashes identify the checked artifacts; they supplement rather than replace the proof build and semantic review.
