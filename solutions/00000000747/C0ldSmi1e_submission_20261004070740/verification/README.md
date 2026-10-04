# Verification record

Locally verified on 2026-10-04 with Lean 4.19.0, Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and Tectonic 0.17.0. These are local checks, separate from maintainer acceptance.

## Fresh project build and strict replay

The final two Lean sources and three configuration files were copied into a fresh project with no prior submission build outputs. Only pinned dependency checkouts and their compiled library cache were reused. All nine dependency revisions matched the committed manifest.

`lake build` rebuilt `Conjecture747` successfully; see `build.txt`. Both source files were then replayed directly:

```sh
lake env lean -DwarningAsError=true Conjecture747.lean
lake env lean -DwarningAsError=true Check.lean
```

All three commands exited zero. The proof module produced no warnings or output. `axioms.txt` preserves the printed actual-domain and conjecture definitions, theorem types, and eight axiom lists. Every list contains only `propext`, `Classical.choice`, and `Quot.sound`.

All five source/configuration files were compared byte for byte with the fresh checked copies. Source inspection and a scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `trustLevel` override. The primality proof for five uses ordinary kernel-checked `decide`. No auxiliary numerical program is used or required.

An independent semantic review covered the actual p-adic domain, characteristic-zero inequalities, all allowed primes, actual function iterates, the positive-iterate condition, and both final negations. It also reviewed the report and historical error account. Its scope is recorded in `../SEMANTIC_REVIEW.md`.

## Report

The exact submitted LaTeX compiled successfully with the desktop compiler and Tectonic. The final export contains no TeX warnings. `report.txt` preserves its successful export log, with trailing whitespace normalized.

All three PDF pages were rendered and visually inspected for legible formulas, complete text, page breaks, margins, and references. Extracted text was also checked. The submitted PDF is byte-identical to the inspected export, and its source is the exact file used for compilation.

## Eligibility, earlier submission, and integrity

`eligibility.json` records live unsolved metadata, all-state PR history, and exact-ID search. The only earlier solution identified was PR35, initially merged then removed by re-audit commit `541cf4fb`; no newer repair was found. `../PRIOR_SUBMISSION.md` gives the required error account with immutable sources. The old Lean source, report, and README were compared between their initial commit and the snapshot immediately before removal and were identical.

The bilingual source copy matches the repository conjecture exactly. All changes are confined to `solutions/00000000747/C0ldSmi1e_submission_20261004070740/`. `SHA256SUMS.json` covers every other submission file and was checked against the exact staged Git bytes before publication.
