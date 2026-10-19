# Solution Review — Conjecture 00000006685 (PR 1028)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261015195500`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000006685; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its self-contained core-Lean setup (no Mathlib dependency) and its toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Classical.choice`, `Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** The LaTeX source compiled cleanly with `pdflatex` and regenerated the PDF. The submitted auxiliary code ran successfully: `build_pdf.sh`, `review/independent_check.py`, `verify.py`, `verify.sh`.

## Semantic audit

**Conjecture as filed.** Definition: Power cells with the partition structure of weight points. Conjecture: The three-dimensional adjacency graph is planar and the dual is a regular triangulation, the planar exception being degenerate weights. (planar adjacency graph of power cells) **Decisive results.** `finite_counterexample_certificates`, `decomposition_bound`, `twenty_dart_bound`, `four_cycle_classification_table`, `no_seven_faces`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the negation of the filed statement, so the submission is a complete disproof.

## Disposition

APPROVED — merged as PR 1028.
