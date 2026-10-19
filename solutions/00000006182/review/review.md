# Solution Review — Conjecture 00000006182 (PR 1031)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261017194000`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000006182; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its self-contained core-Lean setup (no Mathlib dependency) and its toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Classical.choice`, `Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** The LaTeX source compiled cleanly with `pdflatex` and regenerated the PDF. The submitted auxiliary code ran successfully: `VERIFY.sh`, `build_pdf.sh`, `independent-review/independent.py`, `verification/independent.py`.

## Semantic audit

**Conjecture as filed.** Definition: Strictly balanced subgraphs are graphs where every proper subgraph has lower density, with the extremal structure of expectations. Conjecture: The conversion constant is the explicit ratio of balanced densities, and the expectation is monotone for strictly balanced subgraphs; the extremal point is unique and exactly the threshold itself; and two strictly balanced subgraphs share the threshold if and only if their densities are equal, in which case the expectation ratio is constant. (monotone extremal conversion of strictly balanced expectations) **Decisive results.** `triangle_expectation_formula`, `square_expectation_formula`, `no_constant_ratio`, `conjecture_6182_constant_ratio_disproved`, `no_constant_in_any_characteristic_zero_field`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the negation of the filed statement, so the submission is a complete disproof.

## Disposition

APPROVED — merged as PR 1031.
