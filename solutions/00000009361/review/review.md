# Solution Review — Conjecture 00000009361 (PR 1030)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261016191700`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009361; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its self-contained core-Lean setup (no Mathlib dependency) and its toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Classical.choice`, `Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** The LaTeX source compiled cleanly with `pdflatex` and regenerated the PDF. The submitted auxiliary code ran successfully: `VERIFY.sh`, `build_pdf.sh`, `verification/independent.py`.

## Semantic audit

**Conjecture as filed.** Definition: Records of random permutations: the exchangeable structure. Conjecture: The counting of records: the records of exchangeable permutations, with the distribution of the records independent Bernoulli. (random permutation independent Bernoulli record counting distribution) **Decisive results.** `rise_bound`, `drop_bound`, `valid_iff_perm`, `bernoulli_false_factor`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the conjecture, so the submission is a complete proof.

## Disposition

APPROVED — merged as PR 1030.
