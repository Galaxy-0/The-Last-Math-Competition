# Solution Review — Conjecture 00000000209 (PR 1045)

**Submission:** zbw123456 — `zbw123456_submission_20261013154916`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000209; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its self-contained core-Lean setup (no Mathlib dependency) and its toolchain `v4.19.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** No auxiliary program was submitted.

## Semantic audit

**Conjecture as filed.** Definition: Gijswijt's sequence: a(1) = 1; a(n) is the largest k such that the word formed by the first n−1 terms can be written as Y^k. Conjecture: The digit 5 occurs in the sequence (4 is known to first occur at term 220; the first occurrence of 5 is estimated to be astronomically large). **Decisive results.** `exact_formula`, `no_five`, `no_rule_solution_contains_five`, `counterexample`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the negation of the filed statement, so the submission is a complete disproof.

## Disposition

APPROVED — merged as PR 1045.
