# Solution Review — Conjecture 00000006238 (PR 1025)

**Submission:** asfigh665 — `asfigh665_submission_20261015132544`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000006238; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its self-contained core-Lean setup (no Mathlib dependency) and its toolchain `v4.24.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Classical.choice`, `Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** The LaTeX source compiled cleanly with `pdflatex` and regenerated the PDF. No auxiliary program was submitted.

## Semantic audit

**Conjecture as filed.** Definition: The closed-formula lattice is the lattice-operation structure, the closed-open duality of subobjects. Conjecture: The closed-open dual difference is the open complement, the combination of completeness being the complement involution; the square of the involution is the identity, with fixed points the clopen elements; and the multiplicative deficit of the double-Boolean structure is the failure of distributivity, with failure degree 1. (complement-involution closed-open lattice operations) **Decisive results.** `no_fixed_subset`, `singleton_not_fixed`, `not_discrete_fixed_point_claim`, `not_universal_fixed_point_claim`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the negation of the filed statement, so the submission is a complete disproof.

## Disposition

APPROVED — merged as PR 1025.
