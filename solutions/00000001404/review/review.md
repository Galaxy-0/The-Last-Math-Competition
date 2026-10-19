# Solution Review — Conjecture 00000001404 (PR 1042)

**Submission:** zbw123456 — `zbw123456_submission_20261018021000`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001404; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its pinned Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` and its toolchain `v4.19.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** The LaTeX source compiled cleanly with `pdflatex` and regenerated the PDF. The following are audit drivers that expect command-line arguments and were not rerun standalone: `verify.sh`.

## Semantic audit

**Conjecture as filed.** Definition: The smooth 4-dimensional Poincaré conjecture asks whether every smooth homology 4-sphere is diffeomorphic to S⁴. Conjecture: There exists an invariant θ of smooth homology 4-spheres, valued in a countable abelian group, additive under connected sum (θ(M#N) = θ(M) + θ(N)), with θ(S⁴) = 0; if some M has θ(M) ≠ 0, the smooth Poincaré conjecture fails. **Decisive results.** `conjecture`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the conjecture, so the submission is a complete proof.

## Disposition

APPROVED — merged as PR 1042.
