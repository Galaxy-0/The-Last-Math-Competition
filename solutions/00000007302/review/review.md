# Solution Review — Conjecture 00000007302 (PR 1014)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261012234103`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007302; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its pinned Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` and its toolchain `v4.19.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Classical.choice`, `Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** The LaTeX source compiled cleanly with `pdflatex` and regenerated the PDF. The following are audit drivers that expect command-line arguments and were not rerun standalone: `evidence/assembly/assemble_package.py`, `evidence/reviews/recheck_engineering.py`, `verification-tools-v2/check_audit_graph.py`, `verification-tools-v2/test_hardening.py`, `verification-tools-v2/verify.py`.

## Semantic audit

**Conjecture as filed.** Definition: The tensor nuclear norm as the convex envelope of low-rank tensors. Conjecture: The density of extreme points of the nuclear-norm ball holds, and the combination of the density is the parameter space of rank-one decompositions. (rank-one-parameter nuclear-ball extreme density) **Decisive results.** `zero_not_mem_closure_extremePoints`, `nuclear_extremePoints_not_relatively_dense`, `nuclear_ball_counterexample`, `ordinaryDecomposition_exists`, `closedBall_not_subset_closure_extremePoints`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the negation of the filed statement, so the submission is a complete disproof.

## Disposition

APPROVED — merged as PR 1014.
