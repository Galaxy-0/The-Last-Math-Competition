# Solution Review — Conjecture 00000007762 (PR 1041)

**Submission:** zbw123456 — `zbw123456_submission_20261014104303`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007762; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its pinned Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` and its toolchain `v4.19.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Classical.choice`, `Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** The LaTeX source compiled cleanly with `pdflatex` and regenerated the PDF. The following are audit drivers that expect command-line arguments and were not rerun standalone: `verify.sh`.

## Semantic audit

**Conjecture as filed.** Definition: The depth of critical orbit relations for the quadratic family f_c: the relation polynomials R_m(c)=f_c^m(0), with compatibility of two relations f^a(0)=f^b(0) characterized by resultants of R_a, R_b. Conjecture: The depth, the longest chain of pairwise compatible nontrivial critical relations, is unbounded but grows at most to 3, i.e. no chain of more than three pairwise compatible nontrivial critical relations exists; the assertion is equivalent to PCF parameters producing no new Gleason polynomial factors after cubic relations. (depth-3 chain bound) **Decisive results.** `no_depth_three_bound`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the negation of the filed statement, so the submission is a complete disproof.

## Disposition

APPROVED — merged as PR 1041.
