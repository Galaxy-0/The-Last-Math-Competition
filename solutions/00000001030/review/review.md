# Solution Review — Conjecture 00000001030 (PR 1013)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261012223441`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001030; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its pinned Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` and its toolchain `v4.19.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Classical.choice`, `Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** The LaTeX source compiled cleanly with `pdflatex` and regenerated the PDF. The submitted auxiliary code ran successfully: `auxiliary/check_icosahedron.py`. The following are audit drivers that expect command-line arguments and were not rerun standalone: `verification/check_audit_graph.py`, `verification/test_hardening.py`, `verification/verify.py`.

## Semantic audit

**Conjecture as filed.** Conjecture: The minimal number of points of a spherical 5-design on S² is 12 (with the icosahedron exceptional) (minimal 5-designs, Bannai's count). **Decisive results.** `ico_coordinates_iff`, `sphere_inner_neg_one_iff`, `sphere_inner_bounds`, `lpValue_eq_zero_iff`, `exists_antipode_of_squared_sum`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the conjecture, so the submission is a complete proof.

## Disposition

APPROVED — merged as PR 1013.
