# Solution Review — Conjecture 00000000023 (PR 1018)

**Submission:** idealistichacker — `idealistichacker_submission_20261013063212`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000023; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its pinned Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474` and its toolchain `v4.33.1`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Classical.choice`, `Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** The LaTeX source compiled cleanly with `pdflatex` and regenerated the PDF. The submitted auxiliary code ran successfully: `tests/test_reproduce.py`. The following are audit drivers that expect command-line arguments and were not rerun standalone: `reproduce.py`.

## Semantic audit

**Conjecture as filed.** Conjecture: The number of solutions of the S-unit equation x+y=1 is polynomially controlled: there exists an absolute constant C such that the number of solutions is at most C·|S|². **Decisive results.** `coprimePairs_card_lower_bound`, `witness_lower_bound`, `no_uniform_quadratic_bound`, `bounded_integer_in_unit_group`, `no_generated_unit_quadratic_bound`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the negation of the filed statement, so the submission is a complete disproof.

## Disposition

APPROVED — merged as PR 1018.
