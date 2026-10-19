# Solution Review — Conjecture 00000004091 (PR 1022)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261014194500`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000004091; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its self-contained core-Lean setup (no Mathlib dependency) and its toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Classical.choice`, `Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** The LaTeX source compiled cleanly with `pdflatex` and regenerated the PDF. The submitted auxiliary code ran successfully: `empirical.py`, `review/independent.py`, `verify.sh`. The following are audit drivers that expect command-line arguments and were not rerun standalone: `build_pdf.sh`.

## Semantic audit

**Conjecture as filed.** Definition: The unordered configuration space Conf_n(X) is the quotient space of n pairwise distinct points on X. Conjecture: For a graph Gamma the first Betti number of Conf_n(Gamma) is invariant under barycentric subdivision and is a polynomial in the chromatic number of the graph of degree exactly n. (subdivision invariance of graph configuration Betti numbers) **Decisive results.** `square_not_zero_dimensional`, `segment_cycle_iff`, `square_cycle_iff`, `no_fewer_than_two`, `conjecture_00000004091_false`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the negation of the filed statement, so the submission is a complete disproof.

## Disposition

APPROVED — merged as PR 1022.
