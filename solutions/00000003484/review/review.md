# Solution Review — Conjecture 00000003484 (PR 1021)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261014194500`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000003484; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its self-contained core-Lean setup (no Mathlib dependency) and its toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Classical.choice`, `Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** The LaTeX source compiled cleanly with `pdflatex` and regenerated the PDF. The submitted auxiliary code ran successfully: `VERIFY.sh`, `verification/independent.py`.

## Semantic audit

**Conjecture as filed.** Definition: The clique tree is the tree structure of maximal cliques of chordal graphs, with clique bags the nodes. Conjecture: The bag count equals the maximal-clique count minus the Helly covering genus; the genus is zero if and only if the graph is an interval graph, with the bag count given explicitly by the recursion of clique-tree embedding counts. (clique tree bag count formula) **Decisive results.** `not_interval_endpoints`, `intersects_iff_endpoints`, `interval_iff_endpoints`, `not_interval`, `threeSun_not_interval`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the negation of the filed statement, so the submission is a complete disproof.

## Disposition

APPROVED — merged as PR 1021.
