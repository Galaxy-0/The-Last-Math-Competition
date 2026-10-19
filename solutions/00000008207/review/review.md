# Solution Review — Conjecture 00000008207 (PR 1032)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261017194500`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008207; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its self-contained core-Lean setup (no Mathlib dependency) and its toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Classical.choice`, `Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** The LaTeX source compiled cleanly with `pdflatex` and regenerated the PDF. The submitted auxiliary code ran successfully: `VERIFY.sh`, `build_pdf.sh`, `independent-review/independent.py`, `verify.py`.

## Semantic audit

**Conjecture as filed.** Definition: The Clifford correspondence between irreducible representations of an inverse monoid M and representations of its unit group G(M): the fiber structure at the level of equivalence classes of the restriction map to G(M). Conjecture: The image of the restriction map consists exactly of the irreducible representations of G(M) fixed by the centralizer action of the maximal group congruence class; every fiber has cardinality exactly 2^k, where k is the number of non-group congruence components in the Rees quotient chain of M; and the smallest example where the correspondence fails for general monoids is the four-point truncation of the full transformation monoid, whose fibers exhibit a non-power branch count of 3. (inverse monoid Clifford power-of-two fibers) **Decisive results.** `classification`, `finite_injection_bound`, `six_not_power_two`, `conjecture8207_false`, `standard_zero_iff`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the negation of the filed statement, so the submission is a complete disproof.

## Disposition

APPROVED — merged as PR 1032.
