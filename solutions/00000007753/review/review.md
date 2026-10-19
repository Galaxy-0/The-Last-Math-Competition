# Solution Review — Conjecture 00000007753 (PR 1046)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261018191312`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-19

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007753; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, or metadata file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; the rendered report matches the submitted PDF.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources, keeping its own module names, its own `lakefile`, its self-contained core-Lean setup (no Mathlib dependency) and its toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** `#print axioms` was run against every declaration exported by the submission's own modules. The transitive axiom set is contained in {`Classical.choice`, `Quot.sound`, `propext`}; no `sorryAx` is reachable.
- **Auxiliary code.** No auxiliary program was submitted.

## Semantic audit

**Conjecture as filed.** Definition: The dynatomic polynomial Phi_{n,c}(x) = prod_{d|n} (f_c^d(x)-x)^{mu(n/d)} defines points of exact period n for f_c(x)=x^2+c; the Galois group of its special value Phi^*_{n,c}=Phi_{n,c}(0) is G_n. Conjecture: For all n>=1 with irreducible polynomial, G_n is S_n for odd n or a transitive subgroup of S_n containing an odd permutation for even n; and the exceptional parameters c making the polynomial reducible are finite in number for fixed n, at most 2^{n-1}. (dynatomic Galois classification) **Decisive results.** `root_not_unit`, `bound_at_one`, `exceptional_parameter_bound_false`. Read against the filed statement, the definitions formalise the quantities named in the conjecture text, and the decisive theorems are stated over those same definitions with no strengthening, weakening or renaming, so the formalisation is a faithful reading. The decisive theorems establish the negation of the filed statement, so the submission is a complete disproof.

## Disposition

APPROVED — merged as PR 1046.
