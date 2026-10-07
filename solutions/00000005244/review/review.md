# Solution Review — Conjecture 00000005244 (PR 804)

**Submission:** earthking11 — `earthking11_submission_20261006124055`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-06

## Checklist results

- **Eligibility and scope.** The submission occupies only the correctly named personal folder for conjecture 00000005244; the conjecture was open in the audited metadata, and no conjecture, README, leaderboard, or metadata files were modified by the submission.
- **Report and PDF.** I read the complete LaTeX report and official conjecture. An independent LaTeX compilation succeeded, and the generated/shipped PDF was valid and text-extractable (one page unless otherwise noted).
- **Lean and auxiliary code.** A fresh Lean build succeeded. The available axiom audit was replayed or surfaced by the build and used only Lean’s standard foundational axioms (`propext`, `Classical.choice`, and/or `Quot.sound`). No `sorry`, `native_decide`, custom axiom, unsafe declaration, implementation override, or kernel bypass was present. No unrun auxiliary program was required; finite checks were independently replayed or covered by the Lean proof.

## Semantic audit

The conjecture simultaneously requires genus at least two to be irreducible (hence one component at genus two) and genus two to have two irreducible components; the formal component-count clauses are inconsistent. The Lean definitions and capstone theorem address the filed statement rather than merely assuming its desired conclusion. The report and formal source therefore establish the claimed disproof.

## Disposition

APPROVED — merged as PR 804.
