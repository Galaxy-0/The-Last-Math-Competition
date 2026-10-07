# Solution Review — Conjecture 00000008304 (PR 820)

**Submission:** earthking11 — `solutions/00000008304/earthking11_submission_20261007005330`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (`conjectures/00000008304.md`, bilingual). Four clauses: (1) brk_pts is finite with explicit count 2^n − n − 1; (2) breakpoints are ratios of EHZ capacities; (3) the exact threshold for the infinite domain (infinitely many breakpoints at n ≥ 24) is 24; (4) below the threshold the breakpoint-set symmetry is the dual of the E8 lattice.
- **LaTeX rebuild:** pass — two pdflatex passes succeed; 1 page.
- **PDF comparison:** pass — rebuilt vs shipped similarity 0.9989; only whitespace/glyph extraction artifacts ("brk \_pts" vs "brk pts"); no content divergence.
- **Lean build:** pass — `lake build` zero errors under pinned Lean 4.33.1. As with PR 819, despite listing metadata ("Mathlib project") the project has no Mathlib dependency; it is self-contained core Lean (empty manifest package list), matching BUILD_AUDIT.md.
- **Axioms:** pass — `Tlmc8304.finite_count_conflicts_with_threshold`, `Tlmc8304.source_claim_false`, and `Tlmc8304.stated_count_at_24` depend on **no axioms at all**; no `sorry`, `native_decide`, `unsafe`, or custom `axiom` anywhere.
- **Auxiliary code:** none — no scripts shipped; BUILD_AUDIT.md claims independently reproduced.
- **Semantic audit:** pass — see below.
- **Source statement ground truth:** pass.

## Semantic audit

Clauses (1) and (3) of the official text concern the same object brk_pts(n) with the same parameter n. Clause (1) fixes its exact finite cardinality 2^n − n − 1; clause (3) makes it infinite for every n ≥ 24 ("infinitely many breakpoints at n at least 24 ... threshold is 24"). At n = 24 the set would have exactly 2^24 − 24 − 1 = 16777191 elements (arithmetic verified; kernel-checked in Lean) and be infinite — impossible. Hence the four-clause conjunction is false. The decisive theorem `source_claim_false` is parameterized over the two remaining clauses (arbitrary propositions), so the negation covers the full conjecture exactly, with no assumption about EHZ capacities, packings, or lattices; `finite_count_conflicts_with_threshold` derives the contradiction at n = 24 from bijectivity with `Fin (2^24−24−1)` versus impossibility of any bijectivity with a finite type. The quantifiers match the official text (∀ n for the count formula; ∀ n ≥ 24 for the threshold), the formalization reads the same `Breakpoints n` family in both clauses as the source does, and the negation is maximally general over the primitives — no toy instantiation and no smuggled hypothesis.

As with PR 819, this is a disproof of the statement as written: the count formula and the infinitude threshold genuinely conflict in the published text, and the submission is explicit that symplectic geometry is not formalized and cannot be repaired by the remaining clauses.

## Issues found

- None material. Observation: the refutation rests on the internal inconsistency between clause (1) (exact finite count for all n) and clause (3) (infinitely many breakpoints for n ≥ 24); a reworded conjecture (e.g., count formula below the threshold only) would be unaffected. The submission discloses this scope plainly.

## Verdict

**APPROVED** as a valid disproof of conjecture 00000008304 as officially stated: zero-assumption, kernel-checked Lean refutation of a self-contradictory conjunction, with an honest and accurate report.
