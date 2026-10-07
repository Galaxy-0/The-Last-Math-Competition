# Solution Review — Conjecture 00000008458 (PR 819)

**Submission:** earthking11 — `solutions/00000008458/earthking11_submission_20261007004618`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (`conjectures/00000008458.md`, bilingual). Content: "Definition: Quasi-alternating means Khovanov homology width 1. Conjecture: Alternating links are always quasi-alternating; the smallest quasi-alternating nonalternating link has crossing number 11 and homological width exactly 2."
- **LaTeX rebuild:** pass — two pdflatex passes succeed; 1 page.
- **PDF comparison:** pass — rebuilt vs shipped text similarity 0.9938; the only differences are whitespace extraction artifacts ("homology ." vs "homology."), no content divergence.
- **Lean build:** pass — `lake build` zero errors under the pinned Lean 4.33.1. Note: despite the listing metadata ("Mathlib project"), the project declares no Mathlib dependency; it is a self-contained core-Lean development (`lake-manifest.json` has an empty package list). This is fine and matches BUILD_AUDIT.md.
- **Axioms:** pass — `Tlmc8458.no_stated_smallest_example` and `Tlmc8458.source_claim_false` depend on **no axioms at all**; no `sorry`, `native_decide`, `unsafe`, or custom `axiom` anywhere.
- **Auxiliary code:** none — no scripts shipped; `BUILD_AUDIT.md` claims (toolchain, empty dependency list, zero-error build, axiom-free theorems) all independently reproduced.
- **Semantic audit:** pass — see below.
- **Source statement ground truth:** pass.

## Semantic audit

The statement's definition sentence fixes QA(K) ⟺ width(K) = 1 (single, unqualified width invariant; no reduced/unreduced distinction is introduced in the source). Its second clause asserts a smallest QA nonalternating link of crossing number 11 with homological width exactly 2. Because that link is QA, the same width invariant must equal both 1 and 2 — the clause is unsatisfiable, independent of any link theory. The submission's Lean formalization matches the official text exactly: `SourceClaim` = (alternating ⟹ width 1) ∧ ∃K (width K = 1 ∧ ¬alternating K ∧ crossingNumber K = 11 ∧ width K = 2 ∧ minimality); the decisive theorem `source_claim_false` is its exact negation, proved with zero assumptions about the primitives (arbitrary `Link` type, arbitrary functions). Since the negation holds under every interpretation of the primitives, this is not a toy instantiation — it is maximally general, and the contradiction is derived from the statement's own clauses, not from any smuggled hypothesis. No deep theorem is assumed as a hypothesis.

The refutation is of the statement as written: the underlying "intended" mathematics (standard Ozsváth–Szabó quasi-alternating links, for which the smallest QA nonalternating example having crossing number 11 and Khovanov width 2 is plausible known material) is a different, non-self-contradictory claim that would need the two-width or standard-definition reading the source does not provide. The submission explicitly acknowledges this boundary in both README and solution.tex. Under this competition's ground-truth-by-official-text convention, the conjunction as published is false, and this submission proves exactly that.

## Issues found

- None material. Observation: the refutation exploits an internal inconsistency of the published wording (the "width exactly 2" clause versus the "width 1" definition), not the mathematics of Khovanov homology; a reworded conjecture would be unaffected. The submission says so plainly.

## Verdict

**APPROVED** as a valid disproof of conjecture 00000008458 as officially stated: zero-assumption, kernel-checked Lean refutation of an internally inconsistent conjunction, with an honest and accurate report.
