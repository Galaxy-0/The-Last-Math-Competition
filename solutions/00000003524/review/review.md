# Solution Review — Conjecture 00000003524 (PR 780)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005232102`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

**Kind:** DISPROOF. **Conjecture:** stationary intersection reflection lower bound closure.

## Checklist results

- **Official conjecture.** `conjectures/00000003524.md` read in full (bilingual); the submission's `conjecture.md` copy is byte-identical to it.
- **LaTeX report.** `proof.tex` read in full; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory (exit 0). Extracted text of shipped and rebuilt PDFs agrees after whitespace normalization; residual differences are font/ToUnicode glyph artifacts only (ligatures, math symbols such as ∑, ‖·‖, ≥), not content.
- **Lean build.** `lake build` with toolchain v4.33.1 / Mathlib `0df444a360` (prebuilt package pool via `.lake/packages` symlink): exit 0, zero errors. No warnings.
- **No cheating.** Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, declared `axiom` over all `.lean` files: clean. `#print axioms` re-run independently (`lake env lean Axioms.lean`) for every decisive theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- **Auxiliary code.** `verification/` contains the build log, axiom output and a SHA-256 manifest; all entries verify against the extracted files (matching after CRLF normalization, consistent with the submitter's Windows build environment). Self-reported build/axiom outputs agree with my independent runs. No other executable auxiliary code is shipped.
- **Semantic audit.** Pass; details below.

## Semantic audit

The first clause of the conjecture — 'the intersection of stationary sets is stationary' — is a definite, literal, and false statement, and the submission refutes it with the Ulam matrix, formalized with Mathlib's own `IsClub`/`IsStationary` on `(ω₁).ToType`: for each a pick an injection fₐ on the initial segment below a (countable); the row A(n,b) = {a > b : fₐ(b) = n} covers the final segment Ioi b as n ranges over ℕ; Ioi b is stationary (its complement is bounded, and ω₁ is uncountable); the countable-union criterion for stationarity (cofinality ω₁ ≠ ℵ₀) makes some A(N(b), b) stationary; and N : ω₁ → ℕ is not injective, so N(b) = N(b') = n for distinct b, b', whereupon A(n,b) ∩ A(n,b') = ∅ by injectivity of fₐ above b. `∅` is not stationary since ω₁ is club. The hypotheses for ω₁ (uncountable, countable initial segments, cofinality ℵ₁) are each proved from Mathlib's cardinal API.

Two features make the semantic handling exemplary. First, since the conjecture is a conjunction whose second clause ('the reflection of stationarity bounded below closure') has no standard meaning, the main theorem proves `¬ (StationaryInterClaim ∧ Q)` for an *arbitrary* proposition Q — the conjunction fails however the second clause is read; the family form (⋂ of a nonempty family) and the intersection-of-all-stationary-sets form are refuted as well. Second, the true sibling statement — a stationary set intersected with a club set has stationary intersection — is proved as a contrast remark, demonstrating that the refutation targets exactly what the text says ('stationary sets', plural, both operands stationary) and not a nearby true statement.

I checked the classical content (Ulam's partition of ω₁ into disjoint stationary sets; the countable-cofinality exception is what makes the literal clause false at ω₁) and the use of `isStationary_iUnion_iff_of_countable` with the correct cofinality hypothesis. The general version for any uncountable well-order with countable initial segments and uncountable cofinality is a clean strengthening with no cost to faithfulness.

## Issues found

None material.

## Verdict

APPROVED. A decisive, fully machine-checked disproof of the literal clause by two explicitly constructed disjoint stationary subsets of ω₁, with the vague second clause neutralized for all readings and the true nearby statement proved as contrast.
