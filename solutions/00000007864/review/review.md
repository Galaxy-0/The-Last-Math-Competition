# Solution Review — Conjecture 00000007864 (PR 677)

**Submission:** Jackmeson1 — `solutions/00000007864/Jackmeson1_submission_20261005105010`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (English + Chinese); `conjecture.md` byte-identical to the official file.
- **LaTeX report:** read in full; independently rebuilt with `latexmk` — exit 0.
- **PDF match:** normalized text of shipped vs. rebuilt PDFs differs only in math-glyph extraction artifacts (−, √, {, →, π). Content identical.
- **Lean build:** `lake build` succeeded, 8708 jobs, zero errors, zero warnings.
- **Axioms:** independent scratch `Check.lean` for `conjecture_7864_false`, `law_menOpt_eq_uniform`, `exists_menOptimal`, `deficit_div_tendsto`, `bits_version`: all exactly `[propext, Classical.choice, Quot.sound]`.
- **Cheating scan:** clean.
- **Auxiliary code:** none shipped.
- **Semantic audit:** pass (see below).
- **Sources:** Gale–Shapley quotations match the cited Wikipedia article; only the submission folder is added; metadata marks the conjecture unsolved.

## Semantic audit

The conjecture's refuted clause is "deficit constant c* = π²/6", where the deficit is D_n = n log n − H(σ_m) for the men-optimal stable matching σ_m under uniform n×n preferences. The submission proves the clause false under every conceivable reading (limit, limsup, liminf, asymptotic equivalence) by proving something much stronger: σ_m is exactly uniformly distributed on S_n, so H(σ_m) = log n! and D_n/n → 1, whereas π²/6 ≈ 1.6449 > 1 (Lean proves 1 < π²/6 from π > 3).

The uniformity argument is a genuinely two-line symmetry argument, and the Lean formalizes all of it. Renaming the women by τ transports profiles (P ↦ τ·P is a bijection preserving the uniform law, since every man's list is re-indexed and every woman's list is re-assigned, all still iid uniform), maps fibres of σ_m to fibres (σ_m(τ·P) = τ∘σ_m(P), proved from uniqueness of the men-optimal stable matching), and hence the law of σ_m is invariant under post-composition with every τ ∈ S_n. Transitivity of right-composition forces every point mass equal: the law is uniform. The report's D_n bounds are then standard: D_n ≤ n from n!/n^n ≤ e^n (Mathlib), and D_n ≥ n − 1 − (½)log n from Mathlib's antitone Stirling sequence, giving the squeeze D_n/n → 1.

The foundational part is not hand-waved: the submission re-proves in Lean that every profile has exactly one men-optimal stable matching (Gale–Shapley via a maximal rejected-pairs set with two invariants; the injectivity and optimality steps are the textbook argument), defines blocking/men-optimality faithfully (both prefer each other; man-wise best among stable matchings), and formalizes entropy as ∑ −p log p on the pushforward PMF. Rank bijections model strict preference lists, so the uniform law on profiles is the uniform law on preference profiles. The base-2 corollary (D_n/n → 1/ln 2 ≠ π²/6) rules out a logarithm-convention rescue.

The report is transparent about scope: the linear-deficit clause D_n = Θ(n) is TRUE and its truth follows from the submission's own bounds; the longest-increasing-subsequence clause is not addressed; the conjecture falls as a conjunction through its false constant clause. A remark also handles a marginal-entropy reading (deficit would be 0). No reading under which c* = π²/6 survives is known or conceivable after exact uniformity.

Sanity check: for n = 2 the men-optimal matching is uniform on S₂ by direct inspection of the 2⁴ = 16 profiles, and D_2 = 2 log 2 − log 2 = log 2 ≤ 2 ✓.

## Issues found

- None material. The uniformity theorem makes the constant clause fail so decisively that no alternative formalization could rescue it.

## Verdict

APPROVED. A complete Lean proof of exact uniformity of the Gale–Shapley men-optimal outcome under uniform iid preferences, decisively refuting the c* = π²/6 clause with faithful definitions; the build and independent axiom audit are clean.
