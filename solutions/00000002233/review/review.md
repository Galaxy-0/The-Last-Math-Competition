# Solution Review — Conjecture 00000002233 (PR 559)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004223000`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read in full from `conjectures/00000002233.md`: "the zero density of the shifted difference of an integer-order entire function has the explicit lower bound T(r,f)·(1−ε)". No SOURCE.md; `verification/original.md` is byte-identical (`diff` clean) to the official file.
- LaTeX `proof.tex` read in full; independently rebuilt with `latexmk -pdf` (pdflatex): compiles cleanly; NFKC/whitespace-normalized pypdf extraction of shipped vs rebuilt PDF matches exactly (2240 = 2240 chars).
- Fresh `lake build` on Lean v4.19.0, Mathlib pinned at c44e0c8e: **Build completed successfully**, 2794 targets, zero errors, one harmless lint warning (simpa style).
- Axiom audit: 6 `#print axioms` lines (`entire`, `zero_free`, `integer_order`, `weighted_count_zero`, `characteristic_positive`, `arbitrarily_large_failure`) — all `[propext, Classical.choice, Quot.sound]` only.
- Grep for `sorry`, `native_decide`, `axiom` declarations, `unsafe`, `@[implemented_by]`, `extern`, `admit`: no hits.
- Auxiliary code: none; the characteristic integral and zero-freeness were re-verified numerically in python (T(r, e^z) = r/π to machine precision at r = 1, 2.5, 10; e−1 ≈ 1.718 ≠ 0).
- `metadata.csv` on main marks 00000002233 neither proven nor disproven (unsolved).

## Semantic audit
The conjecture asserts, for integer-order entire functions, a Bank–Lang-type explicit lower bound T(r,f)·(1−ε) on the zero density of the shifted difference. The submission disproves it with the simplest possible witness inside the stated class: f(z) = e^z has genuine maximum modulus M(r) = e^r (proved with both the Cauchy–Schwarz-type bound and attainment at the real point r), so its limsup order is exactly 1 — an integer, matching the conjecture's hypothesis. The shifted difference with the nonzero real shift c = 1 is Δ₁f(z) = e^{z+1} − e^z = (e−1)e^z; since e ≠ 1 (proved from Real.exp_lt_exp) and the exponential never vanishes, Δ₁f is globally zero-free, non-identically-zero, and 1 is not a period of f — so the counterexample survives even under a "non-period shift" or "nonzero difference" reading. Consequently every zero count is zero: the formalization proves the zero set of every disk is empty, and `weighted_count_zero` shows the finite count vanishes for *every* weight function — a quantification that covers genuine multiplicity weights — and the integrated Nevanlinna-style count ∫₀^r n(t)/t dt is zero as well.

On the other side of the proposed inequality, the submission uses the genuine Nevanlinna characteristic of an entire function (no pole-counting term): T(r,f) = (1/2π)∫ log⁺|e^{re^{iθ}}| dθ, with the integrand simplified to max(0, r cos θ), and proves strict positivity for every r > 0 via continuity and a positive point value at θ = 0. I re-verified numerically that T(r, e^z) = r/π. The proposed bound would require 0 = N(r,0;Δ₁f) ≥ T(r,f)(1−ε) = ½T(r,f) > 0 with ε = 1/2, which is impossible at every positive radius — and since the difference is globally zero-free, the failure holds for every ε < 1 and for raw or normalized zero-density readings alike. `arbitrarily_large_failure` additionally shows the failure occurs beyond every prescribed radius R, matching the usual "for all large r" formulation of such bounds. Neither the English nor the Chinese version of the conjecture excludes zero-free shifted differences, exponential-type functions, or this shift.

The formalization uses genuine definitions throughout — real sSup maximum modulus with attainment, the standard limsup order, an actual Finset of zero points obtained from a finiteness proof of an empty set, interval integrals for the integrated count, and the actual angular proximity integral with `intervalIntegral.integral_pos` — and the report's mathematics matches the Lean theorems step by step. The scope paragraph correctly limits the claim to the unqualified bound as written and does not dispute Bank–Lang results carrying additional hypotheses.

## Issues found
None blocking. (One non-fatal lint warning.)

## Verdict
APPROVED. The submission disproves the conjecture's unconditional lower bound with an explicit, fully verified counterexample — the integer-order entire function e^z whose shifted difference (e−1)e^z is provably zero-free while T(r,f) = r/π > 0 — with all mechanical checks passing and every numerical claim independently re-verified.
