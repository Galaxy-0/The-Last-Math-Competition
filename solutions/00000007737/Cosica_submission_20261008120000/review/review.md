# Solution Review — Conjecture 00000007737 (PR 843)

**Submission:** Cosica — `Cosica_submission_20261008120000`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-08

## Checklist results
- Conjecture read: yes — for the `k`-fold free multiplicative convolution `μ_k` of the uniform law `ν` on `[0,1]`, the source asserts the lower support endpoint `x_k = exp(−2k+2)·k^{2k/(k−1)}` (together with density-exponent and Stieltjes-transform clauses).
- Change scope: only `solutions/00000007737/Cosica_submission_20261008120000/` was added; the conjecture is unsolved in the base metadata.
- LaTeX: `proof.tex` read in full. The argument is complete: at `k = 2` the formula gives `x_2 = 16/e² > 1`, but the support of a free multiplicative convolution of laws on `[0,1]` is contained in `[0,1]`, so `x_2 ≤ 1` — a contradiction.
- Lean build: Lean 4.33.1, Mathlib v4.33.1 (`0df444a360eaa60ab8c11dca51a86af692955474`). `lake build` exit 0 (`8708 jobs`). No `sorry`/`native_decide`/extra axiom.
- Forbidden content: none.
- Axioms: `conjecture_00000007737_endpoint_false`, `positiveProduct_law_refutes_endpoint`, and `conjecturedEndpoint_two` depend only on `[propext, Classical.choice, Quot.sound]`.

## Semantic audit
The report uses the standard operator realization of free multiplicative convolution: for free positive contractions `a, b` with distribution `ν`, the distribution of `c = a^{1/2} b a^{1/2}` is `ν ⊠ ν`. Lemma `contraction` shows `c` is a positive contraction because `a^{1/2}ba^{1/2} = (b^{1/2}a^{1/2})^*(b^{1/2}a^{1/2})` and `0 ≤ a^{1/2}ba^{1/2} ≤ a ≤ 1`. Hence the spectrum, and therefore the support of any scalar spectral law of `c`, lies in `[0,1]`, so the lower endpoint is at most `1`.

The Lean project formalizes this operator core using Mathlib's C*-algebras and continuous functional calculus: `positiveProduct_nonneg`/`positiveProduct_le_one` (`0 ≤ c ≤ 1`), `positiveProduct_spectrum_subset` (`σ_ℝ(c) ⊆ [0,1]`), `spectralLaw_support_subset`/`spectralLaw_support_nonempty`, `claimedEndpoint_gt_one` (`1 < 16/exp 2`, via the certified bound `exp 1 < 3`), `conjecturedEndpoint_two` (substitution into the displayed formula), and the combined `conjecture_00000007737_endpoint_false`. The report explicitly notes that the Lean project does not itself define the free-convolution operation; the identification of the free-product spectral law with `ν ⊠ ν` is supplied at the level of the standard definition (with a citation to Ji). Because the formal operator statement is universal (it needs neither freeness nor uniformity), it applies to the defining realization.

## Issues found
- The free-probability bridge (identification of `μ_2` with the distribution of `a^{1/2}ba^{1/2}`) is argued in the report and cited, but is not itself formalized. This is a reasonable and standard boundary for the formalization and does not affect the validity of the disproof.

## Verdict rationale
The counterexample is mathematically decisive: the conjectured formula is impossible already at `k = 2`, and the disproof of one conjunct disproves the conjecture. The Lean formalization rigorously establishes the analytic core with only the three standard axioms.

## Disposition
APPROVED — ready to merge (PR 843).
