# Solution Review — Conjecture 00000000236 (PR 632)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261005113928`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (bilingual): the statement asserts the conjunction of (i) Hadamard matrices exist for every 4 | n, and (ii) D(n)/n^{n/2} → 1, with D(n) the maximum |det| over n×n ±1 matrices. Shipped `conjecture.md` is byte-identical to `conjectures/00000000236.md`.
- LaTeX: `main.tex` rebuilt independently with `latexmk -pdf` (exit 0); 4 pages in both PDFs; extracted text identical after glyph normalization (one line-break hyphenation artifact only).
- Lean: `lake build` exits 0 (warnings-as-errors configured in the lakefile); `lake env lean Check.lean` also exits 0.
- Axioms: all 22 `#print axioms` reports in `Check.lean` are exactly `[propext, Classical.choice, Quot.sound]`, including `sign_determinant_gap`, `normalizedMaximum_odd_gap`, `not_AllOrdersLimit`, `conjecture236_false`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern` in the mathematical sources.
- Auxiliary code: the auxiliary Lean inspection tools (`Inspect.lean`, `Audit.lean`) are read-only declaration/type/axiom auditors; I reproduced their essential content by running `Check.lean` directly (all types and axioms as claimed). `verification/replay-author-inspection.py` is a reproducibility harness, not a mathematical oracle.
- Integrity: 52/52 files match `verification/SHA256SUMS.json`.

## Semantic audit
The source asserts a conjunction. Clause (ii) — "D(n)/n^{n/2} → 1" — carries no divisibility restriction (the restriction to 4 | n belongs to clause (i) only, as the report itself points out), so the faithful formalization is convergence of the full sequence, which the submission states as `AllOrdersLimit : Tendsto (fun n => D n / n^{n/2}) atTop (nhds 1)` with real exponentiation. `D n` is the genuine maximum: `Finset.univ.sup'` over the entire finite type of Boolean n×n matrices, with `D_isMaximum` proving both attainment by a real ±1 matrix and domination of every real ±1 matrix (`sign_encoding_complete` shows the Boolean encoding loses nothing). `HadamardConjecture` (clause (i)) is stated faithfully but deliberately not attacked — the disproof only needs clause (ii), so `conjecture236_false : ¬ (HadamardConjecture ∧ AllOrdersLimit)` is the exact negation of the official conjunction, with no quantifier strengthening or strawman.

The mathematics is a clean, self-contained parity argument. For odd n, each Gram entry Σₖ AᵢₖAⱼₖ of a ±1 matrix is a sum of n odd terms, hence an odd integer; off-diagonal entries are therefore nonzero, so `gram_entry_sq_lower` gives |Gᵢⱼ| ≥ 1 and `gram_square_trace_lower` gives tr(G²) ≥ n(n² + n − 1). Diagonal entries are n (`gram_diag`). With λᵢ the eigenvalues of the symmetric PSD matrix G and xᵢ = λᵢ/n (`spectral_moments` supplies Σλᵢ = tr G = n² and Σλᵢ² = tr(G²)), one gets Σxᵢ = n and Σ(xᵢ−1)² = tr(G²)/n² − n ≥ 1 − 1/n ≥ 1/2. The `product_gap` lemma then shows Πxᵢ ≤ e^{−1/18}: if S = Σ(√xᵢ−1)² < 1/18 every factor satisfies √xᵢ < 2, whence (xᵢ−1)² ≤ 9(√xᵢ−1)² and Σ(xᵢ−1)² ≤ 9S < 1/2, a contradiction; and xᵢ ≤ e^{2(√xᵢ−1)} with Σ2(√xᵢ−1) = −S gives the product bound. Since det(A)² = det G = nⁿ Πxᵢ, every odd-order sign matrix satisfies (det A)²/nⁿ ≤ e^{−1/18}; applying this to a maximizer and taking square roots (`normalization_square`: (n^{n/2})² = nⁿ exactly) yields D(n)/n^{n/2} ≤ e^{−1/36} < 1 for every odd n ≥ 3.

The limit clause therefore fails: `not_AllOrdersLimit` derives from any alleged convergence an eventual lower bound above c = e^{−1/36} < 1, then instantiates at the odd order 2N+3, contradicting the uniform gap. I verified the estimates numerically: D(3)/3^{3/2} ≈ 0.770 and D(5)/5^{5/2} = 48/25√5 ≈ 0.859, both well below e^{−1/36} ≈ 0.9725, consistent with the bound; the classical Barba bound (√(2n−1)(n−1)^{(n−1)/2}, ratio → √(2/e) ≈ 0.858) confirms that odd orders genuinely stay away from 1. The disproof is an infinite-order obstruction with a fixed positive gap — a true mathematical fact, correctly formalized, and it leaves the actual Hadamard conjecture (clause (i)) untouched.

## Issues found
- None blocking. The report is explicit that only the second clause is refuted and makes no claim against Hadamard existence.

## Verdict
APPROVED. Fresh LaTeX and Lean builds pass; axioms are exactly the standard three; the parity/spectral gap argument is mathematically sound and numerically corroborated; and the formalized statement is the exact literal negation of the source conjunction — clause (ii), as printed without any order restriction, is false because D(n)/n^{n/2} ≤ e^{−1/36} < 1 at every odd order.
