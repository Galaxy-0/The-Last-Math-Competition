# Solution Review — Conjecture 00000001870 (PR 727)

**Submission:** Jackmeson1 — `solutions/00000001870/Jackmeson1_submission_20261005163916`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000001870.md` read in full (English + Chinese). Shipped `conjecture.md` is **byte-identical** to the official file.
- LaTeX: full `proof.tex` (174 lines) read. Independently rebuilt with `latexmk -pdf` — succeeds (3 pages). Shipped vs rebuilt text compared with pypdf after normalization: 99.6% character-stream similarity; all 34 non-equal blocks are single math-glyph extraction artifacts (‖·‖, ∫, −, subscripts); no content difference.
- Lean build: `lake build` re-run — **Build completed successfully (8708 jobs), zero errors**. Lean 4.33.1, Mathlib v4.33.1 (pool rev 0df444a360).
- Axioms: fresh `lake env lean Check.lean` audit of every decisive theorem (`conjecture_1870_false`, `kappa3_not_equivalent`, `kappa3_eq_zero`, `mixed_cumulants_eq_zero`, `kappa3Re_eq_zero`, `cumulant3_linear_trace_eq_zero`, `cumulant3_linear_trace_eq_zero_right`) reports exactly `[propext, Classical.choice, Quot.sound]` in all cases. Cheating grep clean (prose hits only).
- Aux code: `verification/build.txt` and `axioms.txt` match fresh reproduction; `SHA256SUMS.txt` verifies except for `conjecture.md` and `lean/Conjecture1870/Basic.lean`, whose recorded digests match their CRLF (pre-normalization) variants exactly — contents verified intact. Non-blocking.
- Metadata: `metadata.csv` lists 00000001870 as `proven=false, disproven=false`; no solution folder on the main branch; README eligibility statement consistent.

## Semantic audit

The conjecture sets the context as "the CLT for the trace distribution of random unitary matrices (known)" and claims the third cumulant decays as N⁻¹·c₃ with c₃ = 2πi/3, the exponent 1 exact. Under the standard reading — a random unitary matrix is Haar-distributed on U(N) (the CUE) and the "trace distribution" is the law of Tr U — the third cumulant is κ₃(N) = E[X³] − 3E[X²]E[X] + 2E[X]³ for X = Tr U. The submission proves κ₃(N) = 0 for every N, negating the claim exactly.

Faithfulness. Every object is the conjecture's own: U(N) is Mathlib's `Matrix.unitaryGroup (Fin N) ℂ` with the subspace topology of the matrix space and its Borel σ-algebra; compactness is proved (closed + entrywise bounded); the Haar probability measure `haarU N = haarMeasure ⊤` is proved to be both a Haar measure and a probability measure; the trace is the actual `Matrix.trace`; the cumulant is the standard joint third cumulant from Bochner integrals of moments, with integrability of all moments E[Xᵃ(X̄)ᵇ] proved so the integrals are genuine. This is the opposite of a toy surrogate — the same objects appear in the literature on the CUE trace CLT (Diaconis–Evans).

The mathematics is a one-line symmetry argument made rigorous: −1 ∈ U(N) is central, Haar measure is invariant under U ↦ (−1)U (and under U(−1)), Tr((−1)U) = −Tr U, so X and every ℝ-linear functional of it are odd; all first and third moments and hence the whole cumulant formula vanish (`cumulant3_eq_zero_of_odd`, `cumulant3_linear_trace_eq_zero[_right]`, `kappa3_eq_zero`). This kills not only κ₃(Tr U) but every natural reading of "third cumulant of the trace distribution": κ₃(Re Tr U), κ₃(Im Tr U) via ℝ-linearity, and the mixed cumulants κ(X,X,X̄), κ(X,X̄,X̄) — all proved zero. The asymptotic negation is exact: the zero sequence is asymptotic to no eventually-nonzero sequence, so κ₃ ≁ c·N^(−α) for every c ≠ 0 and real α (`kappa3_not_equivalent`), in particular κ₃ ≁ (2πi/3)/N, and N·κ₃(N) → 0 ≠ 2πi/3 by uniqueness of limits (`conjecture_1870_false`). Independent sanity check: for N = 1, U(1) is the circle with uniform measure, E[U^k] = 0 for all k ≥ 1, so κ₃ = 0 — consistent; indeed odd cumulants of the CUE trace vanish for every N by the −I symmetry, so the conjecture (with its nonzero purely imaginary constant and "exact exponent 1") is genuinely false.

Scope is honestly stated: third cumulants of other statistics (|Tr U|², Tr U^j for even j, log det(1−U)) and other ensembles (COE, CSE) are declared out of scope; these are different statistics, not readings of "the trace distribution". The paper's claim structure matches the Lean: every theorem named in the paper exists with the stated form.

## Issues found

None blocking. (Same cosmetic SHA256SUMS CRLF note as in VERDICT.json.)

## Verdict

APPROVED. A faithful, complete, machine-checked disproof: the third cumulant of Tr U under Haar measure on U(N) is exactly 0 for every N — for all ℝ-linear functionals of the trace and all mixed variants — so it is not asymptotic to (2πi/3)/N with any exponent, and N·κ₃(N) tends to 0, not 2πi/3. Zero build errors and only the standard three axioms; the submission proves exactly the negation of the conjecture under its standard reading.
