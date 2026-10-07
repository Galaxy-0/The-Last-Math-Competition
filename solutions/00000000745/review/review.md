# Solution Review — Conjecture 00000000745 (PR 739)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005193437`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000000745.md` read in full (English + Chinese). Shipped `conjecture.md` is byte-identical to it (`diff` clean).
- LaTeX: full `proof.tex` read; `latexmk -pdf -interaction=nonstopmode` rebuild in a scratch dir succeeds (exit 0). pypdf text comparison of shipped vs rebuilt PDF matches after normalizing extraction artifacts only (∏ glyph mapping, `\texttt` underscores, ligature ff, spacing); no content discrepancy.
- Lean: clean `lake build` succeeds with zero errors and zero warnings (Lean v4.33.1, Mathlib v4.33.1, 8708 jobs).
- Axioms: independent `lake env lean Check.lean` on `conjecture745_false`, `julia_facts`, `chordal_eq_dist`, `norm_multiplier_le`, `fatouSet_eq_univ` — all report only `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `native_decide`, `extern`, `unsafe`, `implemented_by`, or declared `axiom` anywhere (`lean/Axioms.lean` contains only `#print axioms` commands).
- Aux code: `verification/axioms.txt` matches the independent axiom run; `verification/build.txt` consistent with a successful fresh build. Note: `verification/SHA256SUMS.txt` has stale entries (`conjecture.md`, `lean/Conjecture745/Basic.lean`) — both files verified directly (byte-identical official copy; clean rebuild), packaging hygiene only.
- Metadata: `metadata.csv` at the PR base commit lists `00000000745` as unsolved; the PR adds only the solution folder.

## Semantic audit

The conjecture states that the Julia set (repelling points) of x² − 1 on ℤ₂ has Hausdorff dimension 1 and open dense complement in the 2-adic topology. The submission proves the negation of this conjunction: for each of four standard readings of "the Julia set (repelling points)" — (J1) complement of the equicontinuity Fatou set, (J2) points of non-equicontinuity of the iterate family, (J3) periodic points of positive period with multiplier of 2-adic norm > 1, (J4) the closure of (J3) — the set is empty. Hence its Hausdorff dimension is 0 (Mathlib `dimH_empty`), not 1, so the dimension clause fails (the complement clause holds trivially, the complement being all of ℤ₂).

The formalization is faithful to the conjecture's own objects. The space is Mathlib's `PadicInt 2` with its 2-adic metric, the map is exactly f x = x² − 1, and the definitions follow the nonarchimedean dynamics literature cited in the paper (equicontinuity-based Fatou/Julia sets after Benedetto–Lee; "repelling" = multiplier norm > 1; the closure characterization from complex dynamics). The derivative is taken on ℚ₂ for the same polynomial, with the coercion ℤ₂ → ℚ₂ proved to intertwine f and g — the standard device, since ℤ₂ is not a field. The chordal-metric alternative on ℙ¹(ℚ₂) is shown to coincide with the 2-adic metric on ℤ₂, closing the last definitional gap. No deep theorem is assumed anywhere and no toy surrogate is used.

The mathematics is airtight. On ℤ₂ the ultrametric gives |x+y|₂ ≤ 1, so f(x) − f(y) = (x−y)(x+y) makes f 1-Lipschitz; hence every iterate is 1-Lipschitz, the family {fⁿ} is uniformly equicontinuous, and the Fatou set is everything (J1, J2 empty). For (J3), the chain rule gives (gⁿ)′(x) = ∏_{i<n} 2·g^{i}(x), and since g^{i}(x) ∈ ℤ₂ each factor has norm ≤ |2|₂·1 = 1/2, so the multiplier norm is ≤ 2⁻ⁿ < 1 for n ≥ 1 — no point of ℤ₂ is repelling for any positive period, so J3 and its closure J4 are empty. I verified the Lipschitz property independently on random samples of ℤ/4096 (v₂(f(x)−f(y)) ≥ v₂(x−y) always), and note that x² − x − 1 = 0 has no solution even mod 2, so f has no fixed points in ℤ₂ whatsoever — the emptiness conclusions are even stronger than needed. Under the alternative convention dim_H ∅ = −∞ the dimension clause still fails, as the paper remarks. This is a genuine counterexample-free structural refutation: the conjecture's premise about the shape of the dynamics is simply false for this map on this space.

## Issues found

None blocking. (Minor, non-blocking: stale SHA-256 entries in `verification/SHA256SUMS.txt` for `conjecture.md` and `lean/Conjecture745/Basic.lean`; both verified directly.)

## Verdict

APPROVED. The submission correctly shows that x² − 1 is 1-Lipschitz (indeed non-expanding) on ℤ₂ with all multipliers of 2-adic norm < 1, so under every standard reading of "Julia set (repelling points)" the set is empty, its Hausdorff dimension is 0 rather than 1, and the conjecture's conjunction is false. The formalization is faithful, the build is clean, the axiom audit shows only the three standard axioms, and the paperwork matches the code.
