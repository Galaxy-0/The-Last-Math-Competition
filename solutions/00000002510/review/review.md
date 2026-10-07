# Solution Review — Conjecture 00000002510 (PR 771)

**Submission:** Jackmeson1 — `solutions/00000002510/Jackmeson1_submission_20261005220423`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (English + Chinese, `conjectures/00000002510.md`; the Chinese text is garbled but adds nothing beyond the English); shipped `conjecture.md` is **byte-identical** to the official copy.
- **LaTeX:** entire `proof.tex` (163 lines) read; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` (build succeeds). pypdf comparison shipped vs rebuilt: identical alphanumeric content after normalizing font-extraction artifacts (`‖·‖` norm bars extracted as letters `k`, set braces `\{ \}` as `f…g`, `∈` as `2`, ligatures); no words, formulas or claims differ.
- **Lean build:** `lake build` succeeds with zero errors and zero warnings — Lean **v4.33.1**, Mathlib **v4.33.1** (pool rev `0df444a360`). Matches the shipped `verification/build.txt`.
- **Axioms:** no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. Independent `#print axioms` for `C2510.conjecture_2510` and `C2510.W_no_best_approx`: only `[propext, Classical.choice, Quot.sound]` — matches the shipped `verification/axioms.txt`.
- **Aux code:** no aux scripts shipped; shipped verification outputs re-derived (build log, axiom printout). `SHA256SUMS.txt` text-file mismatches are the commit-time CRLF→LF normalization artifact (verified byte-wise in the sibling submission); binary files pass. Cosmetic only.
- **Metadata:** `metadata.csv` lists 00000002510 as unsolved; the PR adds only its own submission folder.

## Semantic audit

The conjecture states that the existence of best low-rank approximations is governed by closure defects: unlike matrices, the set of bounded-rank tensors is not closed, and approximation fails via limiting divergence. The submission fixes the vague meta-claim into four precisely scoped claims (R1–R4), states the scoping explicitly (it does not claim non-closedness for every rank — impossible, since rank ≤ 0 is `{0}`), and proves all four in Lean over the genuine objects: real `Fin 2 → Fin 2 → Fin 2 → ℝ` tensors with the sup norm, CP tensor rank via rank-one decompositions, and Mathlib's `Matrix.rank` for the contrast.

(R1) is proved for all m, n, r via the linear map M ↦ (v ↦ Mv), continuity in finite dimension, Mathlib's `isOpen_setOfPred_nat_le_rank`, giving closedness of the rank-≤r locus, hence existence of best matrix approximations. (R2) is the clean general criterion `bestApprox_forall_iff_isClosed` for nonempty subsets of proper spaces, instantiated at `rankLE r`. (R3) is the classical de Silva–Lim phenomenon in the smallest genuine instance: `W = e₁⊗e₁⊗e₂ + e₁⊗e₂⊗e₁ + e₂⊗e₁⊗e₁` has `tensorRank W = 3` — the algebraic core `W_eqns_inconsistent` eliminates the two-slice system by Cramer-type combinations (forming `D = a₀p₁ - a₁p₀`, deriving `Db_jc_k` from the first-mode slices, the identity `(Db₀c₁)(Db₁c₀) = (Db₀c₀)(Db₁c₁)` forcing `p₁ = a₁ = 0`, and then `W₁₀₀ = 1` reads `0 = 1`; no division by the possibly-zero D is performed) — while the explicit rank-2 sequence `(n+1)(e₁+e₂/(n+1))^{⊗3} - (n+1)e₁^{⊗3} = W + t_nP + t_n²Q` converges to W entry-by-entry, so `rankLE 2` is not closed, `infDist W (rankLE 2) = 0`, and no best approximation exists. (R4) proves the strongest faithful form of "limiting divergence": for every sequence of two-term decompositions converging to W, each of the two summand norms tends to +∞ — rebalancing factors to norm ≤ max(‖T‖,1) (justified by `‖a‖‖b‖‖c‖ ≤ ‖a⊗b⊗c‖` in the sup norm), Bolzano–Weierstrass extraction, continuity of ⊗, contradiction with `W_not_rankLE_two`; the individual divergence follows from `‖S_s‖ ≥ max - ‖S_0+S_1‖` with `‖S_n‖ < ‖W‖+1` eventually. The faithfulness gate is satisfied: the theorem formalizes the conjecture's own objects (actual tensors, actual rank, actual best approximations), assumes nothing comparable to the statement, and is not a toy instantiation — it is the canonical example plus the general matrix contrast and the general criterion.

The mathematics checks out: I verified numerically that `‖T_n - W‖ → 0` (values 0.5, 0.0909, 0.0099, 0.001 for n = 1, 10, 100, 1000), that the rebalanced summand norms diverge, and that a 300 000-case random small-integer search finds no two-term decomposition of W, consistent with the proof.

## Issues found

None blocking. (Cosmetic: README says "340 lines" for a file whose `wc -l` is 341; same CRLF-induced `SHA256SUMS.txt` text-file mismatches as the sibling submissions.)

## Verdict

APPROVED. The submission proves exactly what the conjecture asserts, in its honest reading: unlike matrices (proved for all m, n, r), a bounded-rank tensor set is not closed (2×2×2, rank ≤ 2, with the genuine W tensor of rank 3 in the closure), best approximation fails exactly when closedness fails, and approximating decompositions exhibit the stated limiting divergence of the summands. Build, axioms, LaTeX/PDF, and metadata checks all pass.
