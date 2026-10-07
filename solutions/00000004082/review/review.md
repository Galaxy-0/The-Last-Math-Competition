# Solution Review — Conjecture 00000004082 (PR 736)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005192110`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000004082.md` read in full (English + Chinese). Shipped `conjecture.md` is byte-identical to it (`diff` clean).
- LaTeX: full `proof.tex` read; `latexmk -pdf -interaction=nonstopmode` rebuild in a scratch dir succeeds (exit 0). pypdf text comparison of shipped vs rebuilt PDF matches after normalizing extraction artifacts only (∑/∏ glyph mapping to P/Q, `\texttt` underscores, ligature ff/fi, one subscript glyph in a display); no content discrepancy.
- Lean: clean `lake build` succeeds with zero errors and zero warnings (Lean v4.33.1, Mathlib v4.33.1, rev v4.33.1, prebuilt pool toolchain; 8708 jobs).
- Axioms: independent `lake env lean Check.lean` on `conjecture4082_false`, `conjecture4082_false_universal`, `Kc_not_function_of_meanAbsDev`, `conjecture4082_false_unnormalised`, `conjecture4082_false_cohesive`, `conjecture4082_false_eventual`, `locked_iff_phaseLockedSolution`, `Kc_lt` — all report only `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `native_decide`, `extern`, `unsafe`, `implemented_by`, or declared `axiom` anywhere (`lean/Axioms.lean` contains only `#print axioms` commands).
- Aux code: `verification/axioms.txt` matches the independent axiom run; `verification/build.txt` consistent with a successful fresh build. Note: `verification/SHA256SUMS.txt` has stale entries (`conjecture.md` in all four sibling submissions, and `Basic.lean` here) — the shipped `conjecture.md` was verified byte-identical to the official copy and the Lean build was rerun from the actual files, so this is packaging hygiene, not a correctness issue.
- Metadata: `metadata.csv` at the PR base commit lists `00000004082` as unsolved; the PR adds only the solution folder.

## Semantic audit

The conjecture states that for n all-to-all coupled oscillators the critical coupling K_c (the onset threshold of synchronization, i.e. phase locking) satisfies K_c = c₁·(Σᵢ|ωᵢ − ω̄|)/n for a universal constant c₁ — i.e. that K_c depends on the intrinsic frequencies only through their dispersion. The submission proves the exact negation of this formula: for every n ≥ 6 there is no constant c₁ (not even one depending on n) with Kc ω = c₁·(Σᵢ|ωᵢ − mean ω|)/n for all ω (`conjecture4082_false`), and the stronger statement that Kc is not any function of the mean absolute deviation.

The formalization is faithful. `Locked ω K` is the standard solvability condition ωᵢ + (K/n)Σⱼsin(θⱼ−θᵢ) = Ω of the all-to-all sine-coupled Kuramoto model, and `locked_iff_phaseLockedSolution` proves it equivalent to the existence of a solution trajectory of the ODE with all phase differences constant — precisely "phase locking". `Kc ω = sInf {K ≥ 0 | Locked ω K}` captures "onset threshold"; variant readings (unnormalized coupling, phase-cohesive locking |θᵢ−θⱼ| < π/2, eventual-locking threshold) are refuted as well. The deep input is not assumed anywhere: it is proved (`abs_sub_mean_le_of_locked`) that at any locked state Ω = ω̄ and |ωᵢ − ω̄| ≤ K, using the antisymmetry of the double sine sum; the locking construction for the two-cluster vector is an explicit arcsin phase profile verified coordinatewise.

The counterexample is correct. For 0 < a < n, `clusterFreq n a` (a entries at n/(2a), n−a at −n/(2(n−a))) has mean 0 and MAD exactly 1. For a = 3 it locks for every K ≥ s₃ = n²/(6(n−3)); for a = 1 the necessary condition forces every locking K ≥ n/2. Since s₃ < n/2 for all n ≥ 6, the two Kc's differ while the MAD's coincide, so no function of the MAD — in particular no multiple c₁·MAD — can equal Kc. I verified the numerics independently for n = 6: the explicit phases lock (1,1,1,−1,−1,−1) exactly at K = 2, and (3,−3/5,…,−3/5) has MAD 1 with the n/2 = 3 lower bound; s₃ = 2 < 3. The threshold-separation lemma is proved for a general locking predicate, which is what makes the variant readings one-line corollaries.

## Issues found

None blocking. (Minor, non-blocking: stale SHA-256 entries in `verification/SHA256SUMS.txt` for `conjecture.md` and `lean/Conjecture4082/Basic.lean`; both files were verified directly against the official copy and by a clean rebuild.)

## Verdict

APPROVED. The Lean main theorem is the exact negation of the conjecture's formula clause, formalized on the conjecture's own objects (the all-to-all Kuramoto model, phase locking, and the critical-coupling infimum), with a correct two-cluster counterexample in which equal dispersions yield strictly different critical couplings. The build is clean, the axiom audit shows only the three standard axioms, and the paper faithfully mirrors the formal development.
