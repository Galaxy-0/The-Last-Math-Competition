# Solution Review — Conjecture 00000000702 (PR 737)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005192510`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000000702.md` read in full (English + Chinese). Shipped `conjecture.md` is byte-identical to it (`diff` clean).
- LaTeX: full `proof.tex` read; `latexmk -pdf -interaction=nonstopmode` rebuild in a scratch dir succeeds (exit 0). pypdf text comparison of shipped vs rebuilt PDF matches after normalizing extraction artifacts only (∑/∏ glyph mapping, `\texttt` underscores, ligatures, spacing); no content discrepancy.
- Lean: clean `lake build` succeeds with zero errors and zero warnings (Lean v4.33.1, Mathlib v4.33.1, 8708 jobs).
- Axioms: independent `lake env lean Check.lean` on `conjecture702_false`, `browkin_counterexample`, `browkinS_spec`, `browkinT_spec`, `bcf2_first_steps` — all report only `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `native_decide`, `extern`, `unsafe`, `implemented_by`, or declared `axiom` anywhere (`lean/Axioms.lean` contains only `#print axioms` commands).
- Aux code: `verification/axioms.txt` matches the independent axiom run; `verification/build.txt` consistent with a successful fresh build; this submission's `Basic.lean` checksum matches its own manifest. Note: `verification/SHA256SUMS.txt` has one stale entry (`conjecture.md`) — the shipped copy was verified byte-identical to the official file, so this is packaging hygiene, not a correctness issue.
- Metadata: `metadata.csv` at the PR base commit lists `00000000702` as unsolved; the PR adds only the solution folder.

## Semantic audit

The conjecture asserts that the Browkin expansion (a continued-fraction-like expansion in the p-adics) of an algebraic number is never eventually periodic, with the unboundedness of its partial quotients as the evidence for non-periodicity. The submission proves the exact negation: for every odd prime p there exists an irrational algebraic α ∈ ℚ_p whose Browkin expansion is eventually periodic and whose partial quotients take only finitely many values (hence bounded in every sense, in particular p-adically). The refutation covers both standard readings of "the Browkin expansion": Browkin's first algorithm (the s-function algorithm as stated in Capuano–Murru–Terracini, arXiv:2010.07364) and Browkin's second algorithm (the t-operator algorithm with sign correction as stated in Murru–Romeo–Santilli, arXiv:2201.12019), each clause being refuted separately for each algorithm.

The formalization is faithful to the conjecture's own objects. The digit sets J_p = ℤ[1/p] ∩ (−p/2, p/2) and K_p = ℤ[1/p] ∩ (−1/2, 1/2), the selectors s and t (defined by their characterizing properties via Classical.epsilon, with uniqueness proved for every prime and existence for odd p via balanced valMinAbs digits), the complete quotients α_{n+1} = 1/(α_n − a_n), eventual periodicity, and p-adic boundedness are all the genuine article — no toy surrogate. The recursion is totalized at 0 in Lean, but the submission proves α_n ≠ a_n (respectively α_n ≠ b_n) for every n, so the never-divide-by-zero condition of the papers' algorithms holds along the entire orbit; there is no loophole through the totalization. Restricting the universal claim to irrational algebraic α only strengthens the refutation (rational expansions terminate).

The counterexample is correct and, in my judgment, definitive. Hensel's lemma applied to F = pX² + X − p at 0 (|F(0)|_p = 1/p < 1 = |F'(0)|_p²) yields β ∈ ℤ_p with pβ² + β − p = 0 and |β|_p < 1. With α = β^{−1} one has the exact identity α − 1/p = β (equivalent to the quadratic equation), so |α − 1/p|_p < 1, and since 1/p ∈ J_p uniqueness gives s(α) = 1/p and α₁ = α: Browkin I produces the purely periodic expansion [1/p; 1/p, …]. For Browkin II the orbit α, (1+β)^{−1}, −α−1, −(1+β)^{−1}, α+1 cycles with period 4 from index 2, giving partial quotients 1/p, 1/p−1, then (1, −1/p, −1, 1/p) repeating. I verified the entire construction independently by simulating both algorithms in p-adic arithmetic for p = 3, 5, 7, 11, 13 over 40 steps: the partial-quotient sequences match the claims exactly, and α is algebraic (root of pX² − X − p) and irrational (4p² + 1 lies strictly between (2p)² and (2p+1)²). The submission is also appropriately explicit about what it does not refute (a degree-≥3 reading, and clause 2 read as a conditional implication), which does not affect the falsity of the stated conjunction.

## Issues found

None blocking. (Minor, non-blocking: stale SHA-256 entry in `verification/SHA256SUMS.txt` for `conjecture.md`; the file content was verified directly.)

## Verdict

APPROVED. The submission exhibits a concrete irrational algebraic p-adic number whose Browkin expansions under both standard algorithms are (eventually) periodic with finitely many, hence bounded, partial quotients — the exact negation of both clauses of the conjecture — formalized faithfully on the conjecture's own objects with a clean build, a standard-axioms-only audit, and correct paperwork.
