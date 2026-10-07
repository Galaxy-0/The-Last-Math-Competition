# Solution Review — Conjecture 00000007751 (PR 657)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005082219`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read: yes — the source asserts MSD(1,2)=9 attained by a unique map, plus a general domination bound (d^{2N+2}−1)/(d−1); the submission's `conjecture.md` is byte-identical to `conjectures/00000007751.md`.
- Change scope: only the submission folder was added; the problem is untouched otherwise.
- LaTeX: independently rebuilt with `latexmk -pdf -interaction=nonstopmode` (exit 0). Shipped and rebuilt PDF text agree after whitespace normalization; all remaining diffs are glyph/ligature/subset extraction artifacts (e.g. `6=` vs `̸=`, `coeﬀ` vs `coeff`), content identical.
- Lean build: `lake build` exit 0, zero errors, zero warnings (Lean v4.33.1, Mathlib pin `0df444a360…` via the prebuilt pool).
- Forbidden content: no executable `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern`; hits are prose-only (README/SEMANTIC_REVIEW). `lean/Axioms.lean` only contains `#print axioms` commands.
- Axioms: independent `lake env lean` run — `MSD_ne_nine`, `twelve_le_MSD`, `not_all_le_nine`, `exists_degree_two_eleven_affine_preperiodic`, `RatMap.act_wellDefined` all depend only on `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: `verification/` contains build log, axiom output and SHA-256 sums. The build/axiom claims reproduce exactly. The SHA-256 manifest is stale (see Issues).
- Semantic audit: pass (below).
- Independent arithmetic check: every entry of the evaluation table was recomputed by hand and is correct.

## Semantic audit
The conjecture is the conjunction (i) MSD(1,2)=9, (ii) attained by a unique map, (iii) general domination. The submission refutes (i), which kills the conjunction; (ii) and (iii) are explicitly not addressed, and the report notes (iii) would give 15 for N=1, d=2, consistent with 12 points.

The Lean modelling is faithful. `RatMap d` is a pair of coprime rational polynomials with `max natDegree = d` — for d ≥ 1 exactly the degree-d morphisms of P¹ over ℚ (coprimality rules out a common affine zero, the degree condition rules out a common pole at infinity, and `RatMap.act_wellDefined` proves both in Lean). P¹(ℚ) is `Option ℚ` with the homogeneous action `[a:1] ↦ [p(a):q(a)]`, `∞ ↦ [coeff_d p : coeff_d q]`; `IsPreperiodic` is finiteness of the forward orbit; `MSD d` is the `ENat` infimum of uniform bounds over all finite subsets, i.e. the least uniform bound with `⊤` if none exists. These match the source definitions line by line.

The witness f(z) = (−2z²−3z−1)/(2z²−z) is a genuine degree-2 rational map over ℚ (Bézout identity `(4X−3)P + (4X+5)Q = 3` proved in Lean; both degrees 2). The 12-point set S is proved to have cardinality 12 (so the points are distinct, not hardcoded) and to be forward-invariant (`S_invariant` by `norm_num` on the explicit action formula). Finiteness of S then gives preperiodicity of all its elements, hence `(12 : ℕ∞) ≤ MSD 2` and `MSD 2 ≠ 9`, plus the equivalent formulation `¬∀ g, ∀ T, (all preperiodic) → #T ≤ 9`. I re-derived all twelve images by hand (∞→−1→0→∞, −5/2→−2/5→−1/6→−5/2, and six tails) and they match. Refuting (i) with a lower bound of 12 > 9 is exactly the negation of that conjunct; no hypothesis is strengthened and nothing is trivialized.

## Issues found
- Non-blocking: `verification/SHA256SUMS.txt` is stale — the recorded hash of `conjecture.md` (and in some PRs of the main Lean file) does not match the shipped files. The shipped `conjecture.md` is byte-identical to the official source and the shipped Lean file is what builds cleanly with clean axioms, so this is a bookkeeping flaw only.

## Verdict
APPROVED. The disproof is faithful, complete for the clause it refutes, machine-checked with clean axioms, and independently rebuilt and reproduced in every audited dimension.
