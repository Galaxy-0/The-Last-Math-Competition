# Solution Review — Conjecture 00000008338 (PR 763)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005213259`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000008338.md` read in full (bilingual); shipped `conjecture.md` is byte-identical to it (`diff` clean). The shipped `verification/SHA256SUMS.txt` lists one stale hash (`conjecture.md`), but the file itself is the correct official copy — bookkeeping artifact only.
- LaTeX rebuild: `latexmk -pdf` in a scratch dir succeeds; shipped and rebuilt `proof.pdf` match after whitespace/ligature normalization; remaining differences are font glyph-extraction artifacts only (underscores, `ff` ligature) — cosmetic.
- Lean build: `lake build` succeeds with zero errors and zero warnings (Lean 4.33.1, Mathlib v4.33.1, pool rev `0df444a360`, ~105 s).
- Axioms: independent `lake env lean Check.lean` with `#print axioms` for `conjecture8338_false`, `not_siegC_eq_bvValue`, `siegC_one_two`, `isLeast_real_bound`, `minSolHeight_witness`, `minSolHeight_lt_bvValue` — each depends only on `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `native_decide`, `extern`, `unsafe`, or declared `axiom`.
- Aux code: `verification/build.txt` and `verification/axioms.txt` match the reviewer's fresh rebuild and axiom output; no runnable scripts shipped (none needed).
- Metadata: `metadata.csv` lists 00000008338 as unsolved.

## Semantic audit

The conjecture's Definition line names `sieg_c` as the height upper bound of minimal solutions of integer-coefficient linear systems, and its main clause asserts that this optimal constant *is* the explicit `(nH)^{m/(n-m)}`, with a further clause that the constant's tightness (attainment of minimal solution heights) holds. The submission formalizes exactly these objects: sup-norm vector height, matrix height, the set of heights of nonzero integer kernel vectors, `minSolHeight A = sInf` of that set, admissibility (integer coefficients, not all zero, bounded by H), and `siegC m n H = sSup` of the minimal-solution heights over admissible systems — the natural and standard reading of "the height upper bound of minimal solutions". The claimed value `bvValue m n H = (nH)^{m/(n-m)}` is tested exactly as written (real power).

The disproof is a genuine counterexample, not a toy surrogate: at `(m, n) = (1, 2)` the submission proves `siegC(1,2,H) = H` for every `H >= 1` from both sides. Upper bound: every 1x2 system has the nonzero kernel vector `(b, -a)` of height max(|a|,|b|) <= H (and `(1, 0)` for the zero row), so every minimal height is at most H. Lower bound: the admissible witness row `(H, H-1)` (height exactly H, nonzero since H >= 1) satisfies `x_1 = H(x_0 + x_1)` on the kernel, forcing `H | x_1`; x_1 = 0 would force x = 0, so every nonzero solution has `H <= |x_1| <= ht(x)`, and since gcd(H, H-1) = 1 the bound is attained. Hence `siegC(1,2,H) = H`, H is even the least real bound (`isLeast_real_bound`), and `(nH)^{m/(n-m)} = (2H)^{1/(2-1)} = 2H > H`. The universal equality clause (`not_siegC_eq_bvValue`, refuted at the single instance (1,2,1)) and the attainment clause (no admissible system whatsoever has minimal height 2H — `minSolHeight_lt_bvValue`, so pointwise for every distribution, random or not) both fail; since the conjecture is a conjunction, it falls with its main clause. The reviewer re-derived the value H independently (kernel of (a b) is spanned by the primitive vector (b,-a)/gcd(a,b); heights maximize at coprime rows such as (H, H-1)).

The submission is also honest about scope: it does not claim to refute the (true) reading that `(nH)^{m/(n-m)}` is a valid upper bound — Siegel's lemma — nor exponent sharpness (the exponent 1 is sharp at (1,2); only the constant factor n is wrong), and it leaves the two Edelman tail clauses untouched, which is legitimate since the conjunction is already refuted. The paper's scholarship note (the formula `(nH)^{m/(n-m)}` is Siegel's bound; Bombieri–Vaaler's sharpened bound is the determinant/minor bound) is correct and does not affect the test of the formula as written.

## Issues found

None blocking. Cosmetic: one stale hash in `verification/SHA256SUMS.txt` (`conjecture.md`), while the file itself is byte-identical to the official conjecture.

## Verdict

APPROVED. A rigorous, fully machine-checked disproof of the written claim: the optimal Siegel constant for 1x2 systems is H, strictly below the conjectured `(nH)^{m/(n-m)} = 2H` for every H >= 1, with the sharp value proven from both sides and non-attainment of the claimed value shown for every admissible system. The formalization uses the conjecture's own objects, the quantifier structure is the exact negation of the universal equality, the build is clean with only the three permitted axioms, and report and Lean agree.
