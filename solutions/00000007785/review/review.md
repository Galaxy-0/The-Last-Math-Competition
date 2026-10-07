# Solution Review — Conjecture 00000007785 (PR 662)

**Submission:** Jackmeson1 — `solutions/00000007785/Jackmeson1_submission_20261005084830`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture 00000007785 read in full (official bilingual English+Chinese text, ground truth). Shipped `conjecture.md` is **byte-identical** to `conjectures/00000007785.md` (`diff` clean).
- LaTeX: read the entire `proof.tex` (172 lines). Rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch dir from the shipped source; build succeeded. Shipped vs rebuilt PDF text compared with pypdf (whitespace-normalized, then glyph-normalized): identical modulo pure extraction artifacts (`ﬀ`/`ff` ligature; math-boundary spacing such as `vol( K)`/`vol(K)`), length 5185/5186 normalized chars.
- Lean: `lake build` succeeded from clean with Lean `leanprover/lean4:v4.33.1`, Mathlib v4.33.1 rev `0df444a360` (prebuilt pool `poolM10`); 8708 jobs, **zero errors, zero warnings**.
- Axioms: fresh `lake env lean Check.lean` on the shipped project printed `[propext, Classical.choice, Quot.sound]` — only the three standard axioms — for `conjecture_7785_symmetric_clause_false` and all supporting theorems (`mahler_cube`, `mahler_cube_lt`, `volume_crossPolytope`, `volume_cube`, `polar_cube`, `cube_isHanner`). No `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, or declared `axiom` anywhere in the submission.
- Aux code: `verification/axioms.txt` and `verification/build.txt` match my fresh runs exactly. `verification/SHA256SUMS.txt` contains a stale checksum for `conjecture.md` only (author re-checksummed before swapping in the official conjecture copy); all other 13 entries verify. Not blocking.
- Metadata: `metadata.csv` lists 00000007785 with `proven=false, disproven=false` (unsolved) — consistent.

## Semantic audit

The official conjecture text defines the Mahler product `M(K) = vol(K) vol(K°)`, asserts "the Mahler conjecture asserts M(K) >= 4^n in the symmetric case" (both languages: 「Mahler 猜想断言对称情形 M(K)≥4^n」), and conjectures that the symmetric extremal (equality-case) bodies are the Hanner polytopes. The submission's decisive theorem `C7785.conjecture_7785_symmetric_clause_false` states that for every n ≥ 2 the cube `[-1,1]^n` (i) is a Hanner polytope in the recursive sense (product/dual closure of the segment), (ii) is an origin-symmetric convex body (compact, convex, nonempty interior, `K = -K`), (iii) has `M(cube) = 4^n/n!`, and (iv) `M(cube) < 4^n`; and hence the universal statements "every origin-symmetric convex body K in R^n has 4^n ≤ M(K)" and "every Hanner polytope in R^n has M(K) = 4^n" are both false.

The formalization is faithful. The polar is the standard `{y | x·y ≤ 1 ∀ x ∈ K}` for the standard dot product; `vol` is Lebesgue (product) measure on `Fin n → ℝ`; the counterexample is one of the conjecture's own objects (a Hanner polytope), not a toy surrogate, and no hypothesis is strengthened: the cube satisfies every stated side condition of the symmetric clause. The mathematics is a direct computation: `polar_cube` (test with sign vectors) gives cube° = cross-polytope; `volume_cube` = 2^n by the product-interval formula; `volume_crossPolytope` = 2^n/n! by Mathlib's ℓ¹-ball volume formula (checked via Gamma values, and independently by Monte Carlo: 1.996/2.000 at n=2, 1.312/1.333 at n=3, 0.674/0.667 at n=4). Since n! > 1 for n ≥ 2, 4^n/n! < 4^n in every dimension n ≥ 2, so the "finitely many low-dimensional exceptions (n ≤ 3)" hedge cannot rescue the clause (in dimension 1, M([-1,1]) = 4 = 4^1, consistent).

A reviewer might object that the classical Mahler conjecture uses the constant 4^n/n! under Lebesgue volume, and that the submission refutes a mis-stated constant. That objection is answered inside the submission itself: the official bilingual text — the ground truth per this competition's protocol — writes `4^n` in the bound, in the "strict inequality outside the Hanner family" clause, and in the stability hypothesis `M(K) ≤ 4^n(1+ε)`, and the report's Remark explicitly disclaims any claim about the corrected 4^n/n! statement, which remains open for n ≥ 4. Under the official text as written, the counterexample satisfies all stated hypotheses and the refuted universal statements are its exact negations; the second conjunct (Hanner polytopes are not all equality cases) additionally falsifies the classification clause on its biconditional reading. The disproof is valid, verified, and correctly scoped.

## Issues found

None blocking. `verification/SHA256SUMS.txt` has one stale entry (`conjecture.md`); the shipped copy is byte-identical to the official file, and the files that matter (Lean sources, proof.tex/pdf, README, SEMANTIC_REVIEW) all verify.

## Verdict

APPROVED. A clean, fully machine-checked disproof of conjecture 00000007785 as written: the cube `[-1,1]^n` is an origin-symmetric convex body and a Hanner polytope with Mahler product 4^n/n! < 4^n for every n ≥ 2, refuting both the asserted symmetric bound and the Hanner equality-case classification in every dimension covered by the statement. Formalization faithful, build clean, axioms minimal, report honest about scope (it explicitly does not touch the corrected classical 4^n/n! conjecture).
