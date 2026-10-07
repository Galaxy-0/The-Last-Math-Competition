# Solution Review — Conjecture 00000004515 (PR 746)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005201335`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `/Users/xinranwang/Documents/GitHub/The-Last-Math-Competition-2/conjectures/00000004515.md` read in full (bilingual). Shipped `conjecture.md` is byte-identical to it (`diff` empty).
- LaTeX: rebuilt independently with `latexmk -pdf -interaction=nonstopmode`; succeeds. Shipped vs rebuilt PDF text compared with pypdf (whitespace-normalized and aggressively normalized): content matches; differences are glyph-extraction artifacts only (math delimiters/ligature mappings of the authoring platform), cosmetic.
- Lean: `lake build` succeeds with zero errors and zero warnings (Lean v4.33.1, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474, prebuilt pool poolM04). The earlier "Too many open files" entries in the shared workspace log were environmental (host fd limit) and vanished on rebuild.
- Axioms: `lake env lean Axioms.lean` prints `[propext, Classical.choice, Quot.sound]` for both `C4515.conjecture_4515_false` and `C4515.conjecture_4515_false_uniform`, matching `verification/axioms.txt`. Supplementary audit: `mstLen_le_unitSq`, `ratio_tendsto_zero`, `not_frequently_lower` also only the standard three. No `sorry`/`native_decide`/`admit`/`unsafe`/`extern`/`implemented_by`/declared `axiom`.
- Aux code: `verification/` contains `SHA256SUMS.txt`, `axioms.txt`, `build.txt`; all recomputed SHA-256 hashes reproduce exactly after LF→CRLF normalization, and `axioms.txt`/`build.txt` match my independent rerun.
- Metadata: `metadata.csv` lists 00000004515 as unsolved; no solution folder for it on `main`.

## Semantic audit

The conjecture claims that for the random Euclidean MST on n iid points of a planar unit region, the expected total weight is a constant times √n times the 1/4 power of log n, with the exponent 1/4 "exact". The submission formalizes exactly these objects: `mstLen` is the minimum total Euclidean length of a spanning tree on the n labelled points (`Fin n → ℝ × ℝ` with the Euclidean distance written out; Mathlib's product `dist` is the sup metric, correctly avoided), `expMST μ n` is the integral of `mstLen` over the product probability measure, and `prof n = √n (log n)^{1/4}`. Measurability and integrability are proved, so the expectation is genuine (not a default-value artifact), and the minimum is proved attained for n ≥ 1.

The disproof rests on a deterministic strip bound proved in full: with k = ⌊√n⌋ + 1 horizontal strips, points sorted by (strip, abscissa) are joined by a path whose edge lengths satisfy d ≤ F(j+1) − F(j) with F(j) = x_j + (2 + 1/k)·strip(y_j) + j/k; telescoping gives len ≤ 1 + (2+1/k)(k−1) + (n−1)/k ≤ 3√n + 2 (`strip_arith` does the exact rational arithmetic). A connected graph contains a spanning tree of no larger length, so W_n ≤ 3√n + 2 for every configuration; scaling extends this to any bounded region; integrating gives E[W_n] ≤ C(3√n + 2). Hence E[W_n]/(c √n (log n)^β) → 0 for every c ≠ 0 and β > 0 (and for c = 0 the quotient is identically 0), so asymptotic equivalence, eventual equality, Θ-growth, and even an infinitely-often lower bound all fail — for every bounded-support law, in particular the uniform law on the unit square (`conjecture_4515_false_uniform`).

The mathematics is sound and consistent with the literature: by Steele's theory of subadditive Euclidean functionals the planar MST weight is in fact O(1) (bounded), so the conjectured √n (log n)^{1/4} growth is impossible; the submission needs only the much weaker O(√n) bound, which makes the disproof robust. I verified the strip bound numerically (Prim MST on random configurations: max W_n/(3√n+2) ≈ 0.22 over trials at n = 10, 100, 1000) and observed slow growth of E[W_n] (≈ 6.98 at n = 100, ≈ 13.18 at n = 400), far below the conjectured profile. The quantifier structure is faithful: all four refuted readings are reasonable formalizations of "is a constant times √n (log n)^{1/4}, exponent exact", each is refuted for all constants in the appropriate range, and refuting the weakest (infinitely-often lower bound) refutes every stronger one. No toy surrogate, no assumed theorem — the decisive theorem is the negation of the claim for the conjecture's own objects.

## Issues found

None blocking. (The c = 0 quotient convention is explicitly disclosed in the report and is not load-bearing for c > 0. SHA256SUMS mismatches are CRLF→LF normalization artifacts, reconciled byte-exactly.)

## Verdict

APPROVED. A clean, faithful, and decisive disproof: the deterministic O(√n) strip bound on the planar MST weight forces E[W_n]/(c √n (log n)^{1/4}) → 0, so the conjectured (log n)^{1/4} profile with exact exponent 1/4 is false for the uniform law on the unit square (and every bounded-support law). Build, axioms, report, and auxiliary verification files all check out, and the mathematics was independently confirmed numerically.
