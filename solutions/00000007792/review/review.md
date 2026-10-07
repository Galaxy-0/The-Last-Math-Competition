# Solution Review — Conjecture 00000007792 (PR 749)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005203138`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (`conjectures/00000007792.md`, bilingual); shipped `conjecture.md` is **byte-identical** to it (`diff` empty).
- **LaTeX**: full `proof.tex` read; independent `latexmk -pdf -interaction=nonstopmode` rebuild succeeds (exit 0). Shipped vs rebuilt PDF text compared with pypdf after whitespace/NFKC normalization: content matches; residual diffs are font-subset glyph-extraction artifacts only (big-operator glyphs and subscripts extracted differently between the author's MiKTeX fonts and the rebuild).
- **Lean build**: `lake build` completes with **zero errors and zero warnings** (8708 jobs). Toolchain `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a360ea` from the pinned manifest, built against the assigned prebuilt package pool.
- **Axioms**: `#print axioms` re-run independently (`lake env lean` with a reviewer-written Check file) for every main theorem — `conjecture_7792_false`, `conjecture_7792_false_eventually`, `conjecture_7792_false_limit`, `admissible_abs_ge_four`, `admissible_ge_four_of_odd`, `uniform_admissible_ge_four`, `ball_volume_product_ge` — each reports exactly `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`, `admit`, `unsafe`, `extern`, `implemented_by`, or declared `axiom` anywhere in the submission.
- **Aux code**: `verification/axioms.txt` matches my independent axiom run verbatim; `verification/build.txt` matches the fresh build (same successful completion); `SHA256SUMS.txt` entries disagree with the shipped files only because the author hashed CRLF working copies (LF→CRLF re-hash reproduces every recorded value exactly) — content is identical.
- **Metadata**: `metadata.csv` lists 00000007792 as unproven and undisproven; no other solution folder for this conjecture exists on `main`.

## Semantic audit

The conjecture defines an M-position of a convex body K as an ellipsoid E with vol(K+E)·vol(K°+E°) ≤ C^n·vol(K)·vol(K°) and asserts, as its first clause, that a single optimal constant C ≤ (π/4)e ≈ 2.135 is uniformly attainable over all bodies (asymptotically via the John position), with a second clause on stability of M-positions. The submission refutes the first clause — which refutes the conjunction — by proving a clean lower bound: in every dimension n ≥ 1 and against **every** ellipsoid E = c + A·B (arbitrary centre, non-degenerate A), the Euclidean unit ball B satisfies vol(B+E)·vol(B°+E°) ≥ 4^n·vol(B)·vol(B°). Hence any admissible constant has |C| ≥ 4, and C ≥ 4 in odd dimensions; 4 > (π/4)e kills all three readings formalized (one C for all n; one C for all large n; limits of per-dimension constants C_n ≥ 0 bounded by (π/4)e).

The formalization is faithful. The objects are the conjecture's own: `Rn n` is Euclidean n-space with Lebesgue `volume`, `polar` is origin polarity, `MEllipsoidCondition` reproduces the displayed inequality with the C^n normalization exactly as written, and `AdmissibleConstant n C` quantifies over all convex bodies (compact, convex, nonempty interior, 0 in the interior — the standard class for polar duality; the unit ball belongs to it, so the counterexample stands under any reading, and a failure of the restricted statement implies failure of the unrestricted one). No hypothesis assumes the deep theorem; the ball estimate is proved from scratch by SVD: with s_j the singular values of A, B+E contains a translate of D_{1+s}B and B°+E° contains a translate of D_{1+1/s}B (the non-centred case handled by the sharp supporting inequality ⟨d, x−kd⟩ + ‖x−kd‖ ≤ 1 with k = (1+‖d‖)^{-1}), and (1+s_j)(1+1/s_j) ≥ 4 coordinatewise.

The mathematics is correct. I verified numerically: the key inequality over 20,000 random d, x with ‖x‖ ≤ 1 in dimensions 1–3; (1+s)(1+1/s) − 4 = (s−1)²/s ≥ 0; centered ratios in 2D (s = (1,1) gives exactly 16 = 4², (2,3) gives 24, etc.); and (π/4)e ≈ 2.1349 < 4. The ENNReal.ofReal truncation of C^n is handled explicitly (a negative odd-power makes the condition unsatisfiable, consistent with the |C| ≥ 4 conclusion). The stability clause e^{cd²} is not formalized, but refuting the constant clause suffices to refute the conjecture as a conjunction, and the report says so explicitly. The report also correctly flags a C^{2n} normalization as a reading outside the refutation — the official text writes C^n, which is what is refuted.

## Issues found

None blocking. (Cosmetic: some `SHA256SUMS.txt` entries are recorded over CRLF variants of the same files; noted, not a content discrepancy.)

## Verdict

APPROVED. The submission exhibits a valid counterexample (the Euclidean unit ball, which satisfies every stated hypothesis), proves the falsifying bound 4^n against all ellipsoids with faithful definitions and no assumed theorems, compiles cleanly with only the three permitted axioms on every main theorem, and its report matches the Lean development. The conjecture's first clause — and with it the conjecture — is false.
