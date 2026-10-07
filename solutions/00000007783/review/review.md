# Solution Review — Conjecture 00000007783 (PR 663)

**Submission:** Jackmeson1 — `solutions/00000007783/Jackmeson1_submission_20261005085222`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture 00000007783 read in full (official bilingual English+Chinese text, ground truth). Shipped `conjecture.md` is **byte-identical** to `conjectures/00000007783.md` (`diff` clean).
- LaTeX: read the entire `proof.tex` (173 lines). Rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch dir from the shipped source; build succeeded. Shipped vs rebuilt PDF text compared with pypdf (whitespace- then glyph-normalized): identical modulo pure extraction artifacts (`∫`/`R` integral glyph ×4, math-boundary spacing), same normalized length 4735 chars.
- Lean: `lake build` succeeded from clean with Lean `leanprover/lean4:v4.33.1`, Mathlib v4.33.1 rev `0df444a360` (prebuilt pool `poolM10`); 8708 jobs, **zero errors, zero warnings**.
- Axioms: fresh `lake env lean Check.lean` on the shipped project printed `[propext, Classical.choice, Quot.sound]` — only the three standard axioms — for all three decisive theorems (`not_thinShell_le_rpow`, `not_sigma_le_rpow`, `not_thinShell_le_rpow_volOne`) and the supporting chain (`variance_norm_cube`, `moment_four`, `moment_two`, `isIsotropic_cube`, `isIsotropicVolOne_cube`). No `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, or declared `axiom` anywhere in the submission.
- Aux code: `verification/axioms.txt` and `verification/build.txt` match my fresh runs exactly. `verification/SHA256SUMS.txt` has stale entries for `conjecture.md` and `lean/Conjecture7783/Basic.lean` (final edit after checksumming; the PR is a single commit, so the shipped file is the only version, and it is the one I built and audited). Not blocking.
- Metadata: `metadata.csv` lists 00000007783 with `proven=false, disproven=false` (unsolved) — consistent.

## Semantic audit

The official conjecture defines the thin-shell constant σ_n as the supremum, over isotropic convex bodies, of the standard deviation of |X| for an isotropic uniform sample, and asserts σ_n = Θ(n^{-1/4}) ("the known upper-bound order cannot be improved"), together with ball/simplex values and a strict-monotone interpolation law. The submission proves the exact negation of the Θ upper bound in three forms: (a) no constants C, N make `thinShell K ≤ C·n^{-1/4}` hold for all n ≥ N and all isotropic convex bodies K ⊆ ℝ^n; (b) the same for σ_n itself, defined as a supremum in [0,∞]; (c) the same in the volume-one isotropy convention. Since Θ(n^{-1/4}) entails an eventual uniform upper bound, and the interpolation clause ("all isotropic bodies interpolate between n^{-1/2} and c·n^{-1/4}") also entails one with a fixed c, refuting (a)–(c) falsifies those clauses, hence the conjunction.

The formalization is faithful. Work is in `EuclideanSpace ℝ (Fin n)` with Lebesgue volume; the uniform law is `volume[|K]`; isotropy is mean zero and covariance identity (with the volume-one/covariance-L²I variant also formalized); the thin-shell quantity is `sqrt(variance (fun x => ‖x‖))`. The counterexample is the genuine cube `[-√3, √3]^n`, a compact convex body with nonempty interior that is genuinely isotropic (moments computed by Fubini: E X_i = 0, E X_iX_j = δ_ij·(a²/3) with a²/3 = 1), i.e., one of the conjecture's own objects — not a toy surrogate. The key inequality `variance_norm_cube`: with m = E‖X‖ and b = √(n)a, pointwise (‖X‖²−m²)² = (‖X‖−m)²(‖X‖+m)² ≤ 4b²(‖X‖−m)², while E(‖X‖²−m²)² = Var(‖X‖²) + (E‖X‖²−m²)² ≥ E‖X‖⁴ − (E‖X‖²)² = 4na⁴/45 (from E‖X‖² = na²/3, E‖X‖⁴ = n²a⁴/9 + n(a⁴/5−a⁴/9)); dividing by 4na² gives Var‖X‖ ≥ a²/45, so sd ≥ 1/√15 for all n ≥ 1. I verified the moment identities and the lower bound numerically by Monte Carlo (Var ≈ 0.250, 0.219, 0.203 at n = 1, 5, 30, all ≥ 3/45 ≈ 0.0667; sd ≈ 0.50, 0.47, 0.45 ≥ 1/√15 ≈ 0.258), and the asymptotic step (C·n^{-1/4} → 0) is standard. Since σ_n ≥ sd(cube) ≥ 1/√15 for every n while C·n^{-1/4} → 0, the Θ(n^{-1/4}) claim is genuinely false — a correct and decisive counterexample.

The conjecture as stated is indeed false in the literature sense too: the cube's thin-shell deviation is bounded below by an absolute constant, so no O(n^{-1/4}) upper bound on the supremum can hold. The submission neither strengthens hypotheses nor trivializes definitions; the volume-one variant (cube [-1/2,1/2]^n, volume 1, covariance (1/12)I, sd ≥ 1/√180) covers the alternative convention. Report and Lean match line-for-line (theorem names, statements, and constants all cross-checked).

## Issues found

None blocking. Stale entries in `verification/SHA256SUMS.txt` (`conjecture.md`, `lean/Conjecture7783/Basic.lean`); the shipped files are the ones built and audited here.

## Verdict

APPROVED. A correct, fully machine-checked disproof of the Θ(n^{-1/4}) thin-shell clause: the isotropic cube has thin-shell deviation at least 1/√15 in every dimension, so σ_n is not O(n^{-1/4}) in either isotropy convention, refuting the conjecture's central upper-bound claim and the upper half of its interpolation clause. Formalization faithful to the official definitions, build clean, axioms minimal, mathematics independently verified.
