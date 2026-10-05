# Solution Review — Conjecture 00000002391 (PR 567)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004203700`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture `conjectures/00000002391.md` read in full (box dimension of the support of a C-doubling measure claimed ≥ log 2/log C, exact/tight constant). The submission's `verification/original.md` is **byte-identical** to the official file (diff clean).
- LaTeX: `proof.tex` rebuilt from scratch with `latexmk -pdf` (clean, 2 pages). Shipped `proof.pdf` (Tectonic) vs rebuild: **exact text match** after standard ligature/whitespace normalization (2457 chars).
- Lean: fresh `lake build` with lean4 v4.19.0, Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b` — **0 errors**, one cosmetic linter warning (`tac1 <;> tac2` where `(tac1; tac2)` suffices, Main.lean:21).
- Axioms: `Main.lean` runs `#print axioms` on all seven headline results (`support_eq`, `doubling_two`, `minimal_constant`, `actual_cover_number`, `upper_dimension_zero`, `local_dimension_zero`, `claimed_bound_fails`); each depends only on `[propext, Classical.choice, Quot.sound]`. No `sorry`/`native_decide`/`axiom`/`unsafe`/`admit`/`implemented_by`/`extern` anywhere.
- Auxiliary code: none beyond verification logs; `verification/validation.txt` and `direct-pr-search.json` (empty) are consistent with the submitted artifacts.
- Repo metadata: conjecture is unsolved; submission claims a disproof.

## Semantic audit
The conjecture asserts, universally over measures with doubling constant C, that the (local or global) box dimension of the support is at least log 2/log C, with a tight constant. The submission exhibits μ = δ₋₁ + δ₁ on ℝ. Its topological support — characterized in Lean exactly as `{x | ∀ r > 0, 0 < μ(B(x,r))}` and proved equal to S = {−1, 1} — is a two-point compact metric space. Under the standard doubling condition μ(B(x,2r)) ≤ C·μ(B(x,r)) for centers in the support (equivalently, μ is a doubling measure on the metric space it lives on), every ball centered in S contains its atom (mass ≥ 1) and every ball has mass ≤ 2, so C = 2 is valid at every radius; minimality is sharp: at x = −1, r = 3/2 the open ball (−2.5, 0.5) contains only −1 while the doubled ball contains both atoms, forcing C ≥ 2. I re-verified all cases (r ≤ 1, 1 < r ≤ 2, r > 2) by hand and numerically.

The covering number of S at scale ε is exactly 2 for all 0 < ε ≤ 1 (a single ε-ball cannot contain two points at distance 2, by the triangle inequality — proved in Lean via `dist_triangle`), hence log N(ε)/log(1/ε) = log 2/t → 0 and both upper and lower box dimensions of the support are 0, as is the local box dimension of S ∩ B(x,1) = {x} at each point. Since the minimal doubling constant is 2, the claimed bound demands 0 = dim ≥ log 2/log 2 = 1, which is false; moreover every valid constant C for this measure satisfies C ≥ 2 > 1, so log 2/log C > 0 = dim fails for **all** valid constants simultaneously — the refutation does not depend on any particular choice of C. The Lean `claimed_bound_fails` negates the bound exactly at the sharp minimal constant, and `doubling_two` + `minimal_constant` supply the two sides (validity and sharpness) needed for a genuine counterexample satisfying the conjecture's hypotheses.

Faithfulness: the official bilingual text imposes no non-atomicity, no absence of isolated support points, and no ambient-space convention; the submission states its center convention explicitly and notes that a modified claim excluding atoms would be a different statement. The quantifier structure is the correct negation of the universal claim (one doubling measure, at its sharp constant, whose support dimension violates the bound). Definitions in Lean are the standard ones: genuine Mathlib Dirac measures, metric balls, measure-theoretic support via positive mass in every ball, covering numbers as infima of cardinalities of finite ball covers, and box dimensions as limsup/liminf of the log-covering exponent with ε = e^{−t}. The report's mathematics matches the Lean theorems line for line.

## Issues found
None blocking. (Cosmetic `<;>` linter warning; shipped PDF built with Tectonic vs reviewer's pdflatex with identical extracted content.)

## Verdict
APPROVED. The two-atom doubling measure with sharp constant C = 2 and support of box dimension 0 < 1 = log 2/log 2 is a mathematically correct, robustly-stated counterexample to the conjecture as written; the formalization is faithful, complete, and verified from a pristine build with only the three standard axioms.
