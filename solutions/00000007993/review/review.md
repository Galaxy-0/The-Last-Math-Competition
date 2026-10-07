# Solution Review — Conjecture 00000007993 (PR 687)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005114056`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (bilingual). The submission's `conjecture.md` is byte-identical to `conjectures/00000007993.md`.
- **LaTeX report:** read in full; rebuilt independently with `latexmk -pdf`; rebuild exited 0.
- **PDF match:** shipped vs rebuilt PDF text agrees after normalization; only glyph extraction artifacts.
- **Lean build:** `lake build` (v4.33.1, Mathlib 0df444a360) exited 0, no errors, no warnings.
- **Axiom audit:** no forbidden keywords; re-ran `lake env lean Axioms.lean`: `C7993.not_conjecture` and `C7993.family` depend only on `[propext, Classical.choice, Quot.sound]`.
- **Auxiliary code:** `verification/axioms.txt` and `build.txt` reproduce my runs; `SHA256SUMS.txt` has stale `conjecture.md` and `Basic.lean` entries (files verified correct).
- **Semantic audit:** pass (see below).
- **Scope:** the PR adds only `solutions/00000007993/Jackmeson1_submission_20261005114056/`; no existing solution on `main`.

## Semantic audit

The definitions follow Figalli–Ros-Oton–Serra (arXiv:1912.00714, §3) as the conjecture's subject matter demands: free boundary `FB = Ω ∩ ∂{u>0}`; regular points (blow-up `½(max{0, e·x})²`, pointwise — the weakest mode, so the negation is the strongest); singular points (blow-up in the class `𝒫` of convex 2-homogeneous polynomials with `Δp ≡ 1`, locally uniformly); and `IsObstacleSolution` requires `C^∞`, `u ≥ 0`, `Δu = 1` on `{u>0}`, and `Δu = χ_{u>0}` a.e. — strictly stronger than the standard `C^{1,1}` setting, which only shrinks the solution class and thereby strengthens the refuted universal claims. The submission says precisely this.

The witness `u₀ = x₁²/2` is decisive on both refuted clauses. It is a solution: `Δu₀ ≡ 1` and the contact set `{x₁ = 0}` is a proper subspace of measure zero, so `Δu₀ = χ_{u₀>0}` a.e. Its free boundary is `B₁ ∩ {x₁ = 0}`; since `u₀` is exactly 2-homogeneous, `r⁻²u₀(x₀ + rx) = u₀` at every free-boundary point, so the blow-up is `u₀ ∈ 𝒫` (via `Q = ½ e₁⊗e₁`, convexity of `t²`, `Δu₀ = 1`): every point is singular. No point is regular: a half-space limit would force `u₀ = ½(max{0,⟨e,x⟩})²` identically, contradicted at `x = −e` (forcing `e₁ = 0`) and then at `x = e₁` (`½ = 0`). Hence `Reg = ∅` while `0 ∈ FB`, killing the density clause; and `dimH Sing = dimH(B₁ ∩ {x₁ = 0}) = n − 1` (isometry + rank–nullity + `dimH` of a set with nonempty interior in an (n−1)-dim space), which exceeds `n − 3` for `n ≥ 3` — decisive at `n = 3` (`2 > 0`) — killing the dimension clause. The n = 2 clause (bound 1) is honestly left unrefuted, as the witness gives dimension 1 there.

Two faithfulness questions I checked independently. First, the singular-point definition does not exclude half-space profiles (FROS's classes are disjoint); this only enlarges `Sing` and could in principle ease the refutation — but for this witness every blow-up is `x₁²/2`, which is *not* a half-space profile (that is exactly what `not_regular_u₀` proves), so `Sing` coincides with the FROS singular set here and the counterexample survives the disjoint reading verbatim. Second, admissibility: beyond the a.e. PDE reading, I verified `u₀` also satisfies the variational-inequality formulation — it is the minimizer of `∫(½|∇v|² + v)` over `v ≥ 0` with its own boundary values, the first-order expression vanishing identically since `Δu₀ ≡ 1` — so this is a genuine obstacle-problem solution with a degenerate (empty-interior) contact set, not an artifact of a weakened definition. The literature agrees the singular set can be (n−1)-dimensional in general (FROS abstract, quoted in the report), so the conjecture's `n−3` bound for all solutions is indeed false. The tangent-cone clause is not formalized; the conjunction fails through the two refuted clauses.

## Issues found

- Minor hygiene: two stale entries in `verification/SHA256SUMS.txt`; actual files verified.
- No mathematical or semantic issues; the report is exemplary in documenting definitional choices and their direction of strength.

## Verdict

APPROVED. A mathematically substantial and fully faithful disproof of two clauses of a hard-analysis conjecture, with real Hausdorff-dimension and blow-up-limit arguments in Lean, clean build and axioms, and a report of unusually high quality.
