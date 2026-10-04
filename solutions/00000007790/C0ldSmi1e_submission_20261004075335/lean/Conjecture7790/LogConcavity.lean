import Conjecture7790.Definitions
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith

noncomputable section
open Real Set

namespace Conjecture7790

theorem density_nonneg (x : ℝ) : 0 ≤ density x := by
  unfold density
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem density_pos_iff (x : ℝ) : 0 < density x ↔ -1 ≤ x := by
  by_cases hx : -1 ≤ x
  · simp [density, hx, Real.exp_pos]
  · simp [density, hx]

/-- The nonzero density has exactly the expected convex half-line support. -/
theorem density_positive_support : {x : ℝ | 0 < density x} = Set.Ici (-1) := by
  ext x
  exact density_pos_iff x

theorem density_logConcave : IsLogConcaveDensity density := by
  refine ⟨density_nonneg, ?_⟩
  intro x y a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0, ha1]
  by_cases hx : -1 ≤ x
  · by_cases hy : -1 ≤ y
    · have hax : 0 ≤ a * (x + 1) := mul_nonneg ha (by linarith)
      have hby : 0 ≤ b * (y + 1) := mul_nonneg hb (by linarith)
      have hxy : -1 ≤ a * x + b * y := by nlinarith
      simp only [density, if_pos hx, if_pos hy, if_pos hxy]
      rw [Real.rpow_def_of_pos (Real.exp_pos _) _,
        Real.rpow_def_of_pos (Real.exp_pos _) _, Real.log_exp, Real.log_exp,
        ← Real.exp_add]
      apply le_of_eq
      congr 1
      nlinarith
    · have hdy : density y = 0 := by simp only [density, if_neg hy]
      rw [hdy, Real.zero_rpow hb0, mul_zero]
      exact density_nonneg _
  · have hdx : density x = 0 := by simp only [density, if_neg hx]
    rw [hdx, Real.zero_rpow ha0, zero_mul]
    exact density_nonneg _

/-- On its positive support, the logarithm of the density is affine. -/
theorem log_density_of_mem_support {x : ℝ} (hx : x ∈ Set.Ici (-1)) :
    Real.log (density x) = -(x + 1) := by
  simp only [Set.mem_Ici] at hx
  simp only [density, if_pos hx, Real.log_exp]

theorem log_density_concave :
    ConcaveOn ℝ (Set.Ici (-1)) (fun x => Real.log (density x)) := by
  refine ⟨convex_Ici (-1), ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ Set.Ici (-1) :=
    (convex_Ici (-1)) hx hy ha hb hab
  dsimp only
  rw [log_density_of_mem_support hx, log_density_of_mem_support hy,
    log_density_of_mem_support hxy]
  simp only [smul_eq_mul]
  nlinarith

end Conjecture7790
