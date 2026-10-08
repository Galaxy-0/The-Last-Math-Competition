import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set
namespace MahlerCube

def cube (n : ℕ) : Set (Fin n → ℝ) := Icc (fun _ => -1) (fun _ => 1)
/-- Polar for the standard coordinate pairing, with no normalization. -/
def polar (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∀ x∈K, ∑ i, x i*y i ≤ 1}
def crossPolytope (n : ℕ) : Set (Fin n → ℝ) := {y | ∑ i, |y i| ≤ 1}
def productVolume (K : Set (Fin n → ℝ)) : ℝ :=
  (volume K).toReal * (volume (polar K)).toReal

theorem cube_convex (n : ℕ) : Convex ℝ (cube n) := convex_Icc _ _
theorem cube_compact (n : ℕ) : IsCompact (cube n) := isCompact_Icc

theorem cube_symmetric (x : Fin n → ℝ) : -x∈cube n ↔ x∈cube n := by
  simp only [cube,mem_Icc,Pi.le_def,Pi.neg_apply]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> intro i
  all_goals have a:=h1 i; have b:=h2 i; linarith

theorem origin_interior (n : ℕ) : (0 : Fin n → ℝ) ∈ interior (cube n) := by
  rw [cube,← pi_univ_Icc,interior_pi_set (finite_univ)]
  simp [interior_Icc]

theorem polar_cube (n : ℕ) : polar (cube n)=crossPolytope n := by
  ext y
  constructor
  · intro hy
    let x : Fin n → ℝ := fun i => if 0≤y i then 1 else -1
    have hx : x∈cube n := by
      constructor <;> intro i <;> dsimp [x] <;> split_ifs <;> norm_num
    have he : ∀ i, x i*y i=|y i| := by
      intro i
      dsimp [x]
      split_ifs with h
      · simp [abs_of_nonneg h]
      · simp [abs_of_neg (lt_of_not_ge h)]
    simpa only [he] using hy x hx
  · intro hy x hx
    apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) hy
    have ha : |x i|≤1 := abs_le.mpr ⟨hx.1 i,hx.2 i⟩
    calc x i*y i ≤ |x i*y i| := le_abs_self _
         _ = |x i| * |y i| := abs_mul _ _
         _ ≤ 1*|y i| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
         _ = |y i| := one_mul _

theorem cube_volume (n : ℕ) : (volume (cube n)).toReal=2^n := by
  norm_num [cube,Real.volume_Icc_pi,ENNReal.toReal_prod]

theorem cross_volume (n : ℕ) [NeZero n] :
    (volume (crossPolytope n)).toReal=2^n/(n.factorial : ℝ) := by
  have hv := volume_sum_rpow_le (Fin n) (p:=1) (by norm_num) 1
  have hg : Real.Gamma ((n:ℝ)+1) = n.factorial := Real.Gamma_nat_eq_factorial n
  have hn : (0:ℝ) ≤ 2^n/(n.factorial : ℝ) := by positivity
  simpa [crossPolytope,Real.rpow_one,hg,Real.Gamma_add_one,Real.Gamma_one,hn,
    ENNReal.toReal_ofReal,div_nonneg] using congrArg ENNReal.toReal hv

theorem product_exact (n : ℕ) [NeZero n] :
    productVolume (cube n)=4^n/(n.factorial : ℝ) := by
  rw [productVolume,polar_cube,cube_volume,cross_volume]
  rw [← mul_div_assoc,← mul_pow]
  norm_num

theorem dimension_twelve : productVolume (cube 12)<8/Real.pi^2 := by
  rw [product_exact]
  have hpi := Real.pi_le_four
  have hp := Real.pi_pos
  have hsmall : (4:ℝ)^12/(Nat.factorial 12 : ℝ)<1/2 := by norm_num
  have hbound : (1:ℝ)/2≤8/Real.pi^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hp)).2
    nlinarith
  exact hsmall.trans_le hbound

theorem dimension_three : productVolume (cube 3)=32/3 := by
  rw [product_exact]
  norm_num

theorem dimension_three_not_claimed : productVolume (cube 3)≠8/Real.pi^2 := by
  rw [dimension_three]
  have hp := Real.two_le_pi
  intro h
  have he := (eq_div_iff (ne_of_gt (sq_pos_of_pos (by linarith : 0<Real.pi)))).mp h
  nlinarith

theorem counterexample : Convex ℝ (cube 12) ∧ IsCompact (cube 12) ∧
    (0 : Fin 12 → ℝ) ∈ interior (cube 12) ∧
    (∀ x, -x∈cube 12 ↔ x∈cube 12) ∧ productVolume (cube 12)<8/Real.pi^2 := by
  exact ⟨cube_convex _,cube_compact _,origin_interior _,cube_symmetric,dimension_twelve⟩

#print axioms cube_convex
#print axioms cube_compact
#print axioms cube_symmetric
#print axioms origin_interior
#print axioms polar_cube
#print axioms cube_volume
#print axioms cross_volume
#print axioms product_exact
#print axioms dimension_twelve
#print axioms dimension_three
#print axioms dimension_three_not_claimed
#print axioms counterexample
end MahlerCube
