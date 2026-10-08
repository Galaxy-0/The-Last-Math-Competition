import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Tactic

open Finset Set
namespace TensorMaximum
variable {ι : Type*} [Fintype ι]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)] [∀ i, Nontrivial (E i)]

noncomputable def unitTuples : Set (∀ i, E i) := {v | ∀ i, ‖v i‖ = 1}

theorem unitTuples_nonempty : (unitTuples (E := E)).Nonempty := by
  choose u hu using fun i => exists_norm_eq (E i) (show (0:ℝ) ≤ 1 by norm_num)
  exact ⟨u,hu⟩

theorem unitTuples_compact : IsCompact (unitTuples (E := E)) := by
  have hc := isCompact_pi_infinite (fun i : ι => isCompact_sphere (0 : E i) 1)
  simpa [unitTuples, mem_sphere_zero_iff_norm] using hc

theorem unit_gain_bound (f : ContinuousMultilinearMap ℝ E ℝ) {v : ∀ i, E i}
    (hv : v ∈ unitTuples) : ‖f v‖ ≤ ‖f‖ := by
  have hvi : ∀ i, ‖v i‖ = 1 := hv
  simpa [hvi] using f.le_opNorm v

theorem sphere_bound_global (f : ContinuousMultilinearMap ℝ E ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hs : ∀ v ∈ unitTuples, ‖f v‖ ≤ B) :
    ∀ m, ‖f m‖ ≤ B * ∏ i, ‖m i‖ := by
  classical
  intro m
  by_cases hz : ∃ i, m i = 0
  · obtain ⟨i,hi⟩ := hz
    rw [f.map_coord_zero i hi, norm_zero]
    positivity
  · have hm : ∀ i, m i ≠ 0 := by simpa using hz
    let v : ∀ i, E i := fun i => ‖m i‖⁻¹ • m i
    have hv : v ∈ unitTuples := by
      intro i
      simp [v, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (norm_nonneg (m i)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hm i))]
    have hp : (∏ i, ‖m i‖) * (∏ i, ‖m i‖⁻¹) = 1 := by
      rw [← prod_mul_distrib]
      exact prod_eq_one fun i hi => mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hm i))
    have he : f m = (∏ i, ‖m i‖) • f v := by
      dsimp [v]
      rw [f.map_smul_univ]
      change f m = (∏ i, ‖m i‖) * ((∏ i, ‖m i‖⁻¹) * f m)
      rw [← mul_assoc, hp, one_mul]
    have hprod : 0 ≤ ∏ i, ‖m i‖ := prod_nonneg fun i hi => norm_nonneg _
    calc
      ‖f m‖ = (∏ i, ‖m i‖) * ‖f v‖ := by rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hprod]
      _ ≤ (∏ i, ‖m i‖) * B := mul_le_mul_of_nonneg_left (hs v hv) hprod
      _ = B * ∏ i, ‖m i‖ := mul_comm _ _

theorem norm_attained (f : ContinuousMultilinearMap ℝ E ℝ) :
    ∃ v ∈ unitTuples, ‖f v‖ = ‖f‖ ∧ ∀ w ∈ unitTuples, ‖f w‖ ≤ ‖f v‖ := by
  obtain ⟨v,hv,hmax⟩ := unitTuples_compact.exists_isMaxOn unitTuples_nonempty
    f.cont.norm.continuousOn
  have hupper : ‖f‖ ≤ ‖f v‖ := ContinuousMultilinearMap.opNorm_le_bound
    (norm_nonneg _) (sphere_bound_global f (norm_nonneg _) hmax)
  exact ⟨v,hv,le_antisymm (unit_gain_bound f hv) hupper,hmax⟩

theorem zero_tensor_attained : ∃ v ∈ unitTuples (E := E),
    ‖(0 : ContinuousMultilinearMap ℝ E ℝ) v‖ = 0 := by
  obtain ⟨v,hv⟩ := unitTuples_nonempty (E := E)
  exact ⟨v,hv,by simp⟩

#print axioms unitTuples_nonempty
#print axioms unitTuples_compact
#print axioms unit_gain_bound
#print axioms sphere_bound_global
#print axioms norm_attained
#print axioms zero_tensor_attained
end TensorMaximum
