import Objects240
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals

open Set MeasureTheory
open scoped ENNReal
namespace Mahler240
noncomputable section

lemma coords_measurePreserving : MeasurePreserving coords volume volume := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Four => ℝ)
  have h : MeasurePreserving e.symm volume volume := by
    refine ⟨e.symm.measurable, ?_⟩
    exact Measure.pi_map_piOptionEquivProd (fun _ : Four => (volume : Measure ℝ))
  have ht := Measure.measurePreserving_swap.comp (h.symm e.symm)
  convert ht using 1

lemma volume_cross3 : volume (cross (Fin 3)) = ENNReal.ofReal (4 / 3 : ℝ) := by
  have h := volume_sum_rpow_le (Fin 3) (p := 1) (by norm_num) 1
  norm_num [cross, Real.rpow_one] at h ⊢
  exact h

lemma volume_K : volume K = ENNReal.ofReal (8 / 3 : ℝ) := by
  rw [K, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, volume_cross3]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  norm_num

lemma measurableSet_P : MeasurableSet P := by
  have heq : P = ⋂ i : Fin 3, {x : E | |x.1| + |x.2 i| ≤ 1} := by
    ext x
    simp [P]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  exact (isClosed_le (by fun_prop) continuous_const).measurableSet

lemma slice_P (t : ℝ) : Prod.mk t ⁻¹' P =
    Set.univ.pi (fun _ : Fin 3 => Set.Icc (-(1 - |t|)) (1 - |t|)) := by
  ext x
  simp only [Set.mem_preimage, P, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    true_imp_iff, Set.mem_Icc]
  apply forall_congr'
  intro i
  rw [← abs_le]
  constructor <;> intro h <;> linarith

lemma volume_slice_P (t : ℝ) :
    volume (Prod.mk t ⁻¹' P) = ENNReal.ofReal (2 * (1 - |t|)) ^ 3 := by
  rw [slice_P, volume_pi_pi]
  simp only [Real.volume_Icc, sub_neg_eq_add, ← two_mul, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

lemma slice_integral : (∫ t in (-1 : ℝ)..1, (2 * (1 - |t|)) ^ 3) = 4 := by
  have hc : Continuous (fun t : ℝ => (2 * (1 - |t|)) ^ 3) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hp : (∫ t in (0 : ℝ)..1, (2 * (1 - |t|)) ^ 3) = 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..1, 8 * (1 - t) ^ 3 := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht0 : 0 ≤ t := by
          rw [Set.uIcc_of_le (by norm_num)] at ht
          exact ht.1
        change (2 * (1 - |t|)) ^ 3 = 8 * (1 - t) ^ 3
        rw [abs_of_nonneg ht0]
        ring
      _ = 8 * ∫ t in (0 : ℝ)..1, (1 - t) ^ 3 := by
        rw [intervalIntegral.integral_const_mul]
      _ = 8 * ∫ t in (0 : ℝ)..1, t ^ 3 := by
        have hh : (∫ t in (0 : ℝ)..1, (1 - t) ^ 3) = ∫ t in (0 : ℝ)..1, t ^ 3 := by
          simpa only [sub_self, sub_zero] using
            intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ 3) 1
              (a := (0 : ℝ)) (b := 1)
        exact congrArg (fun z : ℝ => 8 * z) hh
      _ = 2 := by rw [integral_pow]; norm_num
  have hn : (∫ t in (-1 : ℝ)..0, (2 * (1 - |t|)) ^ 3) = 2 := by
    have hh := intervalIntegral.integral_comp_neg (fun t : ℝ => (2 * (1 - |t|)) ^ 3)
      (a := (-1 : ℝ)) (b := 0)
    have heq : (∫ t in (-1 : ℝ)..0, (2 * (1 - |t|)) ^ 3) =
        ∫ t in (0 : ℝ)..1, (2 * (1 - |t|)) ^ 3 := by
      simpa only [abs_neg, neg_zero, neg_neg] using hh
    exact heq.trans hp
  rw [hn, hp]
  norm_num

lemma volume_P : volume P = 4 := by
  rw [Measure.volume_eq_prod, Measure.prod_apply measurableSet_P]
  simp_rw [volume_slice_P]
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (2 * (1 - |t|)) ^ 3
  have hs : Function.support f ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    apply abs_le.mp
    by_contra h
    have hle : 2 * (1 - |t|) ≤ 0 := by linarith
    have hz : f t = 0 := by simp [f, ENNReal.ofReal_eq_zero.mpr hle]
    exact ht hz
  change ∫⁻ t, f t = 4
  rw [← setLIntegral_eq_of_support_subset hs]
  have heq : (fun t => f t) =ᵐ[volume.restrict (Set.Icc (-1 : ℝ) 1)]
      (fun t => ENNReal.ofReal ((2 * (1 - |t|)) ^ 3)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht1 : |t| ≤ 1 := abs_le.mpr ht
    simp only [f, ENNReal.ofReal_pow (by linarith : 0 ≤ 2 * (1 - |t|))]
  rw [lintegral_congr_ae heq]
  have hi : IntegrableOn (fun t : ℝ => (2 * (1 - |t|)) ^ 3) (Set.Icc (-1) 1) :=
    (show Continuous (fun t : ℝ => (2 * (1 - |t|)) ^ 3) by fun_prop).continuousOn.integrableOn_Icc
  have hn : 0 ≤ᵐ[volume.restrict (Set.Icc (-1 : ℝ) 1)] (fun t => (2 * (1 - |t|)) ^ 3) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht1 : |t| ≤ 1 := abs_le.mpr ht
    exact pow_nonneg (by linarith) _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), slice_integral]
  norm_num

end
end Mahler240
