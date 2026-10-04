import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Set MeasureTheory Metric Filter
open scoped Pointwise Topology
noncomputable section

namespace Counterexample

def K : Set ℝ := Icc 0 1
def L : Set ℝ := Icc 0 2

theorem bodies : IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
    IsCompact L ∧ Convex ℝ L ∧ (interior L).Nonempty := by
  refine ⟨isCompact_Icc, convex_Icc 0 1, ?_, isCompact_Icc, convex_Icc 0 2, ?_⟩
  · exact ⟨1/2, by norm_num [K, interior_Icc]⟩
  · exact ⟨1, by norm_num [L, interior_Icc]⟩

theorem minkowski_sum : K + L = Icc 0 3 := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    change 0 ≤ x ∧ x ≤ 1 at hx
    change 0 ≤ y ∧ y ≤ 2 at hy
    change 0 ≤ x + y ∧ x + y ≤ 3
    constructor <;> linarith
  · intro hz
    refine ⟨z/3, ?_, 2*z/3, ?_, by ring⟩
    · change 0 ≤ z/3 ∧ z/3 ≤ 1
      constructor <;> linarith [hz.1, hz.2]
    · change 0 ≤ 2*z/3 ∧ 2*z/3 ≤ 2
      constructor <;> linarith [hz.1, hz.2]

def deficit : ℝ := (volume (K + L)).toReal -
  ((volume K).toReal + (volume L).toReal)

theorem volumes : (volume K).toReal = 1 ∧ (volume L).toReal = 2 ∧
    (volume (K + L)).toReal = 3 := by
  rw [minkowski_sum]
  norm_num [K, L, Real.volume_Icc]

theorem zero_deficit : deficit = 0 := by
  unfold deficit
  rw [volumes.1, volumes.2.1, volumes.2.2]
  norm_num

theorem rigid_distance (f g : ℝ → ℝ) (hf : Isometry f) (hg : Isometry g) :
    (1/2 : ℝ) ≤ hausdorffDist (f '' L) (g '' K) := by
  have hs : IsCompact (g '' K) := isCompact_Icc.image hg.continuous
  have ht : IsCompact (f '' L) := isCompact_Icc.image hf.continuous
  have hsn : (g '' K).Nonempty := ⟨g 0, ⟨0, by norm_num [K], rfl⟩⟩
  have htn : (f '' L).Nonempty := ⟨f 0, ⟨0, by norm_num [L], rfl⟩⟩
  have fin := hausdorffEdist_ne_top_of_nonempty_of_bounded htn hsn ht.isBounded hs.isBounded
  obtain ⟨a, ha, hea⟩ := hs.exists_infDist_eq_dist hsn (f 0)
  obtain ⟨b, hb, heb⟩ := hs.exists_infDist_eq_dist hsn (f 2)
  have h0 := infDist_le_hausdorffDist_of_mem
    (show f 0 ∈ f '' L from ⟨0, by norm_num [L], rfl⟩) fin
  have h2 := infDist_le_hausdorffDist_of_mem
    (show f 2 ∈ f '' L from ⟨2, by norm_num [L], rfl⟩) fin
  rw [hea] at h0
  rw [heb] at h2
  have hab := dist_le_diam_of_mem hs.isBounded ha hb
  have hd : diam (g '' K) = 1 := by
    rw [hg.diam_image]
    norm_num [K, Real.diam_Icc]
  rw [hd] at hab
  have hf02 : dist (f 0) (f 2) = 2 := by
    rw [hf.dist_eq]
    norm_num [Real.dist_eq]
  have htri := dist_triangle (f 0) a (f 2)
  have htri2 := dist_triangle a b (f 2)
  rw [dist_comm b (f 2)] at htri2
  linarith

theorem no_vanishing_estimate (m : ℕ → ℝ) (hm : Tendsto m atTop (𝓝 0)) :
    ¬ ∃ N, ∀ n ≥ N, ∃ f g : ℝ → ℝ, Isometry f ∧ Isometry g ∧
      hausdorffDist (f '' L) (g '' K) ≤ m n := by
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (hm.eventually (Iio_mem_nhds (show (0:ℝ) < 1/2 by norm_num)))
  rintro ⟨N, hN⟩
  obtain ⟨f, g, hf, hg, hbound⟩ := hN (max N M) (le_max_left _ _)
  have hsmall := hM (max N M) (le_max_right _ _)
  have hlarge := rigid_distance f g hf hg
  change m (max N M) < 1/2 at hsmall
  linarith

def epsilon (n : ℕ) : ℝ := 1 / ((n:ℝ) + 1)

theorem epsilon_positive (n : ℕ) : 0 < epsilon n := by
  unfold epsilon
  positivity

theorem epsilon_limit : Tendsto epsilon atTop (𝓝 0) := by
  unfold epsilon
  simpa only [one_div, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop))

theorem no_claimed_power (C : ℝ) :
    ¬ ∃ N, ∀ n ≥ N, ∃ f g : ℝ → ℝ, Isometry f ∧ Isometry g ∧
      hausdorffDist (f '' L) (g '' K) ≤ C * Real.sqrt (epsilon n) := by
  apply no_vanishing_estimate
  have hs : Tendsto (fun n => Real.sqrt (epsilon n)) atTop (𝓝 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp epsilon_limit
  simpa using tendsto_const_nhds.mul hs

end Counterexample
#print axioms Counterexample.bodies
#print axioms Counterexample.minkowski_sum
#print axioms Counterexample.zero_deficit
#print axioms Counterexample.rigid_distance
#print axioms Counterexample.no_vanishing_estimate
#print axioms Counterexample.no_claimed_power
