import Conjecture1561.Definitions
import Mathlib.Tactic

noncomputable section
open scoped RealInnerProductSpace

namespace Conjecture1561

/-- A unit point strictly inside the hemisphere, displaced toward `w`. -/
def interiorLeft (v w : Space) : Space := (3 / 5 : ℝ) • v + (4 / 5 : ℝ) • w

/-- A second interior point, displaced the same amount in the opposite direction. -/
def interiorRight (v w : Space) : Space := (3 / 5 : ℝ) • v - (4 / 5 : ℝ) • w

theorem interiorLeft_norm {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : @inner ℝ Space _ v w = 0) : ‖interiorLeft v w‖ = 1 := by
  have hwv : @inner ℝ Space _ w v = 0 := by rw [real_inner_comm]; exact hvw
  have hs : ‖interiorLeft v w‖ ^ 2 = (1 : ℝ) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [interiorLeft, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hvw, hwv, real_inner_self_eq_norm_sq, hv, hw]
    norm_num [norm_smul, hv, hw]
  nlinarith [norm_nonneg (interiorLeft v w)]

theorem interiorRight_norm {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : @inner ℝ Space _ v w = 0) : ‖interiorRight v w‖ = 1 := by
  have hwv : @inner ℝ Space _ w v = 0 := by rw [real_inner_comm]; exact hvw
  have hs : ‖interiorRight v w‖ ^ 2 = (1 : ℝ) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [interiorRight, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hvw, hwv, real_inner_self_eq_norm_sq, hv, hw]
    norm_num [norm_smul, hv, hw]
  nlinarith [norm_nonneg (interiorRight v w)]

theorem inner_center_left {v w : Space} (hv : ‖v‖ = 1)
    (hvw : @inner ℝ Space _ v w = 0) :
    @inner ℝ Space _ v (interiorLeft v w) = 3 / 5 := by
  simp only [interiorLeft, inner_add_right, real_inner_smul_right, hvw,
    real_inner_self_eq_norm_sq, hv]
  norm_num

theorem inner_center_right {v w : Space} (hv : ‖v‖ = 1)
    (hvw : @inner ℝ Space _ v w = 0) :
    @inner ℝ Space _ v (interiorRight v w) = 3 / 5 := by
  simp only [interiorRight, inner_sub_right, real_inner_smul_right, hvw,
    real_inner_self_eq_norm_sq, hv]
  norm_num

theorem interiorLeft_mem_open {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : @inner ℝ Space _ v w = 0) : interiorLeft v w ∈ openHemisphere v := by
  constructor
  · simpa only [sphereS2, Metric.mem_sphere, dist_zero_right] using interiorLeft_norm hv hw hvw
  · rw [inner_center_left hv hvw]
    norm_num

theorem interiorRight_mem_open {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : @inner ℝ Space _ v w = 0) : interiorRight v w ∈ openHemisphere v := by
  constructor
  · simpa only [sphereS2, Metric.mem_sphere, dist_zero_right] using interiorRight_norm hv hw hvw
  · rw [inner_center_right hv hvw]
    norm_num

theorem inner_interior_pair {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : @inner ℝ Space _ v w = 0) :
    @inner ℝ Space _ (interiorLeft v w) (interiorRight v w) = -(7 / 25 : ℝ) := by
  have hwv : @inner ℝ Space _ w v = 0 := by rw [real_inner_comm]; exact hvw
  simp only [interiorLeft, interiorRight, inner_add_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hvw, hwv, real_inner_self_eq_norm_sq, hv, hw]
  norm_num [norm_smul, hv, hw]

theorem interior_distance_gt {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : @inner ℝ Space _ v w = 0) :
    Real.pi / 2 < sphericalDistance (interiorLeft v w) (interiorRight v w) := by
  rw [sphericalDistance, InnerProductGeometry.angle, inner_interior_pair hv hw hvw,
    interiorLeft_norm hv hw hvw, interiorRight_norm hv hw hvw, one_mul, div_one]
  apply lt_of_not_ge
  intro h
  have hnonneg := Real.arccos_le_pi_div_two.mp h
  norm_num at hnonneg

/-- These two actual interior points violate the pairwise spherical-distance condition. -/
theorem interior_bad_pair {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : @inner ℝ Space _ v w = 0) :
    ∃ x ∈ openHemisphere v, ∃ y ∈ openHemisphere v,
      Real.pi / 2 < sphericalDistance x y :=
  ⟨interiorLeft v w, interiorLeft_mem_open hv hw hvw,
    interiorRight v w, interiorRight_mem_open hv hw hvw, interior_distance_gt hv hw hvw⟩

end Conjecture1561
