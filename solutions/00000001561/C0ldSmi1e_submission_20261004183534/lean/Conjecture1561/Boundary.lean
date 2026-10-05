import Conjecture1561.Definitions
import Mathlib.Tactic

noncomputable section
open scoped InnerProductSpace

namespace Conjecture1561

@[simp] theorem sphereS2_mem_iff (x : Space) : x ∈ sphereS2 ↔ ‖x‖ = 1 := by
  simp [sphereS2, Metric.mem_sphere]

/-- For unit vectors the actual angle is the great-circle distance in radians. -/
theorem sphericalDistance_eq_arccos_inner (x y : Space)
    (hx : x ∈ sphereS2) (hy : y ∈ sphereS2) :
    sphericalDistance x y = Real.arccos (@inner ℝ Space _ x y) := by
  simp [sphericalDistance, InnerProductGeometry.angle,
    (sphereS2_mem_iff x).mp hx, (sphereS2_mem_iff y).mp hy]

/-- Every pole has an actual orthogonal unit vector on the sphere. -/
theorem exists_unit_orthogonal (v : Space) (hv : v ∈ sphereS2) :
    ∃ w : Space, ‖w‖ = 1 ∧ @inner ℝ Space _ v w = 0 := by
  have hvnorm := (sphereS2_mem_iff v).mp hv
  have hvne : v ≠ 0 := by
    intro h
    simp [h] at hvnorm
  letI : Fact (Module.finrank ℝ Space = 2 + 1) := ⟨by simp [Space]⟩
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2 hvne
  refine ⟨(b 0 : Space), ?_, ?_⟩
  · exact b.orthonormal.norm_eq_one 0
  · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b 0).property

/-- The two opposite equatorial points lie in every closed hemisphere. -/
theorem closedHemisphere_antipodal_pair (v : Space) (hv : v ∈ sphereS2) :
    ∃ w : Space, w ∈ closedHemisphere v ∧ -w ∈ closedHemisphere v ∧
      sphericalDistance w (-w) = Real.pi := by
  obtain ⟨w, hw, horth⟩ := exists_unit_orthogonal v hv
  have hwne : w ≠ 0 := by
    intro h
    simp [h] at hw
  refine ⟨w, ?_, ?_, ?_⟩
  · exact ⟨(sphereS2_mem_iff w).mpr hw, horth.ge⟩
  · constructor
    · simpa using hw
    · simp [inner_neg_right, horth]
  · exact InnerProductGeometry.angle_self_neg_of_nonzero hwne

/-- A closed hemisphere violates the exact bound by a pair at distance π. -/
theorem closedHemisphere_bad_pair (v : Space) (hv : v ∈ sphereS2) :
    ∃ x ∈ closedHemisphere v, ∃ y ∈ closedHemisphere v,
      Real.pi / 2 < sphericalDistance x y := by
  obtain ⟨w, hw, hnw, hdist⟩ := closedHemisphere_antipodal_pair v hv
  refine ⟨w, hw, -w, hnw, ?_⟩
  rw [hdist]
  linarith [Real.pi_pos]

theorem closedHemisphere_not_admissible (v : Space) (hv : v ∈ sphereS2) :
    ¬ Admissible (closedHemisphere v) := by
  intro h
  obtain ⟨x, hx, y, hy, hdist⟩ := closedHemisphere_bad_pair v hv
  exact (not_lt_of_ge (h.2 x hx y hy)) hdist

end Conjecture1561
