import Conjecture1561.Boundary
import Conjecture1561.Interior

noncomputable section

namespace Conjecture1561

/-- The strict interior also contains a pair violating the stated bound. -/
theorem openHemisphere_bad_pair (v : Space) (hv : v ∈ sphereS2) :
    ∃ x ∈ openHemisphere v, ∃ y ∈ openHemisphere v,
      Real.pi / 2 < sphericalDistance x y := by
  obtain ⟨w, hw, horth⟩ := exists_unit_orthogonal v hv
  exact interior_bad_pair ((sphereS2_mem_iff v).mp hv) hw horth

theorem openHemisphere_not_admissible (v : Space) (hv : v ∈ sphereS2) :
    ¬ Admissible (openHemisphere v) := by
  intro h
  obtain ⟨x, hx, y, hy, hdist⟩ := openHemisphere_bad_pair v hv
  exact (not_lt_of_ge (h.2 x hx y hy)) hdist

/-- Infeasibility excludes a maximizer for every actual objective measure. -/
theorem closedHemisphere_not_maximizer (μ : MeasureTheory.Measure Space)
    (v : Space) (hv : v ∈ sphereS2) :
    ¬ IsAreaMaximizer μ (closedHemisphere v) := by
  intro h
  exact closedHemisphere_not_admissible v hv h.1

theorem openHemisphere_not_maximizer (μ : MeasureTheory.Measure Space)
    (v : Space) (hv : v ∈ sphereS2) :
    ¬ IsAreaMaximizer μ (openHemisphere v) := by
  intro h
  exact openHemisphere_not_admissible v hv h.1

theorem no_hemisphere_extremizer (μ : MeasureTheory.Measure Space) :
    ¬ HemisphereExtremizerClaim μ := by
  rintro ⟨v, hv, hmax⟩
  exact closedHemisphere_not_maximizer μ v hv hmax

/-- The necessary first clause is false for actual Hausdorff area. -/
theorem conjecture_false : ¬ ConjectureFirstClause :=
  no_hemisphere_extremizer sphericalArea

end Conjecture1561
