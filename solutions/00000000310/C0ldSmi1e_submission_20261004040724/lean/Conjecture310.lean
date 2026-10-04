import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic

/-!
# Disproof of TLMC conjecture 00000000310

The plane below carries its Euclidean metric. Distance to the integers is
Mathlib's infimum of real distances to the integer lattice. The defining
condition permits a separate positive constant for each unit direction;
this is weaker than requiring one constant uniformly in the direction.
-/

noncomputable section

open scoped InnerProductSpace

namespace Conjecture310

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Distance from a real number to the nearest integer, expressed as an infimum. -/
def distanceToIntegers (t : ℝ) : ℝ :=
  Metric.infDist t (Set.range (Int.cast : ℤ → ℝ))

@[simp] theorem distanceToIntegers_zero : distanceToIntegers 0 = 0 := by
  apply Metric.infDist_zero_of_mem
  exact ⟨0, by simp⟩

/-- The set in the conjecture, with a direction-dependent positive constant
and the inequality required at every positive integer denominator. -/
def BadAbs : Set Plane :=
  {x | ∀ e : Plane, ‖e‖ = 1 →
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 0 < q →
      c / (q : ℝ) < distanceToIntegers ((q : ℝ) * ⟪e, x⟫_ℝ)}

/-- Every point of the Euclidean plane has a perpendicular unit direction. -/
theorem perpendicular_unit (x : Plane) :
    ∃ e : Plane, ‖e‖ = 1 ∧ ⟪e, x⟫_ℝ = 0 := by
  by_cases hx : x = 0
  · refine ⟨!₂[1, 0], ?_, ?_⟩
    · simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    · simp [hx]
  · let y : Plane := !₂[-x 1, x 0]
    have hy : y ≠ 0 := by
      intro h
      apply hx
      ext i
      fin_cases i
      · have h1 := congrArg (fun v : Plane => v 1) h
        simpa [y] using h1
      · have h0 := congrArg (fun v : Plane => v 0) h
        simpa [y] using h0
    have hyinner : ⟪y, x⟫_ℝ = 0 := by
      simp [PiLp.inner_apply, Fin.sum_univ_two, y]
      ring
    refine ⟨‖y‖⁻¹ • y, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)
    · rw [real_inner_smul_left, hyinner, mul_zero]

/-- The obstructing direction has zero distance to the integers for every
real multiplier, in particular every positive integer denominator. -/
theorem perpendicular_unit_zero_distance (x : Plane) :
    ∃ e : Plane, ‖e‖ = 1 ∧
      ∀ q : ℝ, distanceToIntegers (q * ⟪e, x⟫_ℝ) = 0 := by
  obtain ⟨e, he, hinner⟩ := perpendicular_unit x
  refine ⟨e, he, ?_⟩
  intro q
  simp [hinner]

/-- No point satisfies the conjecture's defining approximation condition. -/
theorem badAbs_eq_empty : BadAbs = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨e, he, hzero⟩ := perpendicular_unit_zero_distance x
  obtain ⟨c, hc, hbound⟩ := hx e he
  have h := hbound 1 (by norm_num)
  simp only [Nat.cast_one, div_one, one_mul] at h
  have hz : distanceToIntegers ⟪e, x⟫_ℝ = 0 := by
    simpa using hzero 1
  rw [hz] at h
  exact (not_lt_of_ge (le_of_lt hc)) h

/-- Mathlib uses Hausdorff dimension zero for the empty set. -/
theorem dimH_badAbs_eq_zero : dimH BadAbs = 0 := by
  rw [badAbs_eq_empty, dimH_empty]

/-- The asserted full Hausdorff dimension is false. -/
theorem dimH_badAbs_ne_two : dimH BadAbs ≠ 2 := by
  rw [dimH_badAbs_eq_zero]
  norm_num

/-- Its intersection with every set is empty, without assumptions on that set. -/
theorem badAbs_inter_eq_empty (K : Set Plane) : BadAbs ∩ K = ∅ := by
  simp [badAbs_eq_empty]

theorem dimH_badAbs_inter_eq_zero (K : Set Plane) :
    dimH (BadAbs ∩ K) = 0 := by
  rw [badAbs_inter_eq_empty, dimH_empty]

end Conjecture310
