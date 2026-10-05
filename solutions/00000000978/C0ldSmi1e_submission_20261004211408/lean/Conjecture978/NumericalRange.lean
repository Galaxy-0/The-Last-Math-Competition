import Conjecture978.Pencil
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Conjecture978

/-- The ordinary complex numerical range, with the Hermitian Euclidean unit condition. -/
def numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ v : Fin n → ℂ, (∑ i, Complex.normSq (v i)) = 1 ∧
    (∑ i, conj (v i) * (A.mulVec v) i) = z}

/-- The norm-square condition is precisely the usual Hermitian unit-vector equation. -/
theorem unit_condition_iff {n : ℕ} (v : Fin n → ℂ) :
    (∑ i, Complex.normSq (v i)) = 1 ↔ (∑ i, conj (v i) * v i) = 1 := by
  have h : ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) = ∑ i, conj (v i) * v i := by
    push_cast
    simp only [Complex.normSq_eq_conj_mul_self]
  rw [← h]
  exact_mod_cast Iff.rfl

/-- Every point of the closed unit disk is the numerical value of a unit vector. -/
theorem disk_quadratic_witness (z : ℂ) (hz : Complex.normSq z ≤ 1) :
    ∃ a b : ℂ, Complex.normSq a + Complex.normSq b = 1 ∧ 2 * conj a * b = z := by
  let s : ℝ := Real.sqrt (1 - Complex.normSq z)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs : s^2 = 1 - Complex.normSq z := Real.sq_sqrt (sub_nonneg.mpr hz)
  let a : ℝ := Real.sqrt ((1 + s) / 2)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha2 : a^2 = (1+s)/2 := Real.sq_sqrt (by positivity)
  have har : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
  refine ⟨(a : ℂ), z / (2 * (a : ℂ)), ?_, ?_⟩
  · rw [Complex.normSq_div, Complex.normSq_mul]
    norm_num [Complex.normSq_ofReal]
    have hrel : 2*a^2-1 = s := by linarith
    rw [← hrel] at hs
    field_simp
    nlinarith
  · simp only [map_natCast, Complex.conj_ofReal]
    field_simp

/-- Evaluation of the actual Hermitian quadratic form of the witness. -/
theorem quadraticForm_witness (v : Fin 2 → ℂ) :
    (∑ i, conj (v i) * (witness.mulVec v) i) = 2 * conj (v 0) * v 1 := by
  simp [witness, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The numerical range is exactly the norm-square unit disk. -/
theorem numericalRange_witness_normSq :
    numericalRange witness = {z : ℂ | Complex.normSq z ≤ 1} := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [quadraticForm_witness]
    simp only [Set.mem_setOf_eq, Complex.normSq_mul, Complex.normSq_conj]
    norm_num
    have hv' : Complex.normSq (v 0) + Complex.normSq (v 1) = 1 := by
      simpa [Fin.sum_univ_two] using hv
    nlinarith [sq_nonneg (Complex.normSq (v 0) - Complex.normSq (v 1))]
  · intro hz
    obtain ⟨a,b,hab,hz'⟩ := disk_quadratic_witness z hz
    refine ⟨![a,b], ?_, ?_⟩
    · simpa [Fin.sum_univ_two] using hab
    · rw [quadraticForm_witness]
      exact hz'

/-- The genuine numerical range of the matrix is the closed complex unit disk. -/
theorem numericalRange_witness_eq :
    numericalRange witness = Metric.closedBall (0 : ℂ) 1 := by
  rw [numericalRange_witness_normSq]
  ext z
  simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    nlinarith [norm_nonneg z]
  · intro h
    nlinarith [norm_nonneg z]

/-- Its actual topological boundary is the complex unit circle. -/
theorem frontier_numericalRange_witness :
    frontier (numericalRange witness) = Metric.sphere (0 : ℂ) 1 := by
  rw [numericalRange_witness_eq]
  exact frontier_closedBall _ (by norm_num)

end Conjecture978
