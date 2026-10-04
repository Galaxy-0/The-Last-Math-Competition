import Mathlib.Data.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Conjecture8586
noncomputable section
open Matrix
open scoped ComplexConjugate InnerProductSpace

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Frame (k : ℕ) := Matrix (Fin 2) (Fin k) ℂ

/-- Columns are orthonormal for the standard complex Euclidean inner product. -/
def OrthonormalColumns {k : ℕ} (Q : Frame k) : Prop := Qᴴ * Q = 1

/-- The actual matrix of the restriction followed by orthogonal projection. -/
def compression {k : ℕ} (T : Mat) (z : ℂ) (Q : Frame k) :
    Matrix (Fin k) (Fin k) ℂ := Qᴴ * (z • 1 - T) * Q

/-- The rank-of-compression definition printed in the supplied conjecture. -/
def statedRange (T : Mat) (k : ℕ) : Set ℂ :=
  {z | ∃ Q : Frame k, OrthonormalColumns Q ∧ (compression T z Q).rank ≤ k - 1}

/-- The usual scalar-compression convention, kept separate from the source's definition. -/
def scalarRange (T : Mat) (k : ℕ) : Set ℂ :=
  {z | ∃ Q : Frame k, OrthonormalColumns Q ∧ Qᴴ * T * Q = z • 1}

/-- An orthonormal-column matrix really induces a Euclidean linear isometry. -/
theorem orthonormal_columns_isometry {k : ℕ} (Q : Frame k)
    (hQ : OrthonormalColumns Q) : Isometry (Matrix.toEuclideanLin Q) := by
  have hcomp : (LinearMap.adjoint (Matrix.toEuclideanLin Q)).comp
      (Matrix.toEuclideanLin Q) = LinearMap.id := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simp_rw [Matrix.toEuclideanLin_eq_toLin]
    rw [← Matrix.toLin_mul, hQ, Matrix.toLin_one]
  have hinner : ∀ x y, ⟪Matrix.toEuclideanLin Q x, Matrix.toEuclideanLin Q y⟫_ℂ =
      ⟪x, y⟫_ℂ := by
    intro x y
    rw [← LinearMap.adjoint_inner_right]
    change ⟪x, ((LinearMap.adjoint (Matrix.toEuclideanLin Q)).comp
      (Matrix.toEuclideanLin Q)) y⟫_ℂ = ⟪x, y⟫_ℂ
    rw [hcomp]
    rfl
  exact ((Matrix.toEuclideanLin Q).isometryOfInner hinner).isometry

theorem scalarRange_subset_statedRange (T : Mat) (k : ℕ) :
    scalarRange T k ⊆ statedRange T k := by
  rintro z ⟨Q, hQ, hscalar⟩
  refine ⟨Q, hQ, ?_⟩
  have hz : compression T z Q = 0 := by
    calc
      compression T z Q = z • (Qᴴ * Q) - Qᴴ * T * Q := by
        simp [compression, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hQ, hscalar]; simp
  rw [hz, Matrix.rank_zero]
  exact Nat.zero_le _

def T : Mat := !![0, 0; 0, 1]
def midpoint : ℂ := 1 / 2
def c : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)
def Qone : Frame 1 := fun _ _ => c

@[simp] theorem star_c : (starRingEnd ℂ) c = c := by simp [c]

theorem c_squared : c ^ 2 = (1 / 2 : ℂ) := by
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : ((Real.sqrt (2 : ℝ))⁻¹) ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, hs]
    norm_num
  have hc := congrArg Complex.ofReal hr
  simpa only [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, c] using hc

theorem T_self_adjoint : Tᴴ = T := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [T, Matrix.conjTranspose_apply]

theorem Qone_orthonormal : OrthonormalColumns Qone := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Qone, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  ring_nf
  norm_num [c_squared]

theorem Qone_scalar_compression : Qoneᴴ * T * Qone = midpoint • 1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Qone, T, midpoint, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply]
  ring_nf
  norm_num [c_squared]

theorem midpoint_mem_scalar_one : midpoint ∈ scalarRange T 1 :=
  ⟨Qone, Qone_orthonormal, Qone_scalar_compression⟩

theorem midpoint_mem_stated_one : midpoint ∈ statedRange T 1 :=
  scalarRange_subset_statedRange T 1 midpoint_mem_scalar_one

theorem shifted_determinant : (midpoint • (1 : Mat) - T).det = -(1 / 4 : ℂ) := by
  norm_num [Matrix.det_fin_two, midpoint, T]

/-- Every full-dimensional isometric compression has nonzero determinant. -/
theorem compression_determinant_two (Q : Frame 2) (hQ : OrthonormalColumns Q) :
    (compression T midpoint Q).det = -(1 / 4 : ℂ) := by
  have hdet : Qᴴ.det * Q.det = 1 := by
    have h := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul, Matrix.det_one] using h
  calc
    (compression T midpoint Q).det = Qᴴ.det * (midpoint • (1 : Mat) - T).det * Q.det := by
      simp only [compression, Matrix.det_mul]
    _ = -(1 / 4 : ℂ) * (Qᴴ.det * Q.det) := by rw [shifted_determinant]; ring
    _ = -(1 / 4 : ℂ) := by rw [hdet]; ring

theorem compression_rank_two (Q : Frame 2) (hQ : OrthonormalColumns Q) :
    (compression T midpoint Q).rank = 2 := by
  have hu : IsUnit (compression T midpoint Q) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [compression_determinant_two Q hQ]
    norm_num
  simpa using Matrix.rank_of_isUnit (compression T midpoint Q) hu

theorem midpoint_not_mem_stated_two : midpoint ∉ statedRange T 2 := by
  rintro ⟨Q, hQ, hrank⟩
  rw [compression_rank_two Q hQ] at hrank
  norm_num at hrank

theorem stated_inclusion_fails : ¬ statedRange T 1 ⊆ statedRange T 2 := by
  intro h
  exact midpoint_not_mem_stated_two (h midpoint_mem_stated_one)

theorem midpoint_not_mem_scalar_two : midpoint ∉ scalarRange T 2 := by
  intro h
  exact midpoint_not_mem_stated_two (scalarRange_subset_statedRange T 2 h)

theorem scalar_inclusion_fails : ¬ scalarRange T 1 ⊆ scalarRange T 2 := by
  intro h
  exact midpoint_not_mem_scalar_two (h midpoint_mem_scalar_one)

def IncreasingRangesInDimensionTwo : Prop :=
  ∀ (M : Mat) (k : ℕ), 1 ≤ k → k < 2 → statedRange M k ⊆ statedRange M (k + 1)

theorem conjectured_inclusion_false : ¬ IncreasingRangesInDimensionTwo := by
  intro h
  exact stated_inclusion_fails (h T 1 (by norm_num) (by norm_num))

theorem full_counterexample :
    Tᴴ = T ∧ midpoint ∈ statedRange T 1 ∧ midpoint ∉ statedRange T 2 ∧
    midpoint ∈ scalarRange T 1 ∧ midpoint ∉ scalarRange T 2 :=
  ⟨T_self_adjoint, midpoint_mem_stated_one, midpoint_not_mem_stated_two,
    midpoint_mem_scalar_one, midpoint_not_mem_scalar_two⟩

#print axioms orthonormal_columns_isometry
#print axioms Qone_orthonormal
#print axioms Qone_scalar_compression
#print axioms compression_determinant_two
#print axioms compression_rank_two
#print axioms stated_inclusion_fails
#print axioms scalar_inclusion_fails
#print axioms conjectured_inclusion_false
#print axioms full_counterexample

end
end Conjecture8586
