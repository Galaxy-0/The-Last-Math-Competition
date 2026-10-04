import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-! Two-dimensional Jordan matrices, their genuine spectrum, and their Euclidean operator norm. -/

noncomputable section
open Matrix Polynomial

namespace Conjecture973

/-- A complex Jordan matrix with a real off-diagonal parameter. -/
def jordan (c : ℂ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![c, (r : ℂ); 0, c]

/-- The polynomial that removes the scalar part of a Jordan matrix. -/
def shiftedPolynomial (c : ℂ) : ℂ[X] := X - C c

theorem jordan_resolvent_det (c z : ℂ) (r : ℝ) :
    (algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) z - jordan c r).det = (z - c) ^ 2 := by
  simp [Matrix.det_fin_two, Matrix.algebraMap_matrix_apply, jordan, sq]

/-- The spectrum is computed in the actual complex matrix algebra. -/
theorem jordan_spectrum (c : ℂ) (r : ℝ) :
    spectrum ℂ (jordan c r) = {c} := by
  ext z
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, jordan_resolvent_det]
  simp [isUnit_iff_ne_zero, sub_eq_zero]

/-- Passing to the canonical Euclidean operator preserves this spectrum. -/
theorem jordan_operator_spectrum (c : ℂ) (r : ℝ) :
    spectrum ℂ (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (jordan c r)) = {c} := by
  rw [AlgEquiv.spectrum_eq (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)), jordan_spectrum]

/-- Polynomial evaluation in the actual matrix algebra gives the nilpotent part. -/
theorem aeval_shiftedPolynomial_jordan (c : ℂ) (r : ℝ) :
    Polynomial.aeval (jordan c r) (shiftedPolynomial c) = jordan 0 r := by
  simp only [shiftedPolynomial, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordan, Matrix.algebraMap_matrix_apply]

theorem nilpotent_jordan_apply (r : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (jordan 0 r) v =
      EuclideanSpace.single 0 ((r : ℂ) * v 1) := by
  apply (WithLp.equiv 2 (Fin 2 → ℂ)).injective
  simp only [Matrix.piLp_equiv_toEuclideanCLM, WithLp.equiv_single, Matrix.toLin'_apply]
  ext i
  fin_cases i <;>
    simp [jordan, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]

/-- The Euclidean operator norm is bounded below by its value on the second unit vector. -/
theorem nilpotent_jordan_operatorNorm_lower (r : ℝ) :
    |r| ≤ ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (jordan 0 r)‖ := by
  have h := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (jordan 0 r)).le_opNorm
    (EuclideanSpace.single 1 (1 : ℂ))
  simpa [nilpotent_jordan_apply, EuclideanSpace.single_apply] using h

/-- In fact this is the exact canonical Euclidean operator norm. -/
theorem nilpotent_jordan_operatorNorm (r : ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (jordan 0 r)‖ = |r| := by
  apply le_antisymm _ (nilpotent_jordan_operatorNorm_lower r)
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg r)
  intro v
  rw [nilpotent_jordan_apply, EuclideanSpace.norm_single, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v 1) (abs_nonneg r)

theorem jordan_shifted_operatorNorm (c : ℂ) (r : ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (Polynomial.aeval (jordan c r) (shiftedPolynomial c))‖ = |r| := by
  rw [aeval_shiftedPolynomial_jordan, nilpotent_jordan_operatorNorm]

theorem jordan_shifted_operatorNorm_lower (c : ℂ) (r : ℝ) :
    |r| ≤ ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (Polynomial.aeval (jordan c r) (shiftedPolynomial c))‖ :=
  (jordan_shifted_operatorNorm c r).ge

end Conjecture973
