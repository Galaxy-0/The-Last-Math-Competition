import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Tactic

noncomputable section
open Matrix Polynomial
namespace Conjecture5960

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def cosine (t : ℝ) : ℝ := (1-t^2)/(1+t^2)
def sine (t : ℝ) : ℝ := 2*t/(1+t^2)
def rotation (t : ℝ) : Mat2 := !![cosine t, -sine t; sine t, cosine t]
def diagonal : Mat2 := !![1, 0; 0, 3]
def matrixFamily (t : ℝ) : Mat2 := rotation t * diagonal * (rotation t).transpose

def firstVector (t : ℝ) : Plane :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![cosine t, sine t]
def secondVector (t : ℝ) : Plane :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-sine t, cosine t]

theorem denominator_pos (t : ℝ) : 0 < 1+t^2 := by positivity

theorem cosine_sq_add_sine_sq (t : ℝ) : cosine t ^ 2 + sine t ^ 2 = 1 := by
  unfold cosine sine
  field_simp [(denominator_pos t).ne']
  ring

theorem transpose_rotation_mul_rotation (t : ℝ) :
    (rotation t).transpose * rotation t = 1 := by
  have h := cosine_sq_add_sine_sq t
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotation, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith only [h]

theorem rotation_mul_transpose_rotation (t : ℝ) :
    rotation t * (rotation t).transpose = 1 := by
  have h := cosine_sq_add_sine_sq t
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotation, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith only [h]

theorem det_rotation (t : ℝ) : (rotation t).det = 1 := by
  simpa [rotation, Matrix.det_fin_two, pow_two] using cosine_sq_add_sine_sq t

theorem matrixFamily_explicit (t : ℝ) : matrixFamily t =
    !![cosine t ^ 2 + 3*sine t ^ 2, -2*cosine t*sine t;
       -2*cosine t*sine t, sine t ^ 2 + 3*cosine t ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixFamily, rotation, diagonal, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem matrixFamily_isSymm (t : ℝ) : (matrixFamily t).IsSymm := by
  rw [matrixFamily_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem matrixFamily_trace (t : ℝ) :
    matrixFamily t 0 0 + matrixFamily t 1 1 = 4 := by
  rw [matrixFamily_explicit]
  change (cosine t^2+3*sine t^2)+(sine t^2+3*cosine t^2) = 4
  nlinarith only [cosine_sq_add_sine_sq t]

theorem det_matrixFamily (t : ℝ) : (matrixFamily t).det = 3 := by
  simp only [matrixFamily, Matrix.det_mul, Matrix.det_transpose, det_rotation]
  norm_num [diagonal, Matrix.det_fin_two]

theorem charpoly_matrixFamily (t : ℝ) :
    (matrixFamily t).charpoly = (X-C (1 : ℝ))*(X-C (3 : ℝ)) := by
  have hform : (matrixFamily t).charpoly =
      X^2 - C (matrixFamily t 0 0 + matrixFamily t 1 1)*X +
        C ((matrixFamily t).det) := by
    simp [Matrix.charpoly, Matrix.det_fin_two, Matrix.charmatrix_apply, map_add, map_sub,
      map_mul]
    ring
  rw [hform, matrixFamily_trace, det_matrixFamily]
  rw [show (4 : ℝ) = 1+3 by norm_num, map_add]
  simp
  ring

theorem spectrum_matrixFamily (t : ℝ) : spectrum ℝ (matrixFamily t) = {1, 3} := by
  ext z
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
  have hdet : (algebraMap ℝ Mat2 z - matrixFamily t).det = (z-1)*(z-3) := by
    calc
      _ = z^2-(matrixFamily t 0 0+matrixFamily t 1 1)*z+(matrixFamily t).det := by
        simp [Matrix.det_fin_two, Matrix.algebraMap_matrix_apply]
        ring
      _ = _ := by rw [matrixFamily_trace, det_matrixFamily]; ring
  rw [hdet]
  simp [isUnit_iff_ne_zero, sub_eq_zero]
  tauto

theorem spectrum_operator_matrixFamily (t : ℝ) :
    spectrum ℝ (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (matrixFamily t)) = {1, 3} := by
  rw [AlgEquiv.spectrum_eq (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)),
    spectrum_matrixFamily]

theorem firstVector_norm (t : ℝ) : ‖firstVector t‖ = 1 := by
  have h : ‖firstVector t‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa [firstVector, Fin.sum_univ_two, Real.norm_eq_abs] using cosine_sq_add_sine_sq t
  nlinarith [norm_nonneg (firstVector t)]

theorem secondVector_norm (t : ℝ) : ‖secondVector t‖ = 1 := by
  have h : ‖secondVector t‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa [secondVector, Fin.sum_univ_two, Real.norm_eq_abs, add_comm] using
      cosine_sq_add_sine_sq t
  nlinarith [norm_nonneg (secondVector t)]

theorem firstVector_eigen (t : ℝ) :
    Matrix.toEuclideanLin (matrixFamily t) (firstVector t) = firstVector t := by
  have h := cosine_sq_add_sine_sq t
  ext i
  fin_cases i <;>
    simp [Matrix.toEuclideanLin_apply, matrixFamily_explicit, firstVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
  · nlinarith only [h, congrArg (fun a : ℝ => cosine t*a) h]
  · nlinarith only [h, congrArg (fun a : ℝ => sine t*a) h]

theorem secondVector_eigen (t : ℝ) :
    Matrix.toEuclideanLin (matrixFamily t) (secondVector t) = (3 : ℝ) • secondVector t := by
  have h := cosine_sq_add_sine_sq t
  ext i
  fin_cases i <;>
    simp [Matrix.toEuclideanLin_apply, matrixFamily_explicit, secondVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
  · nlinarith only [h, congrArg (fun a : ℝ => sine t*a) h]
  · nlinarith only [h, congrArg (fun a : ℝ => cosine t*a) h]

theorem firstVector_hasEigenvector (t : ℝ) :
    Module.End.HasEigenvector (Matrix.toEuclideanLin (matrixFamily t)) 1 (firstVector t) := by
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, one_smul]
    exact firstVector_eigen t
  · exact norm_ne_zero_iff.mp (by rw [firstVector_norm]; norm_num)

theorem secondVector_hasEigenvector (t : ℝ) :
    Module.End.HasEigenvector (Matrix.toEuclideanLin (matrixFamily t)) 3 (secondVector t) := by
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    exact secondVector_eigen t
  · exact norm_ne_zero_iff.mp (by rw [secondVector_norm]; norm_num)

@[fun_prop] theorem continuous_cosine : Continuous cosine := by
  unfold cosine
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact (denominator_pos t).ne'

@[fun_prop] theorem continuous_sine : Continuous sine := by
  unfold sine
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact (denominator_pos t).ne'

@[fun_prop] theorem continuous_rotation : Continuous rotation := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [rotation] <;> fun_prop

@[fun_prop] theorem continuous_matrixFamily : Continuous matrixFamily := by
  unfold matrixFamily
  fun_prop

/-- The two displayed eigenvectors form orthogonal unit directions. -/
theorem firstVector_inner_secondVector (t : ℝ) :
    @inner ℝ Plane _ (firstVector t) (secondVector t) = 0 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, firstVector, secondVector,
    dotProduct, Fin.sum_univ_two]
  ring

/-- Every vector decomposes along the actual two eigenvector directions. -/
theorem vector_decomposition (t : ℝ) (x : Plane) :
    x = (cosine t*x 0+sine t*x 1) • firstVector t +
      (-sine t*x 0+cosine t*x 1) • secondVector t := by
  have h := cosine_sq_add_sine_sq t
  ext i
  fin_cases i <;> simp [firstVector, secondVector]
  · nlinarith only [congrArg (fun a : ℝ => x 0*a) h]
  · nlinarith only [congrArg (fun a : ℝ => x 1*a) h]

end Conjecture5960
