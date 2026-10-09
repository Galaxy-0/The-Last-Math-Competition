import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
open scoped Matrix
namespace KrylovNilpotent

abbrev M := Matrix (Fin 2) (Fin 2) ℂ
def A (t : ℝ) : M := !![0, t; 0, 0]
def b : Fin 2 → ℂ := ![0, 1]

/-- The Euclidean norm, written explicitly in complex coordinates. -/
def euclideanNorm (v : Fin 2 → ℂ) : ℝ := Real.sqrt (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2)

/-- The genuine first Krylov space span{A^0 b}=span{b}. -/
def krylovOne : Submodule ℂ (Fin 2 → ℂ) := Submodule.span ℂ {b}

theorem b_unit : euclideanNorm b = 1 := by norm_num [euclideanNorm, b]

theorem squared_zero (t : ℝ) : A t ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, A, Matrix.mul_apply, Fin.sum_univ_two]

theorem high_powers_zero (t : ℝ) (n : ℕ) (hn : 2 ≤ n) : A t ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, squared_zero, zero_mul]

theorem spectrum_fixed (t : ℝ) : spectrum ℂ (A t) = {0} := by
  ext z
  simp [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two,
    Matrix.algebraMap_eq_diagonal, A, isUnit_iff_ne_zero]

/-- The canonical matrix exponential is evaluated from its convergent finite-support series. -/
theorem exponential_eq (t : ℝ) : NormedSpace.exp ℂ (A t) = 1 + A t := by
  rw [NormedSpace.exp_eq_tsum]
  dsimp only
  rw [tsum_eq_sum (s := ({0,1} : Finset ℕ))]
  · simp
  · intro n hn
    have hn2 : 2 ≤ n := by simp only [Finset.mem_insert, Finset.mem_singleton] at hn; omega
    rw [high_powers_zero t n hn2, smul_zero]

theorem exponential_action (t : ℝ) : NormedSpace.exp ℂ (A t) *ᵥ b = ![(t : ℂ), 1] := by
  rw [exponential_eq]
  ext i
  fin_cases i <;> simp [A, b, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem first_coordinate_zero (v : Fin 2 → ℂ) (hv : v ∈ krylovOne) : v 0 = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  simp [b]

/-- The one-step Arnoldi compression b*Ab vanishes. -/
theorem arnoldi_compression_zero (t : ℝ) :
    star (b 0) * (A t *ᵥ b) 0 + star (b 1) * (A t *ᵥ b) 1 = 0 := by
  simp [A, b, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- exp(0)=1, so the one-step Arnoldi output is exactly b. -/
theorem arnoldi_output : (NormedSpace.exp ℂ (0 : ℂ)) • b = b := by simp

theorem euclidean_coordinate_le (v : Fin 2 → ℂ) : ‖v 0‖ ≤ euclideanNorm v := by
  unfold euclideanNorm
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).2
  nlinarith [sq_nonneg ‖v 1‖]

theorem all_krylov_errors (t : ℝ) (v : Fin 2 → ℂ) (hv : v ∈ krylovOne) :
    |t| ≤ euclideanNorm (NormedSpace.exp ℂ (A t) *ᵥ b - v) := by
  have h := euclidean_coordinate_le (NormedSpace.exp ℂ (A t) *ᵥ b - v)
  simpa [exponential_action, first_coordinate_zero v hv, Complex.norm_real, Real.norm_eq_abs] using h

theorem arnoldi_error_exact (t : ℝ) :
    euclideanNorm (NormedSpace.exp ℂ (A t) *ᵥ b - b) = |t| := by
  rw [exponential_action]
  simp [euclideanNorm, b, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

/-- With spectrum, dimensions, time and starting-vector norm fixed, no finite bound exists. -/
theorem no_spectral_only_bound :
    ∀ C : ℝ, ∃ t : ℝ, spectrum ℂ (A t) = {0} ∧
      ∀ v ∈ krylovOne, C < euclideanNorm (NormedSpace.exp ℂ (A t) *ᵥ b - v) := by
  intro C
  refine ⟨|C|+1, spectrum_fixed _, ?_⟩
  intro v hv
  have hlower := all_krylov_errors (|C|+1) v hv
  have hc : C < |(|C|+1)| := by rw [abs_of_pos (by positivity)]; linarith [le_abs_self C]
  exact hc.trans_le hlower

#print axioms b_unit
#print axioms squared_zero
#print axioms spectrum_fixed
#print axioms exponential_eq
#print axioms exponential_action
#print axioms first_coordinate_zero
#print axioms arnoldi_compression_zero
#print axioms arnoldi_output
#print axioms all_krylov_errors
#print axioms arnoldi_error_exact
#print axioms no_spectral_only_bound
end KrylovNilpotent
