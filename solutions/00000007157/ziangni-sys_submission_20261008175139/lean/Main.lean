import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
open scoped Matrix ComplexConjugate
namespace NilpotentBoundary

abbrev M := Matrix (Fin 2) (Fin 2) ℂ
def J : M := !![0, 1; 0, 0]

theorem nonnormal : J * J.conjTranspose ≠ J.conjTranspose * J := by
  intro h
  have hh := congrArg (fun A : M => A 0 0) h
  norm_num [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] at hh

theorem spectrum_singleton : spectrum ℂ J = {0} := by
  ext z
  simp [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two,
    Matrix.algebraMap_eq_diagonal, J, isUnit_iff_ne_zero]

theorem boundary_singleton : frontier (spectrum ℂ J) = {0} := by
  rw [spectrum_singleton]
  simp [frontier]

/-- The squared Euclidean norm on complex two-space, in coordinates. -/
def UnitVector (v : Fin 2 → ℂ) : Prop := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 = 1

/-- The actual quadratic form v*Av; no eigenvalue surrogate is used. -/
def quadratic (A : M) (v : Fin 2 → ℂ) : ℂ :=
  star (v 0) * (A.mulVec v) 0 + star (v 1) * (A.mulVec v) 1

theorem quadratic_J (v : Fin 2 → ℂ) : quadratic J v = star (v 0) * v 1 := by
  simp [quadratic, J, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def numericalValues : Set ℝ := {r | ∃ v : Fin 2 → ℂ, UnitVector v ∧ ‖quadratic J v‖ = r}
def numericalRadius : ℝ := sSup numericalValues

theorem values_upper_bound : ∀ r ∈ numericalValues, r ≤ 1 / 2 := by
  rintro r ⟨v, hv, rfl⟩
  rw [quadratic_J, norm_mul, norm_star]
  dsimp [UnitVector] at hv
  nlinarith [sq_nonneg (‖v 0‖ - ‖v 1‖)]

/-- A rational unit vector suffices to show a strictly positive numerical radius. -/
def witness : Fin 2 → ℂ := ![(3 / 5 : ℝ), (4 / 5 : ℝ)]

theorem witness_unit : UnitVector witness := by
  norm_num [UnitVector, witness, Complex.norm_real, Real.norm_eq_abs]

theorem witness_value : ‖quadratic J witness‖ = 12 / 25 := by
  rw [quadratic_J, norm_mul, norm_star]
  norm_num [witness, Complex.norm_real, Real.norm_eq_abs]

theorem radius_positive : 0 < numericalRadius := by
  have hmem : (12 / 25 : ℝ) ∈ numericalValues := ⟨witness, witness_unit, witness_value⟩
  have hle : (12 / 25 : ℝ) ≤ numericalRadius := le_csSup ⟨1/2, values_upper_bound⟩ hmem
  linarith

theorem radius_bounds : (12 / 25 : ℝ) ≤ numericalRadius ∧ numericalRadius ≤ 1 / 2 := by
  have hmem : (12 / 25 : ℝ) ∈ numericalValues := ⟨witness, witness_unit, witness_value⟩
  exact ⟨le_csSup ⟨1/2, values_upper_bound⟩ hmem, csSup_le ⟨12/25, hmem⟩ values_upper_bound⟩

/-- A semicircle of radius r centered at c, with unit orientation u. -/
def semicircle (c u : ℂ) (r : ℝ) : Set ℂ :=
  {z | ∃ w : ℂ, ‖w‖ = r ∧ 0 ≤ w.im ∧ z = c + u * w}

theorem endpoints_mem (c u : ℂ) (r : ℝ) (hr : 0 < r) :
    c + u * (r : ℂ) ∈ semicircle c u r ∧
    c + u * (-r : ℂ) ∈ semicircle c u r := by
  constructor
  · exact ⟨r, by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr], by simp, rfl⟩
  · refine ⟨-r, ?_, by simp, rfl⟩
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using norm_neg (r : ℂ)

/-- No translated or rotated positive-radius semicircle equals the spectral frontier. -/
theorem boundary_not_semicircle (c u : ℂ) (hu : ‖u‖ = 1) :
    frontier (spectrum ℂ J) ≠ semicircle c u numericalRadius := by
  intro h
  obtain ⟨hp, hm⟩ := endpoints_mem c u numericalRadius radius_positive
  rw [← h, boundary_singleton, Set.mem_singleton_iff] at hp hm
  have heq : u * (numericalRadius : ℂ) = u * (-numericalRadius : ℂ) := add_left_cancel (hp.trans hm.symm)
  have hu0 : u ≠ 0 := by intro hz; simp [hz] at hu
  have hr : (numericalRadius : ℂ) = (-numericalRadius : ℂ) := mul_left_cancel₀ hu0 heq
  have hre := congrArg Complex.re hr
  simp only [Complex.ofReal_re, Complex.neg_re] at hre
  linarith [radius_positive]

#print axioms nonnormal
#print axioms spectrum_singleton
#print axioms boundary_singleton
#print axioms radius_bounds
#print axioms radius_positive
#print axioms boundary_not_semicircle
end NilpotentBoundary
