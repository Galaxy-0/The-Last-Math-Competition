import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! The standard linear complementarity problem on the actual nonnegative orthant.
The explicit nonzero positive semidefinite example has a full ray of solutions. -/

noncomputable section
open Matrix Set

namespace Conjecture3794

/-- The standard nonnegative cone in the real coordinate space. -/
def nonnegativeOrthant (n : ℕ) : ConvexCone ℝ (Fin n → ℝ) :=
  ConvexCone.positive ℝ (Fin n → ℝ)

@[simp] theorem mem_nonnegativeOrthant {n : ℕ} (x : Fin n → ℝ) :
    x ∈ nonnegativeOrthant n ↔ ∀ i, 0 ≤ x i := by
  rfl

/-- Primal and residual feasibility in the nonnegative cone, together with orthogonality. -/
def LCPSolutions {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | x ∈ nonnegativeOrthant n ∧ M.mulVec x + q ∈ nonnegativeOrthant n ∧
    dotProduct x (M.mulVec x + q) = 0}

theorem mem_LCPSolutions_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (q x : Fin n → ℝ) :
    x ∈ LCPSolutions M q ↔
      (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ (M.mulVec x + q) i) ∧
        dotProduct x (M.mulVec x + q) = 0 := by
  rfl

/-- For nonnegative vectors, orthogonality is exactly coordinatewise complementarity. -/
theorem dotProduct_eq_zero_iff_coordinatewise {n : ℕ} (x y : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    dotProduct x y = 0 ↔ ∀ i, x i * y i = 0 := by
  simpa only [dotProduct, Finset.mem_univ, forall_const] using
    (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (f := fun i => x i * y i)
      (fun i _ => mul_nonneg (hx i) (hy i)))

/-- The cone formulation is equivalent to the standard scalar LCP conditions in every coordinate. -/
theorem mem_LCPSolutions_iff_coordinatewise {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (q x : Fin n → ℝ) :
    x ∈ LCPSolutions M q ↔
      ∀ i, 0 ≤ x i ∧ 0 ≤ (M.mulVec x + q) i ∧ x i * (M.mulVec x + q) i = 0 := by
  rw [mem_LCPSolutions_iff]
  constructor
  · rintro ⟨hx, hy, hdot⟩ i
    exact ⟨hx i, hy i, (dotProduct_eq_zero_iff_coordinatewise x _ hx hy).mp hdot i⟩
  · intro h
    have hx : ∀ i, 0 ≤ x i := fun i => (h i).1
    have hy : ∀ i, 0 ≤ (M.mulVec x + q) i := fun i => (h i).2.1
    exact ⟨hx, hy, (dotProduct_eq_zero_iff_coordinatewise x _ hx hy).mpr
      (fun i => (h i).2.2)⟩

def counterMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

def diagonalVector (t : ℝ) : Fin 2 → ℝ := ![t, t]

theorem counterMatrix_mulVec (x : Fin 2 → ℝ) :
    counterMatrix.mulVec x = ![x 0 - x 1, x 1 - x 0] := by
  ext i
  fin_cases i <;>
    simp [counterMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg, add_comm]

theorem counterMatrix_mul_diagonal (t : ℝ) :
    counterMatrix.mulVec (diagonalVector t) = 0 := by
  ext i
  fin_cases i <;> simp [counterMatrix_mulVec, diagonalVector]

theorem diagonalVector_mem (t : ℝ) (ht : 0 ≤ t) :
    diagonalVector t ∈ LCPSolutions counterMatrix 0 := by
  rw [mem_LCPSolutions_iff, counterMatrix_mul_diagonal]
  simp [diagonalVector, Fin.forall_fin_two, ht]

/-- These are all solutions, rather than only an infinite subfamily of solutions. -/
theorem counterSolutions_iff (x : Fin 2 → ℝ) :
    x ∈ LCPSolutions counterMatrix 0 ↔
      ∃ t : ℝ, 0 ≤ t ∧ x = diagonalVector t := by
  constructor
  · intro h
    obtain ⟨hx, hy, _⟩ := (mem_LCPSolutions_iff counterMatrix 0 x).mp h
    have h0 : 0 ≤ x 0 - x 1 := by simpa [counterMatrix_mulVec] using hy 0
    have h1 : 0 ≤ x 1 - x 0 := by simpa [counterMatrix_mulVec] using hy 1
    have heq : x 0 = x 1 := by linarith
    refine ⟨x 0, hx 0, ?_⟩
    ext i
    fin_cases i <;> simp [diagonalVector, heq]
  · rintro ⟨t, ht, rfl⟩
    exact diagonalVector_mem t ht

theorem diagonalVector_injective : Function.Injective diagonalVector := by
  intro s t h
  have h0 := congrFun h 0
  simpa [diagonalVector] using h0

theorem counterMatrix_ne_zero : counterMatrix ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [counterMatrix] at h00

/-- The example is singular; no claim is made about a nonsingular or P-matrix restriction. -/
theorem counterMatrix_det : counterMatrix.det = 0 := by
  norm_num [counterMatrix, Matrix.det_fin_two]

theorem counterMatrix_isHermitian : counterMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [counterMatrix]

theorem counterMatrix_quadratic (x : Fin 2 → ℝ) :
    dotProduct (star x) (counterMatrix.mulVec x) = (x 0 - x 1) ^ 2 := by
  simp [counterMatrix_mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The counterexample matrix is positive semidefinite in Mathlib's standard matrix sense. -/
theorem counterMatrix_posSemidef : counterMatrix.PosSemidef := by
  refine ⟨counterMatrix_isHermitian, ?_⟩
  intro x
  rw [counterMatrix_quadratic]
  exact sq_nonneg _

end Conjecture3794
