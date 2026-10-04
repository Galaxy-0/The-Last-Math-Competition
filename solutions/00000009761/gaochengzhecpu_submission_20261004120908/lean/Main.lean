import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Conjecture9761
noncomputable section
open Matrix Polynomial

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def A : Mat := !![1, 3 / 2; 0, 1]

def gram : Mat := Aᴴ * A

theorem gram_eq : gram = !![1, 3 / 2; 3 / 2, 13 / 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat]

theorem charpoly_two (M : Mat) : M.charpoly =
    (X - C (M 0 0)) * (X - C (M 1 1)) - C (M 0 1) * C (M 1 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_two, Matrix.charmatrix_apply, Matrix.diagonal]

theorem charpoly_A : A.charpoly = (X - C 1) * (X - C 1) := by
  rw [charpoly_two]
  norm_num [A]

theorem charpoly_gram : gram.charpoly = (X - C 4) * (X - C (1 / 4 : ℂ)) := by
  rw [gram_eq, charpoly_two]
  apply Polynomial.funext
  intro z
  norm_num
  ring

/-- Normalization for an explicit singular value decomposition. -/
def c : ℂ := ((Real.sqrt 5)⁻¹ : ℝ)

@[simp] theorem star_c : (starRingEnd ℂ) c = c := by simp [c]

theorem c_squared : c ^ 2 = (1 / 5 : ℂ) := by
  have hs : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hr : ((Real.sqrt (5 : ℝ))⁻¹) ^ 2 = (1 / 5 : ℝ) := by
    rw [inv_pow, hs]
    norm_num
  have hc := congrArg Complex.ofReal hr
  simpa only [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, c] using hc

def U : Mat := !![2 * c, -c; c, 2 * c]
def V : Mat := !![c, -2 * c; 2 * c, c]
def S : Mat := !![2, 0; 0, 1 / 2]

theorem U_unitary : U ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change U * Uᴴ = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [U, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat] <;>
    ring_nf <;> norm_num [c_squared]

theorem V_unitary : V ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change V * Vᴴ = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [V, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat] <;>
    ring_nf <;> norm_num [c_squared]

theorem explicit_svd : A = U * S * Vᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, U, V, S, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, map_ofNat] <;>
    ring_nf <;> norm_num [c_squared]

/-- Eigenvalues with their algebraic multiplicities, not just a set of roots. -/
theorem eigenvalue_multiset : A.charpoly.roots = ({1, 1} : Multiset ℂ) := by
  rw [charpoly_A, Polynomial.roots_mul
    (mul_ne_zero (Polynomial.X_sub_C_ne_zero 1) (Polynomial.X_sub_C_ne_zero 1))]
  rw [Polynomial.roots_X_sub_C]
  simp

theorem gram_eigenvalue_multiset :
    gram.charpoly.roots = ({4, 1 / 4} : Multiset ℂ) := by
  rw [charpoly_gram, Polynomial.roots_mul
    (mul_ne_zero (Polynomial.X_sub_C_ne_zero 4) (Polynomial.X_sub_C_ne_zero (1 / 4)))]
  simp

def eigenvalues : Fin 2 → ℂ := ![1, 1]
def singularValues : Fin 2 → ℝ := ![2, 1 / 2]

/-- Complete, algebraic-multiplicity eigenvalue data in decreasing modulus order. -/
def OrderedEigenvalues (M : Mat) (eig : Fin 2 → ℂ) : Prop :=
  M.charpoly.roots = ({eig 0, eig 1} : Multiset ℂ) ∧ ‖eig 1‖ ≤ ‖eig 0‖

/-- The defining finite-dimensional singular-value decomposition certificate.
The two entries are nonnegative and in decreasing order, and are the diagonal
of a decomposition by actual complex unitary matrices. -/
def OrderedSingularValues (M : Mat) (s : Fin 2 → ℝ) : Prop :=
  0 ≤ s 1 ∧ s 1 ≤ s 0 ∧ ∃ (L R : Mat),
    L ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    R ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    M = L * Matrix.diagonal (fun i => (s i : ℂ)) * Rᴴ

theorem ordered_eigenvalues : OrderedEigenvalues A eigenvalues := by
  constructor
  · simpa [eigenvalues] using eigenvalue_multiset
  · norm_num [eigenvalues]

theorem ordered_singular_values : OrderedSingularValues A singularValues := by
  refine ⟨by norm_num [singularValues], by norm_num [singularValues],
    U, V, U_unitary, V_unitary, ?_⟩
  have hd : Matrix.diagonal (fun i => (singularValues i : ℂ)) = S := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [singularValues, S, Matrix.diagonal]
  rw [hd]
  exact explicit_svd

/-- The matrix acts on the usual complex Euclidean Hilbert space. -/
def operator : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

/-- The conjugate transpose used in `gram` is the Hilbert-space adjoint. -/
theorem matrix_adjoint_bridge :
    Matrix.toEuclideanLin Aᴴ = LinearMap.adjoint (Matrix.toEuclideanLin A) :=
  Matrix.toEuclideanLin_conjTranspose_eq_adjoint A

/-- The singular-value sequence padded by zero outside the dimension. -/
def singularSequence (k : ℕ) : ℝ :=
  (if k = 0 then singularValues 0 else 0) +
  (if k = 1 then singularValues 1 else 0)

/-- Finiteness of the trace norm, using the verified SVD values. -/
theorem singular_sequence_hasSum : HasSum singularSequence (5 / 2 : ℝ) := by
  have h := (hasSum_ite_eq (0 : ℕ) (singularValues 0)).add
    (hasSum_ite_eq 1 (singularValues 1))
  convert h using 1
  norm_num [singularSequence, singularValues]

theorem singular_sequence_summable : Summable singularSequence :=
  singular_sequence_hasSum.summable

theorem singular_sequence_nonnegative (k : ℕ) : 0 ≤ singularSequence k := by
  simp only [singularSequence, singularValues, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  split_ifs <;> norm_num

/-- The conjectured upper bound at n = 2; the positive second root is sqrt. -/
def proposedBound (s : Fin 2 → ℝ) : ℝ :=
  (Real.sqrt (s 0 * s 1) + s 1) / 2

theorem proposed_bound_value : proposedBound singularValues = 3 / 4 := by
  norm_num [proposedBound, singularValues]

theorem inequality_fails : ¬ ‖eigenvalues 1‖ ≤ proposedBound singularValues := by
  rw [proposed_bound_value]
  norm_num [eigenvalues]

/-- A universal assertion for operators would entail this two-dimensional case. -/
def ArithmeticStrengtheningInDimensionTwo : Prop :=
  ∀ (M : Mat) (eig : Fin 2 → ℂ) (s : Fin 2 → ℝ),
    OrderedEigenvalues M eig → OrderedSingularValues M s →
    ‖eig 1‖ ≤ proposedBound s

theorem conjecture_false_in_dimension_two : ¬ ArithmeticStrengtheningInDimensionTwo := by
  intro h
  exact inequality_fails (h A eigenvalues singularValues
    ordered_eigenvalues ordered_singular_values)

theorem full_counterexample :
    OrderedEigenvalues A eigenvalues ∧
    OrderedSingularValues A singularValues ∧
    HasSum singularSequence (5 / 2 : ℝ) ∧
    ¬ ‖eigenvalues 1‖ ≤ proposedBound singularValues :=
  ⟨ordered_eigenvalues, ordered_singular_values, singular_sequence_hasSum, inequality_fails⟩

#print axioms eigenvalue_multiset
#print axioms gram_eigenvalue_multiset
#print axioms ordered_eigenvalues
#print axioms ordered_singular_values
#print axioms matrix_adjoint_bridge
#print axioms singular_sequence_hasSum
#print axioms conjecture_false_in_dimension_two
#print axioms full_counterexample

end
end Conjecture9761
