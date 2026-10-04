import Mathlib.Algebra.CubicDiscriminant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section

namespace Conjecture1259
open Polynomial

/-- Letters 0, 1, 2 mean a, b, c. These are the exact stated substitution images. -/
def substitution : Fin 3 → List (Fin 3) := ![[0, 1], [0, 2], [0]]

/-- Column j counts the occurrences of each letter in the image of letter j. -/
def incidenceCounts : Matrix (Fin 3) (Fin 3) ℕ :=
  fun i j => (substitution j).count i

/-- The actual real incidence matrix obtained from the substitution by counting. -/
def incidenceMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (incidenceCounts i j : ℝ)

theorem incidenceMatrix_eq :
    incidenceMatrix = !![1, 1, 1; 1, 0, 0; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [incidenceMatrix, incidenceCounts, substitution, List.count_cons, Fin.ext_iff]

/-- Its characteristic polynomial is computed from Matrix.det, not postulated. -/
theorem incidence_charpoly :
    incidenceMatrix.charpoly = X ^ 3 - X ^ 2 - X - 1 := by
  rw [incidenceMatrix_eq]
  norm_num [Matrix.charpoly, Matrix.det_fin_three, Matrix.charmatrix_apply, Matrix.cons_val_two, Matrix.diagonal, Fin.ext_iff]
  ring

/-- Reversing the row/column convention does not change the characteristic polynomial. -/
theorem transpose_charpoly : incidenceMatrix.transpose.charpoly = incidenceMatrix.charpoly := by
  unfold Matrix.charpoly
  have htrans : incidenceMatrix.transpose.charmatrix = incidenceMatrix.charmatrix.transpose := by
    ext i j
    simp [Matrix.charmatrix_apply, Matrix.transpose_apply, Matrix.diagonal, eq_comm]
  rw [htrans, Matrix.det_transpose]

/-- The corresponding genuine cubic object, for the discriminant identity. -/
def tribonacciCubic : Cubic ℝ := ⟨1, -1, -1, -1⟩

theorem charpoly_eq_cubic : incidenceMatrix.charpoly = tribonacciCubic.toPoly := by
  rw [incidence_charpoly]
  simp [tribonacciCubic, Cubic.toPoly]
  ring

theorem cubic_discriminant : tribonacciCubic.disc = -44 := by
  norm_num [tribonacciCubic, Cubic.disc]

/-- A real cubic with this discriminant cannot split, including repeated-root cases. -/
theorem cubic_not_splits : ¬tribonacciCubic.toPoly.Splits (RingHom.id ℝ) := by
  intro hsplit
  have ha : tribonacciCubic.a ≠ 0 := by norm_num [tribonacciCubic]
  obtain ⟨x, y, z, hroots⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplit
  have hdisc := Cubic.disc_eq_prod_three_roots ha hroots
  rw [cubic_discriminant] at hdisc
  simp only [RingHom.id_apply] at hdisc
  have hnonneg := sq_nonneg
    (tribonacciCubic.a * tribonacciCubic.a * (x - y) * (x - z) * (y - z))
  linarith

theorem incidence_charpoly_not_splits :
    ¬incidenceMatrix.charpoly.Splits (RingHom.id ℝ) := by
  rw [charpoly_eq_cubic]
  exact cubic_not_splits

/-- Three real eigenvalues counted with algebraic multiplicity, expressed by actual roots. -/
def threeRealEigenvalues : Prop := incidenceMatrix.charpoly.roots.card = 3

/-- For this 3x3 matrix, the root-count assertion is exactly splitting over the real field. -/
theorem threeRealEigenvalues_iff_splits :
    threeRealEigenvalues ↔ incidenceMatrix.charpoly.Splits (RingHom.id ℝ) := by
  unfold threeRealEigenvalues
  rw [Polynomial.splits_iff_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- The explicit three-real-eigenvalues clause is necessary for the stated conjecture and is false. -/
theorem conjecture1259_disproof : ¬threeRealEigenvalues := by
  intro h
  exact incidence_charpoly_not_splits (threeRealEigenvalues_iff_splits.mp h)

theorem transpose_charpoly_not_splits :
    ¬incidenceMatrix.transpose.charpoly.Splits (RingHom.id ℝ) := by
  rw [transpose_charpoly]
  exact incidence_charpoly_not_splits

end Conjecture1259
