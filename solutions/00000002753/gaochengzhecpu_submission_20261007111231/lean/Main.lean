import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.NormNum

noncomputable section
open Matrix
namespace Conjecture2753

abbrev NCPoly := FreeAlgebra ℚ (Fin 3)
def ncX (i : Fin 3) : NCPoly := FreeAlgebra.ι ℚ i
def nestedCommutator : NCPoly :=
  (ncX 0 * ncX 1 - ncX 1 * ncX 0) * ncX 2 -
    ncX 2 * (ncX 0 * ncX 1 - ncX 1 * ncX 0)

def A : Matrix (Fin 2) (Fin 2) ℚ := !![0,1;0,0]
def B : Matrix (Fin 2) (Fin 2) ℚ := !![0,0;1,0]
def matrixInputs : Fin 3 → Matrix (Fin 2) (Fin 2) ℚ := ![A,B,A]

theorem matrix_evaluation :
    FreeAlgebra.lift ℚ matrixInputs nestedCommutator = !![0,2;0,0] := by
  simp only [nestedCommutator, map_sub, map_mul, ncX, FreeAlgebra.lift_ι_apply,
    show matrixInputs 0 = A from rfl, show matrixInputs 1 = B from rfl,
    show matrixInputs 2 = A from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixInputs, A, B, Matrix.mul_apply, Fin.sum_univ_two]

theorem nontrivial_polynomial : nestedCommutator ≠ 0 := by
  intro hz
  have he := matrix_evaluation
  rw [hz, map_zero] at he
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 1) he
  norm_num at h01

abbrev InfiniteAlgebra := Polynomial ℚ

theorem infinite_dimensional : ¬ Module.Finite ℚ InfiniteAlgebra := Polynomial.not_finite

theorem identity_on_infinite_algebra (v : Fin 3 → InfiniteAlgebra) :
    FreeAlgebra.lift ℚ v nestedCommutator = 0 := by
  simp only [nestedCommutator, map_sub, map_mul, ncX, FreeAlgebra.lift_ι_apply]
  rw [mul_comm (v 0) (v 1), sub_self]
  simp

theorem infinite_dimensional_counterexample :
    ¬ Module.Finite ℚ InfiniteAlgebra ∧ nestedCommutator ≠ 0 ∧
      ∀ v : Fin 3 → InfiniteAlgebra, FreeAlgebra.lift ℚ v nestedCommutator = 0 :=
  ⟨infinite_dimensional, nontrivial_polynomial, identity_on_infinite_algebra⟩

#print axioms matrix_evaluation
#print axioms nontrivial_polynomial
#print axioms infinite_dimensional
#print axioms identity_on_infinite_algebra
#print axioms infinite_dimensional_counterexample
end Conjecture2753
