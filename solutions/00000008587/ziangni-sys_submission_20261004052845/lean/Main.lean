import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

namespace TriangularBasisCounterexample
noncomputable section
universe u
abbrev H := EuclideanSpace ℂ (Fin 3)
abbrev EndH := H →ₗ[ℂ] H

def scalar : ℂ →ₐ[ℂ] EndH := Algebra.ofId ℂ EndH

def scalarAlgebra : Subalgebra ℂ EndH := scalar.range

theorem scalar_injective : Function.Injective scalar :=
  RingHom.injective scalar.toRingHom

theorem scalar_unital : scalar 1 = 1 := scalar.map_one

theorem scalar_apply (a : ℂ) (x : H) : scalar a x = a • x := rfl

theorem scalar_continuous (a : ℂ) : Continuous (scalar a) :=
  (scalar a).continuous_of_finiteDimensional

theorem algebra_commutative (x y : EndH) (hx : x ∈ scalarAlgebra)
    (hy : y ∈ scalarAlgebra) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← scalar.map_mul, ← scalar.map_mul, mul_comm]

def standardBasis : Basis (Fin 3) ℂ H := (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis

-- Actual representation matrices in an arbitrary genuine vector-space basis.
theorem scalar_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℂ H) (a : ℂ) :
    LinearMap.toMatrix b b (scalar a) = a • (1 : Matrix ι ι ℂ) := by
  change LinearMap.toMatrix b b (algebraMap ℂ EndH a) = _
  rw [Module.algebraMap_end_eq_smul_id]
  simp

def Triangularizing {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : Basis ι ℂ H) : Prop :=
  ∀ L ∈ scalarAlgebra, ∀ i j, j < i → LinearMap.toMatrix b b L i j = 0

theorem every_basis_triangularizes {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : Basis ι ℂ H) : Triangularizing b := by
  intro L hL i j hji
  obtain ⟨a, rfl⟩ := hL
  change (LinearMap.toMatrix b b (scalar a)) i j = 0
  rw [scalar_matrix]
  simp [Matrix.one_apply, ne_of_gt hji]

theorem standard_triangularizes : Triangularizing standardBasis :=
  every_basis_triangularizes standardBasis

theorem ambient_dimension : Module.finrank ℂ H = 3 := by simp [H]

theorem every_basis_finite {ι : Type*} (b : Basis ι ℂ H) : Finite ι :=
  Module.Finite.finite_basis b

theorem every_basis_cardinality {ι : Type*} (b : Basis ι ℂ H) : Nat.card ι = 3 := by
  rw [← Module.finrank_eq_nat_card_basis b, ambient_dimension]

theorem no_small_basis {ι : Type*} (b : Basis ι ℂ H) : ¬ Nat.card ι ≤ 2 := by
  rw [every_basis_cardinality b]
  norm_num

theorem minimum_triangularizing_basis_size :
    Triangularizing standardBasis ∧ Nat.card (Fin 3) = 3 ∧
    (∀ (ι : Type u) (_b : Basis ι ℂ H), Nat.card ι = 3) := by
  exact ⟨standard_triangularizes, by simp, fun _ b => every_basis_cardinality b⟩

theorem dimension_bound_fails :
    Triangularizing standardBasis ∧
    (∀ (ι : Type u) (_b : Basis ι ℂ H), ¬ Nat.card ι ≤ 2) :=
  ⟨standard_triangularizes, fun _ b => no_small_basis b⟩

#print axioms scalar_injective
#print axioms algebra_commutative
#print axioms scalar_matrix
#print axioms every_basis_triangularizes
#print axioms every_basis_finite
#print axioms every_basis_cardinality
#print axioms dimension_bound_fails
end
end TriangularBasisCounterexample
