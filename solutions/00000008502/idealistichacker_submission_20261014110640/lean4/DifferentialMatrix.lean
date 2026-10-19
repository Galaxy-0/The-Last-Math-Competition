import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Differential8502

variable {K : Type*} [Field K] [Differential K]

def fundamental (t : K) : Matrix (Fin 2) (Fin 2) K := !![1, t; 0, 1]
def coefficient : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]

omit [Differential K] in
theorem fundamental_det (t : K) : Matrix.det (fundamental t) = 1 := by
  simp [fundamental, Matrix.det_fin_two]

theorem fundamental_equation (t : K) (ht : Differential.deriv t = 1) :
    (fundamental t).map Differential.deriv = coefficient * fundamental t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fundamental, coefficient, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, ht]

theorem one_second_derivative : Differential.deriv (Differential.deriv (1 : K)) = 0 := by
  simp

theorem t_second_derivative (t : K) (ht : Differential.deriv t = 1) :
    Differential.deriv (Differential.deriv t) = 0 := by
  simp [ht]

omit [Differential K] in
theorem self_base_automorphism (g : K ≃ₐ[K] K) : g = AlgEquiv.refl := by
  ext x
  exact g.commutes x

def differentialSelfGroup : Subgroup (K ≃ₐ[K] K) where
  carrier := {g | forall x, g (Differential.deriv x) = Differential.deriv (g x)}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro g h hg hh x
    change g (h (Differential.deriv x)) = Differential.deriv (g (h x))
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    rw [self_base_automorphism g]
    intro x
    rfl

theorem differential_self_group_eq_bot :
    differentialSelfGroup (K := K) = ⊥ := by
  ext g
  simp only [Subgroup.mem_bot]
  constructor
  · intro _
    exact self_base_automorphism g
  · intro hg
    subst g
    exact (differentialSelfGroup (K := K)).one_mem

end Differential8502
