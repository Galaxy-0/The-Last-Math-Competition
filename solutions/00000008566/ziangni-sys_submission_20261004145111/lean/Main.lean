import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

noncomputable section
namespace UnitaryDilationCounterexample

def T : ℂ →L[ℂ] ℂ := 0
theorem contraction : ‖T‖ ≤ 1 := by simp [T]
theorem not_isometry : ¬ Isometry T := by
  intro h
  have hh := h.dist_eq (0 : ℂ) 1
  norm_num [T] at hh

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitaryMap (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  U.toContinuousLinearEquiv.toContinuousLinearMap

def DilationThroughTwo (j : ℂ →ₗᵢ[ℂ] H) (U : H ≃ₗᵢ[ℂ] H) : Prop :=
  ∀ n : ℕ, n ≤ 2 →
    j.toContinuousLinearMap.adjoint ∘L (unitaryMap U ^ n) ∘L j.toContinuousLinearMap = T ^ n

theorem first_moment (j : ℂ →ₗᵢ[ℂ] H) (U : H ≃ₗᵢ[ℂ] H)
    (h : DilationThroughTwo j U) : @inner ℂ H _ (j 1) (U (j 1)) = 0 := by
  have hv : j.toContinuousLinearMap.adjoint (U (j 1)) = 0 := by
    simpa [unitaryMap, T] using congrArg (fun A : ℂ →L[ℂ] ℂ => A 1) (h 1 (by norm_num))
  have hi := ContinuousLinearMap.adjoint_inner_right j.toContinuousLinearMap 1 (U (j 1))
  rw [hv, inner_zero_right] at hi
  exact hi.symm

theorem second_moment (j : ℂ →ₗᵢ[ℂ] H) (U : H ≃ₗᵢ[ℂ] H)
    (h : DilationThroughTwo j U) : @inner ℂ H _ (j 1) (U (U (j 1))) = 0 := by
  have hv : j.toContinuousLinearMap.adjoint (U (U (j 1))) = 0 := by
    simpa [unitaryMap, T, pow_two, ContinuousLinearMap.mul_apply] using
      congrArg (fun A : ℂ →L[ℂ] ℂ => A 1) (h 2 (by norm_num))
  have hi := ContinuousLinearMap.adjoint_inner_right j.toContinuousLinearMap 1 (U (U (j 1)))
  rw [hv, inner_zero_right] at hi
  exact hi.symm

def orbitThree (j : ℂ →ₗᵢ[ℂ] H) (U : H ≃ₗᵢ[ℂ] H) : Fin 3 → H :=
  ![j 1, U (j 1), U (U (j 1))]

theorem orbit_orthonormal (j : ℂ →ₗᵢ[ℂ] H) (U : H ≃ₗᵢ[ℂ] H)
    (h : DilationThroughTwo j U) : Orthonormal ℂ (orbitThree j U) := by
  have h01 := first_moment j U h
  have h02 := second_moment j U h
  have h12 : @inner ℂ H _ (U (j 1)) (U (U (j 1))) = 0 := by
    rw [U.inner_map_map]; exact h01
  have h10 := (inner_eq_zero_symm).mpr h01
  have h20 := (inner_eq_zero_symm).mpr h02
  have h21 := (inner_eq_zero_symm).mpr h12
  constructor
  · intro i
    fin_cases i <;> simp [orbitThree]
  · intro i k hik
    fin_cases i <;> fin_cases k <;> simp_all [orbitThree]

theorem dimension_lower_bound [FiniteDimensional ℂ H]
    (j : ℂ →ₗᵢ[ℂ] H) (U : H ≃ₗᵢ[ℂ] H) (h : DilationThroughTwo j U) :
    3 ≤ Module.finrank ℂ H := by
  simpa using (orbit_orthonormal j U h).linearIndependent.fintype_card_le_finrank

theorem no_dimension_two_dilation [FiniteDimensional ℂ H]
    (hd : Module.finrank ℂ H ≤ 2) :
    ¬ ∃ j : ℂ →ₗᵢ[ℂ] H, ∃ U : H ≃ₗᵢ[ℂ] H, DilationThroughTwo j U := by
  rintro ⟨j, U, h⟩
  have := dimension_lower_bound j U h
  omega

#print axioms contraction
#print axioms not_isometry
#print axioms first_moment
#print axioms second_moment
#print axioms orbit_orthonormal
#print axioms dimension_lower_bound
#print axioms no_dimension_two_dilation
end UnitaryDilationCounterexample
