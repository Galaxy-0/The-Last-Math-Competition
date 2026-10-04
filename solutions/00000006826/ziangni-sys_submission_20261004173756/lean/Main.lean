import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section
namespace HyperinvariantSchur
abbrev E := Fin 2 → ℂ
def A : E →L[ℂ] E := ContinuousLinearMap.id ℂ E
def Hyperinvariant (M : Submodule ℂ E) : Prop :=
  ∀ S : E →L[ℂ] E, S.comp A = A.comp S → ∀ v ∈ M, S v ∈ M

theorem all_commute (S : E →L[ℂ] E) : S.comp A = A.comp S := by simp [A]

def rankOne (j : Fin 2) (v w : E) : E →L[ℂ] E :=
  (ContinuousLinearMap.proj j).smulRight ((v j)⁻¹ • w)

theorem rankOne_sends (j : Fin 2) (v w : E) (h : v j ≠ 0) :
    rankOne j v w v = w := by
  simp [rankOne, ContinuousLinearMap.smulRight_apply, smul_smul, h]

theorem hyperinvariant_classification (M : Submodule ℂ E) (hM : Hyperinvariant M) :
    M = ⊥ ∨ M = ⊤ := by
  classical
  by_cases h : M = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hv, hv0⟩ := M.ne_bot_iff.mp h
    have hj : ∃ j, v j ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hv0
      funext j
      exact hn j
    obtain ⟨j, hj⟩ := hj
    apply top_unique
    intro w _
    have hw := hM (rankOne j v w) (all_commute _) v hv
    rwa [rankOne_sends j v w hj] at hw

theorem actual_dimension : Module.finrank ℂ E = 2 := by
  simp [E, Module.finrank_fintype_fun_eq_card]

theorem no_intermediate (M : Submodule ℂ E) (hM : Hyperinvariant M) :
    Module.finrank ℂ M ≠ 1 := by
  rcases hyperinvariant_classification M hM with h | h
  · subst M
    simp
  · subst M
    simpa [actual_dimension] using (show Module.finrank ℂ E ≠ 1 by rw [actual_dimension]; decide)

def ordinaryLine : Submodule ℂ E := LinearMap.ker (LinearMap.proj (1 : Fin 2))
theorem ordinaryLine_invariant : ∀ v ∈ ordinaryLine, A v ∈ ordinaryLine := by
  simp [A]

theorem ordinaryLine_nontrivial : ordinaryLine ≠ ⊥ ∧ ordinaryLine ≠ ⊤ := by
  constructor
  · intro h
    have hv : (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0) ∈ ordinaryLine := by
      simp [ordinaryLine, LinearMap.mem_ker]
    rw [h] at hv
    have hz := congrFun ((show (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0) = 0 from by simpa using hv)) 0
    simp at hz
  · intro h
    have hv : (fun _ : Fin 2 => (1 : ℂ)) ∈ ordinaryLine := by rw [h]; trivial
    simpa [ordinaryLine, LinearMap.mem_ker] using hv

theorem ordinaryLine_not_hyperinvariant : ¬ Hyperinvariant ordinaryLine := by
  intro h
  rcases hyperinvariant_classification ordinaryLine h with h | h
  · exact ordinaryLine_nontrivial.1 h
  · exact ordinaryLine_nontrivial.2 h

def matrixA : Matrix (Fin 2) (Fin 2) ℂ := 1
theorem actual_matrix_action (v : E) : matrixA.mulVec v = A v := by simp [matrixA, A]
theorem actual_upper_triangular : ∀ i j : Fin 2, j < i → matrixA i j = 0 := by
  intro i j hij
  have h : i ≠ j := ne_of_gt hij
  simp [matrixA, Matrix.one_apply, h]

def HyperinvariantCompleteFlag : Prop :=
  ∃ M : Submodule ℂ E, Hyperinvariant M ∧ Module.finrank ℂ M = 1
theorem counterexample : (∀ i j : Fin 2, j < i → matrixA i j = 0) ∧
    ¬ HyperinvariantCompleteFlag := by
  constructor
  · exact actual_upper_triangular
  · rintro ⟨M, hM, hd⟩
    exact no_intermediate M hM hd

#print axioms all_commute
#print axioms rankOne_sends
#print axioms hyperinvariant_classification
#print axioms actual_dimension
#print axioms no_intermediate
#print axioms ordinaryLine_nontrivial
#print axioms ordinaryLine_not_hyperinvariant
#print axioms actual_matrix_action
#print axioms actual_upper_triangular
#print axioms counterexample
end HyperinvariantSchur
