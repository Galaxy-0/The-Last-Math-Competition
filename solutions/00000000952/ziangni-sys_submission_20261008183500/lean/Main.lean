import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

noncomputable section
open scoped InnerProductSpace
namespace TetrahedronErasure
abbrev H := EuclideanSpace ℝ (Fin 3)
def frame (i : Fin 4) : H := (WithLp.equiv 2 (Fin 3 → ℝ)).symm
  (![![(1:ℝ)/2,1/2,1/2], ![1/2,-1/2,-1/2],
     ![-1/2,1/2,-1/2], ![-1/2,-1/2,1/2]] i)
def projection (i : Fin 4) : H →L[ℝ] H :=
  (innerSL ℝ (frame i)).smulRight (frame i)
def full : H →L[ℝ] H := ∑ i : Fin 4, projection i
def erased : H →L[ℝ] H := projection 1 + projection 2 + projection 3
def defect : H →L[ℝ] H := full - erased

theorem dimension : Module.finrank ℝ H = 3 := finrank_euclideanSpace_fin
theorem frame_inner (i j : Fin 4) :
    ⟪frame i, frame j⟫_ℝ = if i=j then 3/4 else -1/4 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [frame, PiLp.inner_apply, Fin.sum_univ_succ]

theorem tight : full = ContinuousLinearMap.id ℝ H := by
  apply ContinuousLinearMap.ext
  intro x
  ext j
  fin_cases j <;>
    simp [full, projection, frame, innerSL_apply, PiLp.inner_apply,
      Fin.sum_univ_succ] <;> ring

theorem defect_projection : defect = projection 0 := by
  simp [defect, full, erased, Fin.sum_univ_succ]
  abel

theorem erased_eigenvector : defect (frame 0) = (3/4 : ℝ) • frame 0 := by
  rw [defect_projection]
  change ⟪frame 0, frame 0⟫_ℝ • frame 0 = (3/4 : ℝ) • frame 0
  rw [frame_inner]
  simp

theorem erased_vector_nonzero : frame 0 ≠ 0 := by
  intro h
  have he := congrArg (fun x : H => x 0) h
  norm_num [frame] at he

theorem deviation_lower : (3/4 : ℝ) ≤ ‖defect‖ := by
  have hp : 0 < ‖frame 0‖ := norm_pos_iff.mpr erased_vector_nonzero
  have h := defect.le_opNorm (frame 0)
  rw [erased_eigenvector, norm_smul] at h
  norm_num at h
  nlinarith

theorem erasure_bound_false : ¬ ‖defect‖ ≤ (1:ℝ)/3 := by
  have := deviation_lower
  linarith

#print axioms dimension
#print axioms frame_inner
#print axioms tight
#print axioms erased_eigenvector
#print axioms erasure_bound_false
end TetrahedronErasure
