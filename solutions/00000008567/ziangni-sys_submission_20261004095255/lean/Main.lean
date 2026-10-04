import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

noncomputable section
namespace PavingCounterexample
abbrev H (n : ℕ) := EuclideanSpace ℝ (Fin n)
variable {n : ℕ}
def basis : OrthonormalBasis (Fin n) ℝ (H n) := EuclideanSpace.basisFun (Fin n) ℝ
def fullOperator : H n →L[ℝ] (H n) := ContinuousLinearMap.id ℝ (H n)
lemma identity_matrix : LinearMap.toMatrix basis.toBasis basis.toBasis
    fullOperator.toLinearMap = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  change LinearMap.toMatrix basis.toBasis basis.toBasis (LinearMap.id) = 1
  exact LinearMap.toMatrix_id _
def coordinateSubspace (s : Finset (Fin n)) : Submodule ℝ (H n) :=
  Submodule.span ℝ (basis '' (s : Set (Fin n)))
def rowRestriction (s : Finset (Fin n)) : H n →L[ℝ] coordinateSubspace s :=
  (coordinateSubspace s).orthogonalProjection.comp fullOperator
def embeddedRestriction (s : Finset (Fin n)) : H n →L[ℝ] (H n) :=
  (coordinateSubspace s).subtypeL.comp (rowRestriction s)
def principalCompression (s : Finset (Fin n)) : H n →L[ℝ] (H n) :=
  (embeddedRestriction s).comp (fullOperator.comp (embeddedRestriction s))
lemma coordinate_mem (s : Finset (Fin n)) {i : Fin n} (hi : i ∈ s) :
    basis i ∈ coordinateSubspace s :=
  Submodule.subset_span ⟨i, hi, rfl⟩
lemma row_fixes (s : Finset (Fin n)) {i : Fin n} (hi : i ∈ s) :
    (rowRestriction s (basis i) : H n) = basis i := by
  exact Submodule.orthogonalProjection_eq_self_iff.mpr (coordinate_mem s hi)
lemma embedded_fixes (s : Finset (Fin n)) {i : Fin n} (hi : i ∈ s) :
    embeddedRestriction s (basis i) = basis i := row_fixes s hi
lemma principal_fixes (s : Finset (Fin n)) {i : Fin n} (hi : i ∈ s) :
    principalCompression s (basis i) = basis i := by
  simp only [principalCompression, ContinuousLinearMap.comp_apply, fullOperator,
    ContinuousLinearMap.id_apply, embedded_fixes s hi]
lemma full_norm [NeZero n] : ‖fullOperator (n := n)‖ = 1 := by
  exact ContinuousLinearMap.norm_id
lemma row_norm_lower (s : Finset (Fin n)) {i : Fin n} (hi : i ∈ s) :
    1 ≤ ‖rowRestriction s‖ := by
  have h := (rowRestriction s).le_opNorm (basis i)
  have hn : ‖rowRestriction s (basis i)‖ = 1 := by
    rw [← Submodule.norm_coe, row_fixes s hi]; exact basis.orthonormal.1 i
  rw [hn, basis.orthonormal.1 i, mul_one] at h
  exact h
lemma principal_norm_lower (s : Finset (Fin n)) {i : Fin n} (hi : i ∈ s) :
    1 ≤ ‖principalCompression s‖ := by
  have h := (principalCompression s).le_opNorm (basis i)
  rw [principal_fixes s hi, basis.orthonormal.1 i, mul_one] at h
  exact h
/-- Every coordinate is in a block; this is implied by every genuine row partition. -/
def Covers {ι : Type*} (blocks : ι → Finset (Fin n)) : Prop :=
  ∀ i, ∃ j, i ∈ blocks j
/-- Genuine finite partitions also require distinct blocks to be disjoint. -/
def IsPartition {ι : Type*} (blocks : ι → Finset (Fin n)) : Prop :=
  Covers blocks ∧ Pairwise (fun j k => Disjoint (blocks j) (blocks k))
variable [NeZero n]
theorem no_row_paving {ι : Type*} (blocks : ι → Finset (Fin n)) (h : Covers blocks) :
    ¬ ∀ j, ‖rowRestriction (blocks j)‖ ≤ (1 - (1/2 : ℝ))^2 * ‖fullOperator (n := n)‖ := by
  intro bound
  obtain ⟨j, hj⟩ := h 0
  have lower := row_norm_lower (blocks j) hj
  have upper := bound j
  rw [full_norm] at upper
  norm_num at upper
  linarith
theorem no_principal_paving {ι : Type*} (blocks : ι → Finset (Fin n)) (h : Covers blocks) :
    ¬ ∀ j, ‖principalCompression (blocks j)‖ ≤ (1 - (1/2 : ℝ))^2 * ‖fullOperator (n := n)‖ := by
  intro bound
  obtain ⟨j, hj⟩ := h 0
  have lower := principal_norm_lower (blocks j) hj
  have upper := bound j
  rw [full_norm] at upper
  norm_num at upper
  linarith
theorem no_finite_partition : ¬ ∃ r : ℕ, ∃ blocks : Fin r → Finset (Fin n),
    IsPartition blocks ∧ ∀ j, ‖rowRestriction (blocks j)‖ ≤
      (1 - (1/2 : ℝ))^2 * ‖fullOperator (n := n)‖ := by
  rintro ⟨r, blocks, hpart, hbound⟩
  exact no_row_paving blocks hpart.1 hbound
#print axioms identity_matrix
#print axioms row_fixes
#print axioms row_norm_lower
#print axioms principal_norm_lower
#print axioms no_row_paving
#print axioms no_principal_paving
#print axioms no_finite_partition
end PavingCounterexample
