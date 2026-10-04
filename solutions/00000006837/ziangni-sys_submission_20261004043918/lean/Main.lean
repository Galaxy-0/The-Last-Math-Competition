import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
namespace AdjointInvariants
open scoped InnerProductSpace
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

def Invariant (A : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  ∀ x ∈ U, A x ∈ U

theorem orthogonal_invariant (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (h : Invariant A U) : Invariant (ContinuousLinearMap.adjoint A) Uᗮ := by
  intro y hy
  apply (U.mem_orthogonal _).2
  intro x hx
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (U.mem_orthogonal y).1 hy (A x) (h x hx)

theorem double_orthogonal_of_closed (U : Submodule 𝕜 E)
    (h : IsClosed (U : Set E)) : Uᗮᗮ = U := by
  rw [Submodule.orthogonal_orthogonal_eq_closure]
  exact h.submodule_topologicalClosure_eq

theorem closed_invariant_iff (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (h : IsClosed (U : Set E)) :
    Invariant A U ↔ Invariant (ContinuousLinearMap.adjoint A) Uᗮ := by
  constructor
  · exact orthogonal_invariant A U
  · intro hU
    have h' := orthogonal_invariant (ContinuousLinearMap.adjoint A) Uᗮ hU
    simpa [ContinuousLinearMap.adjoint_adjoint, double_orthogonal_of_closed U h] using h'

def ClosedInvariant (A : E →L[𝕜] E) :=
  { U : Submodule 𝕜 E // IsClosed (U : Set E) ∧ Invariant A U }

def complement (A : E →L[𝕜] E) :
    ClosedInvariant A → ClosedInvariant (ContinuousLinearMap.adjoint A) :=
  fun U => ⟨U.valᗮ, U.val.isClosed_orthogonal, orthogonal_invariant A U.val U.property.2⟩

def adjointCorrespondence (A : E →L[𝕜] E) :
    ClosedInvariant A ≃ ClosedInvariant (ContinuousLinearMap.adjoint A) where
  toFun := complement A
  invFun := fun U => ⟨U.valᗮ, U.val.isClosed_orthogonal, by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      orthogonal_invariant (ContinuousLinearMap.adjoint A) U.val U.property.2⟩
  left_inv := by
    intro U
    apply Subtype.ext
    exact double_orthogonal_of_closed U.val U.property.1
  right_inv := by
    intro U
    apply Subtype.ext
    exact double_orthogonal_of_closed U.val U.property.1

theorem correspondence_reverses_order (A : E →L[𝕜] E)
    (U V : ClosedInvariant A) :
    U.val ≤ V.val ↔ (adjointCorrespondence A V).val ≤ (adjointCorrespondence A U).val := by
  change U.val ≤ V.val ↔ V.valᗮ ≤ U.valᗮ
  constructor
  · exact Submodule.orthogonal_le
  · intro h
    have h' := Submodule.orthogonal_le h
    simpa [double_orthogonal_of_closed U.val U.property.1,
      double_orthogonal_of_closed V.val V.property.1] using h'

end AdjointInvariants
#print axioms AdjointInvariants.orthogonal_invariant
#print axioms AdjointInvariants.closed_invariant_iff
#print axioms AdjointInvariants.adjointCorrespondence
#print axioms AdjointInvariants.correspondence_reverses_order
