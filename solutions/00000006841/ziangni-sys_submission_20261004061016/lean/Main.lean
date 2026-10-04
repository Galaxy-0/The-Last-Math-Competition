import Mathlib.Analysis.InnerProductSpace.Projection

noncomputable section
namespace SubspaceReflections
open scoped InnerProductSpace
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

def UnitaryIsometry (f : E → E) : Prop :=
  (∃ A : E →ₗ[𝕜] E, ∀ x, A x = f x) ∧ Function.Surjective f ∧
    Isometry f ∧ ∀ x y, ⟪f x, f y⟫_𝕜 = ⟪x, y⟫_𝕜

theorem equivalence_unitary (U : E ≃ₗᵢ[𝕜] E) : UnitaryIsometry (𝕜 := 𝕜) U := by
  exact ⟨⟨U.toLinearMap, fun _ => rfl⟩, U.surjective, U.isometry, U.inner_map_map⟩

theorem reflection_structure (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    (∀ x, K.reflection x = 2 • (K.orthogonalProjection x : E) - x) ∧
    Function.Involutive K.reflection ∧
    (∀ x, K.reflection x = x ↔ x ∈ K) ∧
    (∀ x ∈ Kᗮ, K.reflection x = -x) ∧
    UnitaryIsometry (𝕜 := 𝕜) K.reflection := by
  exact ⟨K.reflection_apply, K.reflection_involutive, K.reflection_eq_self_iff,
    fun _ hx => K.reflection_mem_subspace_orthogonalComplement_eq_neg hx,
    equivalence_unitary K.reflection⟩

def ProjectableSubspace := {K : Submodule 𝕜 E // K.HasOrthogonalProjection}

def reflectionOf (K : ProjectableSubspace (𝕜 := 𝕜) (E := E)) : E ≃ₗᵢ[𝕜] E := by
  letI : K.val.HasOrthogonalProjection := K.property
  exact K.val.reflection

def productReflection (ks : List (ProjectableSubspace (𝕜 := 𝕜) (E := E))) : E ≃ₗᵢ[𝕜] E :=
  ks.foldr (fun K U => (reflectionOf K).trans U)
    (LinearIsometryEquiv.refl 𝕜 E)

theorem productReflection_nil : productReflection ([] : List (ProjectableSubspace (𝕜 := 𝕜) (E := E))) =
    LinearIsometryEquiv.refl 𝕜 E := rfl

theorem productReflection_cons (K : ProjectableSubspace (𝕜 := 𝕜) (E := E))
    (ks : List (ProjectableSubspace (𝕜 := 𝕜) (E := E))) (x : E) :
    productReflection (K :: ks) x =
      productReflection ks (reflectionOf K x) := rfl

theorem finite_composition_unitary (ks : List (ProjectableSubspace (𝕜 := 𝕜) (E := E))) :
    UnitaryIsometry (𝕜 := 𝕜) (productReflection ks) :=
  equivalence_unitary _

def closedReflection [CompleteSpace E] (K : Submodule 𝕜 E)
    (h : IsClosed (K : Set E)) : E ≃ₗᵢ[𝕜] E := by
  letI : CompleteSpace K := h.completeSpace_coe
  exact K.reflection

theorem closed_reflection_unitary [CompleteSpace E] (K : Submodule 𝕜 E)
    (h : IsClosed (K : Set E)) :
    UnitaryIsometry (𝕜 := 𝕜) (closedReflection K h) := equivalence_unitary _

theorem two_closed_reflections_unitary [CompleteSpace E] (K L : Submodule 𝕜 E)
    (hK : IsClosed (K : Set E)) (hL : IsClosed (L : Set E)) :
    UnitaryIsometry (𝕜 := 𝕜) (fun x => closedReflection L hL (closedReflection K hK x)) :=
  equivalence_unitary ((closedReflection K hK).trans (closedReflection L hL))

end SubspaceReflections
#print axioms SubspaceReflections.reflection_structure
#print axioms SubspaceReflections.productReflection_cons
#print axioms SubspaceReflections.finite_composition_unitary
#print axioms SubspaceReflections.closed_reflection_unitary
#print axioms SubspaceReflections.two_closed_reflections_unitary
