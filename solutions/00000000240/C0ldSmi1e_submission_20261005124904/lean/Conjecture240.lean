import Volume240

open Set MeasureTheory
namespace Mahler240
noncomputable section

/-- Ordinary Lebesgue volume product, expressed as a real number. -/
def mahlerVolume (S : Set E) : ℝ := volume.real S * volume.real (polar S)

lemma mahlerVolume_K : mahlerVolume K = 32 / 3 := by
  rw [mahlerVolume, measureReal_def, measureReal_def, polar_K, volume_K, volume_P]
  norm_num

lemma equality_K :
    mahlerVolume K = (4 : ℝ) ^ Module.finrank ℝ E /
      (Nat.factorial (Module.finrank ℝ E) : ℝ) := by
  rw [ambient_dimension, mahlerVolume_K]
  norm_num

/-- A concrete four-dimensional body contradicting the claimed equality classification. -/
theorem counterexample :
    Module.finrank ℝ E = 4 ∧
    IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
    (∀ x ∈ K, -x ∈ K) ∧
    volume.real K = 8 / 3 ∧ volume.real (polar K) = 4 ∧
    mahlerVolume K = (4 : ℝ) ^ Module.finrank ℝ E /
      (Nat.factorial (Module.finrank ℝ E) : ℝ) ∧
    (¬ ∃ f : E →ₗ[ℝ] E, f '' Cube = K) ∧
    (¬ ∃ f : E →ₗ[ℝ] E, f '' Cross = K) := by
  refine ⟨ambient_dimension, K_body.1, K_body.2.1, K_body.2.2.1,
    K_body.2.2.2, ?_, ?_, equality_K, not_linear_image_Cube, not_linear_image_Cross⟩
  · rw [measureReal_def, volume_K]
    norm_num
  · rw [measureReal_def, polar_K, volume_P]
    norm_num

/-- The necessary equality condition common to both source language versions is false. -/
theorem equality_classification_false :
    ¬ (∀ S : Set E, SymmetricConvexBody S →
      mahlerVolume S = (4 : ℝ) ^ Module.finrank ℝ E /
        (Nat.factorial (Module.finrank ℝ E) : ℝ) →
      (∃ f : E →ₗ[ℝ] E, f '' Cube = S) ∨
        (∃ f : E →ₗ[ℝ] E, f '' Cross = S)) := by
  intro h
  rcases h K K_body equality_K with hc | ho
  · exact not_linear_image_Cube hc
  · exact not_linear_image_Cross ho

/-- The dimension-four instance of the exact English assertion is false. -/
theorem conjecture_00000000240_english_false :
    ¬ (∀ S : Set E, SymmetricConvexBody S →
      ((4 : ℝ) ^ Module.finrank ℝ E /
        (Nat.factorial (Module.finrank ℝ E) : ℝ) ≤ mahlerVolume S ∧
      (mahlerVolume S = (4 : ℝ) ^ Module.finrank ℝ E /
        (Nat.factorial (Module.finrank ℝ E) : ℝ) →
        (∃ f : E →ₗ[ℝ] E, f '' Cube = S) ∨
          (∃ f : E →ₗ[ℝ] E, f '' Cross = S)))) := by
  intro h
  exact equality_classification_false (fun S hS => (h S hS).2)

/-- The dimension-four instance of the exact Chinese assertion is false. -/
theorem conjecture_00000000240_chinese_false :
    ¬ (∀ S : Set E, SymmetricConvexBody S →
      ((4 : ℝ) ^ Module.finrank ℝ E /
        (Nat.factorial (Module.finrank ℝ E) : ℝ) ≤ mahlerVolume S ∧
      (mahlerVolume S = (4 : ℝ) ^ Module.finrank ℝ E /
        (Nat.factorial (Module.finrank ℝ E) : ℝ) ↔
        (∃ f : E →ₗ[ℝ] E, f '' Cube = S) ∨
          (∃ f : E →ₗ[ℝ] E, f '' Cross = S)))) := by
  intro h
  exact equality_classification_false (fun S hS => (h S hS).2.mp)

end
end Mahler240
