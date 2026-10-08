import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

noncomputable section
open Filter
namespace EngelMatrix
abbrev Mat := Matrix (Fin 1) (Fin 1) ℚ

def commutator (X Y : Mat) : Mat := X * Y - Y * X

def iterated (X Y : Mat) : ℕ → Mat
  | 0 => Y
  | k + 1 => commutator X (iterated X Y k)

def IsEngel (S : Submodule ℚ Mat) (k : ℕ) : Prop :=
  ∀ X ∈ S, ∀ Y ∈ S, iterated X Y k = 0

lemma matrix_mul_comm (X Y : Mat) : X * Y = Y * X := by
  ext i j
  have hi : i = 0 := Fin.eq_zero i
  have hj : j = 0 := Fin.eq_zero j
  subst i
  subst j
  simp [Matrix.mul_apply, mul_comm]

lemma commutator_zero (X Y : Mat) : commutator X Y = 0 := by
  unfold commutator
  rw [matrix_mul_comm, sub_self]

lemma iterated_positive (X Y : Mat) (k : ℕ) (hk : 0 < k) : iterated X Y k = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact commutator_zero X (iterated X Y j)

lemma full_space_engel (k : ℕ) (hk : 0 < k) : IsEngel (⊤ : Submodule ℚ Mat) k := by
  intro X _ Y _
  exact iterated_positive X Y k hk

lemma ambient_dimension : Module.finrank ℚ Mat = 1 := by
  simp [Mat, Matrix, Module.finrank_pi_fintype, Module.finrank_pi]

lemma full_dimension : Module.finrank ℚ (⊤ : Submodule ℚ Mat) = 1 := by
  rw [finrank_top, ambient_dimension]

lemma every_space_dimension_le_one (S : Submodule ℚ Mat) : Module.finrank ℚ S ≤ 1 := by
  simpa only [ambient_dimension] using Submodule.finrank_le S

/-- Maximum dimension is certified by the full space, with an upper bound
for every genuine subspace, including every k-Engel subspace. -/
theorem actual_maximum_one (k : ℕ) (hk : 0 < k) :
    IsEngel (⊤ : Submodule ℚ Mat) k ∧
    Module.finrank ℚ (⊤ : Submodule ℚ Mat) = 1 ∧
    ∀ S : Submodule ℚ Mat, IsEngel S k → Module.finrank ℚ S ≤ 1 := by
  exact ⟨full_space_engel k hk, full_dimension, fun S _ => every_space_dimension_le_one S⟩

/-- The conjectured formula specialized to the actual n=1 full space. -/
def DimensionFormula (c : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    (Module.finrank ℚ (⊤ : Submodule ℚ Mat) : ℝ) = (1 : ℝ)^2 - 1 + c k

lemma correction_forced_one (c : ℕ → ℝ) (h : DimensionFormula c) (k : ℕ) (hk : 0 < k) :
    c k = 1 := by
  have hh := h k hk
  simpa [finrank_top, ambient_dimension] using hh.symm

theorem correction_cannot_tend_zero (c : ℕ → ℝ) (h : DimensionFormula c) :
    ¬ Tendsto c atTop (nhds 0) := by
  intro hz
  have he : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop] c := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact (correction_forced_one c h k (by omega)).symm
  have hone : Tendsto c atTop (nhds 1) := tendsto_const_nhds.congr' he
  have bad : (0 : ℝ) = 1 := tendsto_nhds_unique hz hone
  norm_num at bad

theorem conjectured_correction_false :
    ¬ ∃ c : ℕ → ℝ, DimensionFormula c ∧ Antitone c ∧ Tendsto c atTop (nhds 0) := by
  rintro ⟨c, hf, _, hz⟩
  exact correction_cannot_tend_zero c hf hz

end EngelMatrix
#print axioms EngelMatrix.iterated_positive
#print axioms EngelMatrix.full_space_engel
#print axioms EngelMatrix.full_dimension
#print axioms EngelMatrix.actual_maximum_one
#print axioms EngelMatrix.correction_forced_one
#print axioms EngelMatrix.correction_cannot_tend_zero
#print axioms EngelMatrix.conjectured_correction_false
