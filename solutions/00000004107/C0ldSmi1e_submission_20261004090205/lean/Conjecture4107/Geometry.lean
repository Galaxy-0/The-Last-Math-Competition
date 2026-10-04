import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Concrete transverse subspaces of the three-dimensional real coordinate space. -/

noncomputable section

namespace Conjecture4107

abbrev V := Fin 3 → ℝ

/-- The coordinate plane with third coordinate zero. -/
def U : Submodule ℝ V where
  carrier := {x | x 2 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    change x 2 + y 2 = 0
    rw [hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change c * x 2 = 0
    rw [hx, mul_zero]

/-- The third coordinate axis. -/
def W : Submodule ℝ V where
  carrier := {x | x 0 = 0 ∧ x 1 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    intro x y hx hy
    change x 0 + y 0 = 0 ∧ x 1 + y 1 = 0
    simp [hx.1, hx.2, hy.1, hy.2]
  smul_mem' := by
    intro c x hx
    change c * x 0 = 0 ∧ c * x 1 = 0
    simp [hx.1, hx.2]

@[simp] theorem mem_U (x : V) : x ∈ U ↔ x 2 = 0 := Iff.rfl

@[simp] theorem mem_W (x : V) : x ∈ W ↔ x 0 = 0 ∧ x 1 = 0 := Iff.rfl

/-- The plane has exactly its first two coordinates as independent parameters. -/
def planeEquiv : U ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![x.val 0, x.val 1]
  invFun y := ⟨![y 0, y 1, 0], rfl⟩
  left_inv x := by
    apply Subtype.ext
    have hx : x.val 2 = 0 := x.property
    funext i
    fin_cases i <;> simp [hx]
  right_inv y := by
    funext i
    fin_cases i <;> rfl
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' c x := by
    funext i
    fin_cases i <;> rfl

/-- The axis is linearly isomorphic to the real line through its third coordinate. -/
def axisEquiv : W ≃ₗ[ℝ] ℝ where
  toFun x := x.val 2
  invFun t := ⟨![0, 0, t], ⟨rfl, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    have hx : x.val 0 = 0 ∧ x.val 1 = 0 := x.property
    funext i
    fin_cases i <;> simp [hx.1, hx.2]
  right_inv t := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

@[simp] theorem finrank_U : Module.finrank ℝ U = 2 := by
  simpa using planeEquiv.finrank_eq

@[simp] theorem finrank_W : Module.finrank ℝ W = 1 := by
  simpa using axisEquiv.finrank_eq

@[simp] theorem finrank_top : Module.finrank ℝ (⊤ : Submodule ℝ V) = 3 := by
  simp [V]

@[simp] theorem finrank_bot : Module.finrank ℝ (⊥ : Submodule ℝ V) = 0 := by
  simp

/-- The plane and axis intersect only at zero. -/
@[simp] theorem U_inf_W : U ⊓ W = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hu : x 2 = 0 := hx.1
  have hw : x 0 = 0 ∧ x 1 = 0 := hx.2
  change x = 0
  funext i
  fin_cases i <;> simp [hu, hw.1, hw.2]

@[simp] theorem W_inf_U : W ⊓ U = ⊥ := by rw [inf_comm, U_inf_W]

theorem U_not_le_W : ¬ U ≤ W := by
  intro h
  have hx : (![1, 0, 0] : V) ∈ U := by simp
  have hw := h hx
  norm_num at hw

theorem W_not_le_U : ¬ W ≤ U := by
  intro h
  have hx : (![0, 0, 1] : V) ∈ W := by simp
  have hu := h hx
  exact one_ne_zero hu

@[simp] theorem U_ne_bot : U ≠ ⊥ := by
  intro h
  apply U_not_le_W
  rw [h]
  exact bot_le

@[simp] theorem W_ne_bot : W ≠ ⊥ := by
  intro h
  apply W_not_le_U
  rw [h]
  exact bot_le

@[simp] theorem U_ne_top : U ≠ ⊤ := by
  intro h
  apply W_not_le_U
  rw [h]
  exact le_top

@[simp] theorem W_ne_top : W ≠ ⊤ := by
  intro h
  apply U_not_le_W
  rw [h]
  exact le_top

end Conjecture4107
