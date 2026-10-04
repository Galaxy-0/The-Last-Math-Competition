import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum

/-! Counterexample to the fixed-space dimension clause of TLMC 00000008230. -/

namespace Adams8230

abbrev G := Multiplicative (ZMod 3)
instance : Fintype G := inferInstanceAs (Fintype (ZMod 3))
def a : G := Multiplicative.ofAdd 1

theorem group_cases (g : G) : g = 1 ∨ g = a ∨ g = a ^ 2 := by
  have h : ∀ g : G, g = 1 ∨ g = a ∨ g = a ^ 2 := by decide
  exact h g

theorem cube_one (g : G) : g ^ 3 = 1 := by
  have h : ∀ g : G, g ^ 3 = 1 := by decide
  exact h g

theorem square_eq_one_iff (g : G) : g ^ 2 = 1 ↔ g = 1 := by
  have h : ∀ g : G, g ^ 2 = 1 ↔ g = 1 := by decide
  exact h g

theorem a_ne_one : a ≠ 1 := by decide

/-- Standard k-regularity, specialized to k = 2: element order coprime to 2. -/
def RegularElement (g : G) : Prop := Nat.Coprime (orderOf g) 2

theorem all_regular (g : G) : RegularElement g := by
  exact Nat.Coprime.of_dvd_left (orderOf_dvd_of_pow_eq_one (cube_one g)) (by decide)

/-- Regularity of a genuine conjugacy class: it contains a regular element. -/
def RegularClass (c : ConjClasses G) : Prop :=
  ∃ g : G, ConjClasses.mk g = c ∧ RegularElement g

theorem all_classes_regular (c : ConjClasses G) : RegularClass c := by
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  exact ⟨g, rfl, all_regular g⟩

noncomputable instance : Fintype {c : ConjClasses G // RegularClass c} :=
  Fintype.ofFinite _

noncomputable def regularClassesEquiv :
    {c : ConjClasses G // RegularClass c} ≃ ConjClasses G where
  toFun := Subtype.val
  invFun c := ⟨c, all_classes_regular c⟩
  left_inv c := by cases c; rfl
  right_inv c := rfl

theorem regular_class_count : Fintype.card {c : ConjClasses G // RegularClass c} = 3 := by
  rw [Fintype.card_congr regularClassesEquiv,
    ← Fintype.card_congr (ConjClasses.mkEquiv : G ≃ ConjClasses G)]
  decide

/-- A class function is invariant under genuine group conjugation. -/
def IsClassFunction (f : G → ℂ) : Prop :=
  ∀ x g : G, f (x * g * x⁻¹) = f g

theorem every_function_is_class (f : G → ℂ) : IsClassFunction f := by
  intro x g
  congr 1
  rw [mul_comm x g, mul_inv_cancel_right]

/-- The Adams operation on complex class functions, evaluated on the group. -/
def adams (k : ℕ) (f : G → ℂ) (g : G) : ℂ := f (g ^ k)

/-- The actual fixed subspace of the second Adams operation on class functions. -/
def fixedClassFunctions : Submodule ℂ (G → ℂ) where
  carrier := {f | IsClassFunction f ∧ adams 2 f = f}
  zero_mem' := ⟨every_function_is_class _, rfl⟩
  add_mem' := by
    intro f h hf hh
    refine ⟨every_function_is_class _, ?_⟩
    funext g
    change f (g ^ 2) + h (g ^ 2) = f g + h g
    exact congrArg₂ (· + ·) (congrFun hf.2 g) (congrFun hh.2 g)
  smul_mem' := by
    intro c f hf
    refine ⟨every_function_is_class _, ?_⟩
    funext g
    change c * f (g ^ 2) = c * f g
    exact congrArg (c * ·) (congrFun hf.2 g)

noncomputable def expand (p : ℂ × ℂ) : fixedClassFunctions :=
  ⟨fun g => if g = 1 then p.1 else p.2,
    every_function_is_class _, by
      funext g
      simp only [adams, square_eq_one_iff]⟩

/-- Explicit coordinates; the inverse sends (u,v) to values (u,v,v). -/
noncomputable def coordinates : fixedClassFunctions ≃ₗ[ℂ] (ℂ × ℂ) where
  toFun f := ((f : G → ℂ) 1, (f : G → ℂ) a)
  invFun := expand
  left_inv f := by
    apply Subtype.ext
    funext g
    rcases group_cases g with rfl | rfl | rfl
    · simp [expand]
    · simp [expand, a_ne_one]
    · have h : (a ^ 2 : G) ≠ 1 := by decide
      have hf : (f : G → ℂ) (a ^ 2) = (f : G → ℂ) a := congrFun f.property.2 a
      simpa [expand, h] using hf.symm
  right_inv p := by
    ext <;> simp [expand, a_ne_one]
  map_add' f h := rfl
  map_smul' c f := rfl

theorem fixed_dimension : Module.finrank ℂ fixedClassFunctions = 2 := by
  rw [coordinates.finrank_eq, Module.finrank_prod]
  simp

/-- The claimed equality fails for the actual finite cyclic group C3 at k = 2. -/
theorem counterexample :
    Module.finrank ℂ fixedClassFunctions ≠
      Fintype.card {c : ConjClasses G // RegularClass c} := by
  rw [fixed_dimension, regular_class_count]
  decide

end Adams8230

#print axioms Adams8230.counterexample
