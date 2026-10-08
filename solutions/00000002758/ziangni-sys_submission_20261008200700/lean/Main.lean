import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic

noncomputable section
namespace MultiplicativeBasis
abbrev G := Multiplicative (ZMod 2)
abbrev A := MonoidAlgebra ℚ G
def g : G := Multiplicative.ofAdd 1
def u : A := MonoidAlgebra.single g 1
def e : A := (1/2 : ℚ) • ((1 : A) + u)

lemma g_ne_one : g ≠ 1 := by decide
lemma g_square : g*g = 1 := by decide
lemma group_cases (x : G) : x = 1 ∨ x = g := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h x.toAdd with h | h
  · left; exact congrArg Multiplicative.ofAdd h
  · right; exact congrArg Multiplicative.ofAdd h

@[simp] lemma add_apply (f h : A) (x : G) : (f+h) x = f x + h x := rfl
@[simp] lemma smul_apply (a : ℚ) (f : A) (x : G) : (a • f) x = a * f x := rfl
@[simp] lemma u_one : u (1 : G) = 0 := by simp [u, g_ne_one]
@[simp] lemma u_g : u g = 1 := by simp [u]
@[simp] lemma one_one : (1 : A) (1 : G) = 1 := by simp [MonoidAlgebra.one_def]
@[simp] lemma one_g : (1 : A) g = 0 := by simp [MonoidAlgebra.one_def, MonoidAlgebra.single_apply, g_ne_one, Ne.symm g_ne_one]
@[simp] lemma e_one : e (1 : G) = 1/2 := by simp [e]
@[simp] lemma e_g : e g = 1/2 := by simp [e]

lemma u_square : u*u = 1 := by
  simp [u, MonoidAlgebra.single_mul_single, g_square, MonoidAlgebra.one_def]

lemma e_square : e*e = e := by
  simp only [e, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, u_square]
  module

lemma e_ne_one : e ≠ 1 := by
  intro h
  have := congrArg (fun f : A => f g) h
  norm_num at this

lemma algebra_ext {f h : A} (h1 : f 1 = h 1) (hg : f g = h g) : f = h := by
  ext x
  rcases group_cases x with rfl | rfl
  · exact h1
  · exact hg

/-- Coordinates in the standard group basis. -/
def standardCoordinates : A ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun f := ![f 1, f g]
  invFun c := c 0 • (1 : A) + c 1 • u
  left_inv f := by
    apply algebra_ext <;> simp
  right_inv c := by
    ext i
    fin_cases i <;> simp
  map_add' f h := by ext i; fin_cases i <;> simp
  map_smul' a f := by ext i; fin_cases i <;> simp

/-- Coordinates in the basis containing a nonidentity idempotent. -/
def alternativeCoordinates : A ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun f := ![f 1 - f g, 2 * f g]
  invFun c := c 0 • (1 : A) + c 1 • e
  left_inv f := by
    apply algebra_ext <;> simp <;> ring
  right_inv c := by
    ext i
    fin_cases i <;> simp <;> ring
  map_add' f h := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a f := by ext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

def standardBasis : Basis (Fin 2) ℚ A := Basis.ofEquivFun standardCoordinates
def alternativeBasis : Basis (Fin 2) ℚ A := Basis.ofEquivFun alternativeCoordinates

lemma standard_values : standardBasis 0 = 1 ∧ standardBasis 1 = u := by
  simp [standardBasis, Basis.coe_ofEquivFun, standardCoordinates]
lemma alternative_values : alternativeBasis 0 = 1 ∧ alternativeBasis 1 = e := by
  simp [alternativeBasis, Basis.coe_ofEquivFun, alternativeCoordinates]

lemma standard_closed (i j : Fin 2) : ∃ k, standardBasis i * standardBasis j = standardBasis k := by
  have h := standard_values
  fin_cases i <;> fin_cases j
  · exact ⟨0, by simp [h.1]⟩
  · exact ⟨1, by simp [h.1, h.2]⟩
  · exact ⟨1, by simp [h.1, h.2]⟩
  · exact ⟨0, by simp [h.1, h.2, u_square]⟩

lemma alternative_closed (i j : Fin 2) : ∃ k, alternativeBasis i * alternativeBasis j = alternativeBasis k := by
  have h := alternative_values
  fin_cases i <;> fin_cases j
  · exact ⟨0, by simp [h.1]⟩
  · exact ⟨1, by simp [h.1, h.2]⟩
  · exact ⟨1, by simp [h.1, h.2]⟩
  · exact ⟨1, by simp [h.2, e_square]⟩

lemma standard_all_square_one (i : Fin 2) : standardBasis i * standardBasis i = 1 := by
  fin_cases i <;> simp [standard_values.1, standard_values.2, u_square]

theorem no_basis_algebra_isomorphism : ¬ ∃ φ : A ≃ₐ[ℚ] A,
    Set.range (fun i => φ (standardBasis i)) = Set.range alternativeBasis := by
  rintro ⟨φ, hr⟩
  have he : e ∈ Set.range alternativeBasis := ⟨1, alternative_values.2⟩
  rw [← hr] at he
  obtain ⟨i, hi⟩ := he
  change φ (standardBasis i) = e at hi
  have hs := congrArg φ (standard_all_square_one i)
  rw [map_mul, hi, map_one, e_square] at hs
  exact e_ne_one hs

lemma subgroup_cases (H : Subgroup G) : H = ⊥ ∨ H = ⊤ := by
  by_cases h : g ∈ H
  · right
    apply top_unique
    intro x _
    rcases group_cases x with rfl | rfl
    · exact H.one_mem
    · exact h
  · left
    apply bot_unique
    intro x hx
    rcases group_cases x with rfl | rfl
    · simp
    · exact False.elim (h hx)

theorem no_distinct_isomorphic_subgroups (H K : Subgroup G) (h : Nonempty (H ≃* K)) : H = K := by
  obtain ⟨f⟩ := h
  have hc := Nat.card_congr f.toEquiv
  rcases subgroup_cases H with rfl | rfl <;>
    rcases subgroup_cases K with rfl | rfl
  · rfl
  · exfalso; norm_num [Subgroup.card_bot, Subgroup.card_top, G, Nat.card_eq_fintype_card] at hc
  · exfalso; norm_num [Subgroup.card_bot, Subgroup.card_top, G, Nat.card_eq_fintype_card] at hc
  · rfl

end MultiplicativeBasis
#print axioms MultiplicativeBasis.standardBasis
#print axioms MultiplicativeBasis.alternativeBasis
#print axioms MultiplicativeBasis.standard_closed
#print axioms MultiplicativeBasis.alternative_closed
#print axioms MultiplicativeBasis.no_basis_algebra_isomorphism
#print axioms MultiplicativeBasis.no_distinct_isomorphic_subgroups
