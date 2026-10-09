import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic

noncomputable section
namespace OrthogonalIndicator

abbrev G := Multiplicative (ZMod 2)
def rho : Representation ℂ G ℂ := Representation.trivial ℂ G ℂ
def character (g : G) : ℂ := LinearMap.trace ℂ ℂ (rho g)
def indicator : ℂ := (Fintype.card G : ℂ)⁻¹ * ∑ g : G, character (g*g)
def form : LinearMap.BilinForm ℂ ℂ := LinearMap.mul ℂ ℂ

theorem action (g : G) (z : ℂ) : rho g z = z := rfl
theorem form_value (x y : ℂ) : form x y = x*y := rfl
theorem form_symmetric (x y : ℂ) : form x y = form y x := mul_comm x y
theorem form_invariant (g : G) (x y : ℂ) :
    form (rho g x) (rho g y) = form x y := rfl
theorem form_nondegenerate (x : ℂ) (h : ∀ y, form x y = 0) : x = 0 := by
  simpa [form_value] using h 1
theorem form_not_alternating : form 1 1 ≠ 0 := by norm_num [form_value]

-- Stronger than irreducibility: every complex-linear subspace is 0 or C.
theorem irreducible (S : Submodule ℂ ℂ) : S = ⊥ ∨ S = ⊤ := by
  by_cases h : S = ⊥
  · exact Or.inl h
  · right
    obtain ⟨a, ha, hne⟩ := S.ne_bot_iff.mp h
    apply top_unique
    intro z hz
    have hm := S.smul_mem (z/a) ha
    simpa [smul_eq_mul, div_mul_cancel₀ z hne] using hm

theorem character_one (g : G) : character g = 1 := by
  simp [character, rho, Representation.trivial, LinearMap.trace_one]

theorem indicator_one : indicator = 1 := by
  simp [indicator, character_one, G, Fintype.card_multiplicative]

theorem orthogonal_sign_counterexample :
    (∀ x y : ℂ, form x y = form y x) ∧
    (∀ g x y, form (rho g x) (rho g y) = form x y) ∧
    (∀ x : ℂ, (∀ y, form x y = 0) → x = 0) ∧
    (∀ S : Submodule ℂ ℂ, S = ⊥ ∨ S = ⊤) ∧ indicator ≠ -1 := by
  refine ⟨form_symmetric, form_invariant, form_nondegenerate, irreducible, ?_⟩
  rw [indicator_one]
  norm_num

#print axioms character_one
#print axioms indicator_one
#print axioms irreducible
#print axioms orthogonal_sign_counterexample
end OrthogonalIndicator
