import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum

namespace Conjecture3380

open Matrix

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev A := Mat × Mat

/-- The actual component exchange as a complex algebra automorphism. -/
def exchange : A ≃ₐ[ℂ] A :=
  { RingEquiv.prodComm with commutes' := fun _ => rfl }

@[simp] theorem exchange_apply (a : A) : exchange a = (a.2, a.1) := rfl

/-- The standard componentwise matrix adjoint. -/
def adjoint (a : A) : A := (a.1ᴴ, a.2ᴴ)

theorem exchange_preserves_adjoint (a : A) :
    exchange (adjoint a) = adjoint (exchange a) := rfl

def centralIdempotent : A := (1, 0)

theorem idempotent : centralIdempotent * centralIdempotent = centralIdempotent := by
  simp [centralIdempotent]

theorem central (a : A) : centralIdempotent * a = a * centralIdempotent := by
  apply Prod.ext <;> simp [centralIdempotent]

theorem exchange_moves_center : exchange centralIdempotent ≠ centralIdempotent := by
  intro h
  have h00 := congrArg (fun a : A => a.1 0 0) h
  norm_num [centralIdempotent] at h00

/-- Innerness is conjugation by an actual unit of the algebra. -/
def IsInner {B : Type*} [Ring B] [Algebra ℂ B] (φ : B ≃ₐ[ℂ] B) : Prop :=
  ∃ u : Bˣ, ∀ a : B, φ a = (u : B) * a * (↑(u⁻¹) : B)

theorem conjugation_fixes_center (u : Aˣ) :
    (u : A) * centralIdempotent * (↑(u⁻¹) : A) = centralIdempotent := by
  calc
    (u : A) * centralIdempotent * (↑(u⁻¹) : A) =
        centralIdempotent * ((u : A) * (↑(u⁻¹) : A)) := by
      rw [← central (u : A), mul_assoc]
    _ = centralIdempotent := by simp

theorem exchange_not_inner : ¬ IsInner exchange := by
  rintro ⟨u, hu⟩
  exact exchange_moves_center ((hu centralIdempotent).trans (conjugation_fixes_center u))

def firstMatrix : Mat := !![0, 1; 0, 0]
def secondMatrix : Mat := !![0, 0; 1, 0]

theorem matrix_products_differ : firstMatrix * secondMatrix ≠ secondMatrix * firstMatrix := by
  intro h
  have h00 := congrArg (fun M : Mat => M 0 0) h
  norm_num [firstMatrix, secondMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem algebra_noncommutative : ∃ a b : A, a * b ≠ b * a := by
  refine ⟨(firstMatrix, 0), (secondMatrix, 0), ?_⟩
  intro h
  exact matrix_products_differ (congrArg Prod.fst h)

/-- The explicit necessary universal clause of the source. -/
def AllNoncommutativeAutomorphismsInner : Prop :=
  ∀ (B : Type) [Ring B] [Algebra ℂ B],
    (∃ a b : B, a * b ≠ b * a) → ∀ φ : B ≃ₐ[ℂ] B, IsInner φ

theorem conjecture_false : ¬ AllNoncommutativeAutomorphismsInner := by
  intro h
  exact exchange_not_inner (h A algebra_noncommutative exchange)

theorem full_counterexample :
    (∃ a b : A, a * b ≠ b * a) ∧ ¬ IsInner exchange ∧
      (∀ a : A, exchange (adjoint a) = adjoint (exchange a)) :=
  ⟨algebra_noncommutative, exchange_not_inner, exchange_preserves_adjoint⟩

#print axioms idempotent
#print axioms central
#print axioms exchange_preserves_adjoint
#print axioms exchange_moves_center
#print axioms conjugation_fixes_center
#print axioms algebra_noncommutative
#print axioms exchange_not_inner
#print axioms conjecture_false
#print axioms full_counterexample

end Conjecture3380
