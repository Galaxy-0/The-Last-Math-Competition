import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.NormNum

namespace SuperDimensionCounterexample

noncomputable section

-- A genuine direct decomposition of the underlying complex vector space.
structure SuperSpace (V : Type*) [AddCommGroup V] [Module ℂ V] where
  even : Submodule ℂ V
  odd : Submodule ℂ V
  disjoint : Disjoint even odd
  exhaustive : even ⊔ odd = ⊤

-- The Lie superalgebra is ℂ in even degree, zero in odd degree, bracket zero.
def bracket : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ := 0

theorem bracket_skew (a b : ℂ) : bracket a b = -bracket b a := by
  simp [bracket]

theorem bracket_jacobi (a b c : ℂ) :
    bracket a (bracket b c) + bracket b (bracket c a) +
      bracket c (bracket a b) = 0 := by
  simp [bracket]

-- Bilinearity is built into the two linear maps. Because all algebra
-- elements are even, the supermodule identity is the ordinary commutator law.
structure SuperRepresentation (V : Type*) [AddCommGroup V] [Module ℂ V] where
  space : SuperSpace V
  action : ℂ →ₗ[ℂ] V →ₗ[ℂ] V
  bracket_action : ∀ a b v, action (bracket a b) v =
    action a (action b v) - action b (action a v)
  preserves_even : ∀ a v, v ∈ space.even → action a v ∈ space.even
  preserves_odd : ∀ a v, v ∈ space.odd → action a v ∈ space.odd

def oddLineSpace : SuperSpace ℂ where
  even := ⊥
  odd := ⊤
  disjoint := disjoint_bot_left
  exhaustive := bot_sup_eq ⊤

def oddLine : SuperRepresentation ℂ where
  space := oddLineSpace
  action := 0
  bracket_action := by intros; simp [bracket]
  preserves_even := by intros; simp [oddLineSpace]
  preserves_odd := by intros; simp [oddLineSpace]

noncomputable def superDimension {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : SuperSpace V) : ℤ :=
  (Module.finrank ℂ S.even : ℤ) - (Module.finrank ℂ S.odd : ℤ)

theorem even_dimension : Module.finrank ℂ oddLineSpace.even = 0 := by
  simp [oddLineSpace, finrank_bot]

theorem odd_dimension : Module.finrank ℂ oddLineSpace.odd = 1 := by
  simp [oddLineSpace, finrank_top, Module.finrank_self]

theorem actual_super_dimension : superDimension oddLine.space = -1 := by
  simp only [superDimension, oddLine]
  rw [even_dimension, odd_dimension]
  norm_num

theorem conjecture_7400_false :
    ¬ (∀ R : SuperRepresentation ℂ, 0 ≤ superDimension R.space) := by
  intro h
  have hp := h oddLine
  rw [actual_super_dimension] at hp
  norm_num at hp

end
end SuperDimensionCounterexample

#print axioms SuperDimensionCounterexample.bracket_jacobi
#print axioms SuperDimensionCounterexample.even_dimension
#print axioms SuperDimensionCounterexample.odd_dimension
#print axioms SuperDimensionCounterexample.conjecture_7400_false
