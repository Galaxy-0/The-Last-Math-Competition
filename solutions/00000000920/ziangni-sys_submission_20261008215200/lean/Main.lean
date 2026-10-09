import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.Star
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

noncomputable section
namespace ProjectionDensityCounterexample
-- The actual homogeneous algebra of complex-valued functions on one point.
abbrev HomogeneousAlgebra := C(Unit, ℂ)
def pointEvaluation : HomogeneousAlgebra ≃ₐ[ℂ] ℂ where
  toFun f := f ()
  invFun z := ContinuousMap.const Unit z
  left_inv f := by ext u; cases u; rfl
  right_inv z := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
lemma every_point_function_constant (f : HomogeneousAlgebra) :
    f = ContinuousMap.const Unit (f ()) := by ext u; cases u; rfl
-- This is the constant identity inductive system's universal property.
theorem identity_system_limit {B : Type} [CommRing B] [Algebra ℂ B]
    (maps : ℕ → ℂ →ₐ[ℂ] B) (compatible : ∀ i j, i ≤ j → maps i = maps j) :
    ∃! f : ℂ →ₐ[ℂ] B, ∀ n, f = maps n := by
  refine ⟨maps 0, fun n => compatible 0 n (Nat.zero_le n), ?_⟩
  intro f hf
  exact hf 0

-- Real-rank zero in the source's self-adjoint invertible approximation form.
def RealRankZero : Prop := ∀ a : ℂ, star a = a → ∀ ε : ℝ, 0 < ε →
  ∃ b : ℂ, star b = b ∧ IsUnit b ∧ ‖b-a‖ < ε
theorem complex_real_rank_zero : RealRankZero := by
  intro a ha ε hε
  by_cases h : a = 0
  · subst a
    refine ⟨((ε/2 : ℝ) : ℂ), ?_, ?_, ?_⟩
    · simp
    · rw [isUnit_iff_ne_zero]
      exact_mod_cast (ne_of_gt (half_pos hε))
    · simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (half_pos hε)]
      linarith
  · exact ⟨a,ha,isUnit_iff_ne_zero.mpr h,by simp; exact hε⟩

def IsProjection (p : ℂ) : Prop := star p = p ∧ p*p = p
theorem projection_classification (p : ℂ) (hp : IsProjection p) : p=0 ∨ p=1 := by
  have h : p*(p-1)=0 := by linear_combination hp.2
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)
theorem projection_norm_gap (p : ℂ) (hp : IsProjection p) : ‖p-(1/2:ℂ)‖ = 1/2 := by
  rcases projection_classification p hp with rfl | rfl <;>
    norm_num [Complex.norm_def]
lemma half_self_adjoint : star (1/2:ℂ) = (1/2:ℂ) := by simp
-- A literal norm-density assertion for projections among self-adjoint elements.
def ProjectionDense : Prop := ∀ a : ℂ, star a=a → ∀ ε : ℝ, 0<ε →
  ∃ p : ℂ, IsProjection p ∧ ‖p-a‖ < ε
theorem projections_not_dense : ¬ ProjectionDense := by
  intro h
  obtain ⟨p,hp,hgap⟩ := h (1/2) half_self_adjoint (1/4) (by norm_num)
  rw [projection_norm_gap p hp] at hgap
  norm_num at hgap

theorem counterexample : RealRankZero ∧ ¬ ProjectionDense :=
  ⟨complex_real_rank_zero,projections_not_dense⟩

#print axioms every_point_function_constant
#print axioms identity_system_limit
#print axioms complex_real_rank_zero
#print axioms projection_classification
#print axioms projection_norm_gap
#print axioms projections_not_dense
#print axioms counterexample
end ProjectionDensityCounterexample
