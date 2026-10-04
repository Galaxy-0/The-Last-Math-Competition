import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.NormNum

open Filter
open scoped Topology

namespace AsymptoticIteration8841

/-- Standard asymptotic nonexpansiveness, with indices starting at zero. -/
def AsymptoticallyNonexpansive (T : ℝ → ℝ) : Prop :=
  ∃ k : ℕ → ℝ, (∀ n, 1 ≤ k n) ∧ Tendsto k atTop (𝓝 1) ∧
    ∀ n x y, dist (T^[n] x) (T^[n] y) ≤ k n * dist x y

/-- Weak convergence means convergence under every continuous linear functional. -/
def WeaklyConverges (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ f : ℝ →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f a))

def reflection (x : ℝ) : ℝ := -x
def orbit (n : ℕ) : ℝ := reflection^[n] 1

theorem iterate_isometry (n : ℕ) : Isometry (reflection^[n]) := by
  induction n with
  | zero => simpa using (isometry_id : Isometry (id : ℝ → ℝ))
  | succ n ih =>
    rw [Function.iterate_succ']
    exact (isometry_neg : Isometry (fun x : ℝ => -x)).comp ih

theorem reflection_asymptotically_nonexpansive :
    AsymptoticallyNonexpansive reflection := by
  refine ⟨fun _ => 1, fun _ => le_rfl, tendsto_const_nhds, ?_⟩
  intro n x y
  simp only [one_mul, (iterate_isometry n).dist_eq]
  exact le_rfl

theorem reflection_fixed_zero : reflection 0 = 0 := neg_zero

theorem interval_geometry :
    IsClosed (Set.Icc (-1 : ℝ) 1) ∧
    Bornology.IsBounded (Set.Icc (-1 : ℝ) 1) ∧
    Convex ℝ (Set.Icc (-1 : ℝ) 1) ∧
    (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 ∧ (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
  exact ⟨isClosed_Icc, Metric.isBounded_Icc _ _, convex_Icc _ _, by norm_num, by norm_num⟩

theorem reflection_preserves_interval :
    Set.MapsTo reflection (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) := by
  intro x hx
  exact ⟨by simpa only [reflection] using neg_le_neg hx.2,
    by simpa only [reflection, neg_neg] using neg_le_neg hx.1⟩

theorem orbit_succ (n : ℕ) : orbit (n + 1) = -orbit n := by
  change reflection^[n + 1] 1 = reflection (reflection^[n] 1)
  rw [Function.iterate_succ_apply']

theorem orbit_even (n : ℕ) : orbit (2 * n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ]
    change orbit ((2 * n + 1) + 1) = 1
    rw [orbit_succ, orbit_succ, neg_neg, ih]

theorem orbit_odd (n : ℕ) : orbit (2 * n + 1) = -1 := by
  rw [orbit_succ, orbit_even]

theorem orbit_in_interval (n : ℕ) : orbit n ∈ Set.Icc (-1 : ℝ) 1 := by
  induction n with
  | zero => norm_num [orbit]
  | succ n ih =>
    rw [orbit_succ]
    exact reflection_preserves_interval ih

theorem even_cofinal : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
  apply tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (by decide : 0 < 2))
  exact tendsto_id

theorem odd_cofinal : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
  exact tendsto_atTop_mono (fun n => Nat.le_add_right (2 * n) 1) even_cofinal

theorem orbit_not_weakly_convergent (a : ℝ) : ¬ WeaklyConverges orbit a := by
  intro h
  have hi : Tendsto orbit atTop (𝓝 a) := by
    simpa using h (ContinuousLinearMap.id ℝ ℝ)
  have he : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 a) := by
    simpa only [Function.comp_def, orbit_even] using hi.comp even_cofinal
  have ho : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 a) := by
    simpa only [Function.comp_def, orbit_odd] using hi.comp odd_cofinal
  have h1 : (1 : ℝ) = a := tendsto_nhds_unique tendsto_const_nhds he
  have hm1 : (-1 : ℝ) = a := tendsto_nhds_unique tendsto_const_nhds ho
  have : (1 : ℝ) = -1 := h1.trans hm1.symm
  norm_num at this

/-- The actual Picard orbit refutes the universal weak-convergence assertion. -/
theorem conjecture_00000008841 :
    AsymptoticallyNonexpansive reflection ∧
    (∀ n, Isometry (reflection^[n])) ∧ reflection 0 = 0 ∧
    Set.MapsTo reflection (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) ∧
    (∀ n, orbit n ∈ Set.Icc (-1 : ℝ) 1) ∧
    ¬ ∃ a, WeaklyConverges orbit a := by
  exact ⟨reflection_asymptotically_nonexpansive, iterate_isometry,
    reflection_fixed_zero, reflection_preserves_interval, orbit_in_interval,
    fun ⟨a, ha⟩ => orbit_not_weakly_convergent a ha⟩

end AsymptoticIteration8841

#print axioms AsymptoticIteration8841.conjecture_00000008841
#print axioms AsymptoticIteration8841.interval_geometry
