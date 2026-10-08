import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

noncomputable section
namespace MonotonePerturbation

/-- Actual bounded linear scalar multiplication on the real Hilbert space. -/
def scale (a : ℝ) : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ

@[simp] theorem scale_apply (a x : ℝ) : scale a x = a * x := rfl

theorem scale_norm (a : ℝ) : ‖scale a‖ = |a| := by
  apply ContinuousLinearMap.homothety_norm
  intro x
  simp [Real.norm_eq_abs, abs_mul]

/-- Monotonicity of a relation, using the real Hilbert inner product. -/
def MonotoneRelation (R : ℝ → ℝ → Prop) : Prop :=
  ∀ x u y v, R x u → R y v → 0 ≤ (x - y) * (u - v)

def graph (F : ℝ →L[ℝ] ℝ) (x u : ℝ) : Prop := u = F x

/-- Maximality among ALL monotone relations, not just linear operators. -/
def MaximalMonotone (F : ℝ →L[ℝ] ℝ) : Prop :=
  MonotoneRelation (graph F) ∧
  ∀ R : ℝ → ℝ → Prop, MonotoneRelation R →
    (∀ x u, graph F x u → R x u) → ∀ x u, R x u → graph F x u

def StronglyMonotone (γ : ℝ) (F : ℝ →L[ℝ] ℝ) : Prop :=
  ∀ x y : ℝ, γ * ‖x - y‖ ^ 2 ≤ (x - y) * (F x - F y)

theorem strong_scale (a : ℝ) : StronglyMonotone a (scale a) := by
  intro x y
  simp only [Real.norm_eq_abs, sq_abs, scale_apply]
  nlinarith

theorem optimal_strong_constant (a γ : ℝ) (h : StronglyMonotone γ (scale a)) : γ ≤ a := by
  have hh := h 1 0
  simpa using hh

theorem positive_scale_maximal (a : ℝ) (ha : 0 < a) : MaximalMonotone (scale a) := by
  constructor
  · intro x u y v hu hv
    dsimp [graph] at hu hv
    rw [hu, hv]
    nlinarith [sq_nonneg (x - y)]
  · intro R hR hcontains x u hxu
    let y : ℝ := (u + a * x) / (2 * a)
    have hy : R y (a * y) := hcontains y (a * y) rfl
    have h := hR x u y (a * y) hxu hy
    have hid : (x - y) * (u - a * y) = -(u - a * x)^2 / (4 * a) := by
      dsimp [y]
      field_simp
      <;> ring
    rw [hid] at h
    have hn : 0 ≤ -(u - a * x)^2 := by
      rcases div_nonneg_iff.mp h with hp | hn
      · exact hp.1
      · nlinarith [hn.2]
    have hs : (u - a * x)^2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)

theorem positive_perturbation (a : ℝ) : scale a + scale (2 * a) = scale (3 * a) := by
  ext x
  simp
  ring

theorem negative_perturbation (a : ℝ) : scale a + scale (-2 * a) = scale (-a) := by
  ext x
  simp
  ring

theorem negative_scale_not_monotone (a : ℝ) (ha : 0 < a) :
    ¬ MonotoneRelation (graph (scale (-a))) := by
  intro h
  have hh := h 1 (-a) 0 0 (by simp [graph]) (by simp [graph])
  simp only [sub_zero, one_mul] at hh
  linarith

/-- Equal perturbation norms produce opposite answers to maximal monotonicity. -/
theorem same_norm_opposite_behavior (a : ℝ) (ha : 0 < a) :
    StronglyMonotone a (scale a) ∧
    (∀ γ, StronglyMonotone γ (scale a) → γ ≤ a) ∧
    ‖scale (2 * a)‖ = 2 * a ∧ ‖scale (-2 * a)‖ = 2 * a ∧
    a < 2 * a ∧ MaximalMonotone (scale a + scale (2 * a)) ∧
    ¬ MonotoneRelation (graph (scale a + scale (-2 * a))) := by
  refine ⟨strong_scale a, optimal_strong_constant a, ?_, ?_, by linarith, ?_, ?_⟩
  · rw [scale_norm, abs_of_pos (by positivity)]
  · rw [scale_norm, abs_of_neg (by nlinarith)]
    ring
  · rw [positive_perturbation]
    exact positive_scale_maximal _ (by positivity)
  · rw [negative_perturbation]
    exact negative_scale_not_monotone a ha

/-- Counterexamples exist within every positive absolute perturbation tolerance. -/
theorem arbitrarily_small_counterexample (ε : ℝ) (hε : 0 < ε) :
    ∃ (A B : ℝ →L[ℝ] ℝ) (γ : ℝ),
      0 < γ ∧ StronglyMonotone γ A ∧
      (∀ g, StronglyMonotone g A → g ≤ γ) ∧
      ‖B‖ < ε ∧ γ < ‖B‖ ∧ MaximalMonotone (A + B) := by
  let a := ε / 4
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨hstrong, hopt, hnorm, _, hlarge, hmax, _⟩ := same_norm_opposite_behavior a ha
  refine ⟨scale a, scale (2 * a), a, ha, hstrong, hopt, ?_, ?_, hmax⟩
  · rw [hnorm]; dsimp [a]; linarith
  · rwa [hnorm]

theorem conjectured_iff_false :
    ¬ ∀ (A B : ℝ →L[ℝ] ℝ) (γ : ℝ), 0 < γ → StronglyMonotone γ A →
      (∀ g, StronglyMonotone g A → g ≤ γ) →
      (MaximalMonotone (A + B) ↔ ‖B‖ ≤ γ) := by
  intro h
  obtain ⟨A, B, γ, hγ, hs, ho, _, hgt, hm⟩ := arbitrarily_small_counterexample 1 (by norm_num)
  exact (not_le_of_gt hgt) ((h A B γ hγ hs ho).mp hm)

#print axioms scale_norm
#print axioms strong_scale
#print axioms optimal_strong_constant
#print axioms positive_scale_maximal
#print axioms same_norm_opposite_behavior
#print axioms arbitrarily_small_counterexample
#print axioms conjectured_iff_false
end MonotonePerturbation
