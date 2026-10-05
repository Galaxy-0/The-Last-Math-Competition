import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A counterexample to the literal formula in conjecture 00000000331

The numerator `a` is fixed. The radius is `ψ n`, and the series has term
`ψ n / n`. This file makes no claim about a differently formulated
inhomogeneous Duffin–Schaeffer problem.
-/

open Filter MeasureTheory Set
open scoped BigOperators

namespace Conjecture331

/-- The sum over precisely the positive denominators `1, ..., N`. -/
noncomputable def partialSum (ψ : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, ψ (k + 1) / ((k + 1 : ℕ) : ℝ)

/-- Genuine divergence of the positive-denominator partial sums to infinity. -/
def Diverges (ψ : ℕ → ℝ) : Prop :=
  Tendsto (partialSum ψ) atTop atTop

/-- Successful positive denominators, with one fixed real numerator. -/
def hitSet (a : ℝ) (ψ : ℕ → ℝ) (α : ℝ) : Set ℕ :=
  {n | 0 < n ∧ |α - a / (n : ℝ)| < ψ n}

/-- The literal infinitely-many-denominators conclusion. -/
def InfinitelyApproximable (a : ℝ) (ψ : ℕ → ℝ) (α : ℝ) : Prop :=
  (hitSet a ψ α).Infinite

/-- The displayed implication, for a fixed parameter and a specified measure. -/
def LiteralClaim (μ : Measure ℝ) (a : ℝ) : Prop :=
  ∀ ψ : ℕ → ℝ, (∀ n, 0 < n → 0 < ψ n) → Diverges ψ →
    ∀ᵐ α ∂μ, InfinitelyApproximable a ψ α

/-- The version allowing nonnegative, rather than only positive, radii. -/
def NonnegativeLiteralClaim (μ : Measure ℝ) (a : ℝ) : Prop :=
  ∀ ψ : ℕ → ℝ, (∀ n, 0 < n → 0 ≤ ψ n) → Diverges ψ →
    ∀ᵐ α ∂μ, InfinitelyApproximable a ψ α

/-- A strictly positive constant approximation function. -/
noncomputable def radius (_n : ℕ) : ℝ := 1 / 4

/-- A closed interval of length `1/4` strictly inside the unit interval. -/
noncomputable def failureInterval : Set ℝ := Icc (1 / 2) (3 / 4)

theorem radius_pos (n : ℕ) : 0 < radius n := by
  norm_num [radius]

theorem divergence_means_exceeding_every_bound (ψ : ℕ → ℝ) :
    Diverges ψ ↔ ∀ B : ℝ, ∃ N : ℕ, ∀ M ≥ N, B < partialSum ψ M := by
  constructor
  · intro h B
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp h (B + 1)
    exact ⟨N, fun M hM => lt_of_lt_of_le (by linarith) (hN M hM)⟩
  · intro h
    apply tendsto_atTop_atTop.mpr
    intro B
    obtain ⟨N, hN⟩ := h B
    exact ⟨N, fun M hM => (hN M hM).le⟩

theorem infinite_means_arbitrarily_large_denominators (a α : ℝ) (ψ : ℕ → ℝ) :
    InfinitelyApproximable a ψ α ↔
      ∀ N : ℕ, ∃ n : ℕ, N < n ∧ 0 < n ∧ |α - a / (n : ℝ)| < ψ n := by
  simp only [InfinitelyApproximable, Set.infinite_iff_exists_gt, hitSet, mem_setOf_eq]
  constructor
  · intro h N
    obtain ⟨n, hn, hN⟩ := h N
    exact ⟨n, hN, hn⟩
  · intro h N
    obtain ⟨n, hN, hn⟩ := h N
    exact ⟨n, hn, hN⟩

theorem partialSum_radius (N : ℕ) :
    partialSum radius N = (1 / 4 : ℝ) *
      ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1)) := by
  simp only [partialSum, radius, Nat.cast_add, Nat.cast_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

theorem radius_diverges : Diverges radius := by
  have h := Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop
    (show (0 : ℝ) < 1 / 4 by norm_num)
  unfold Diverges
  convert h using 1
  funext N
  exact partialSum_radius N

/-- Each successful denominator is below one bound depending only on `a`. -/
theorem hits_bounded (a α : ℝ) (hα : 1 / 2 ≤ α) :
    ∃ N : ℕ, ∀ n ∈ hitSet a radius α, n < N := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * a)
  refine ⟨N, ?_⟩
  intro n hn
  by_contra hnot
  have hlarge : N ≤ n := le_of_not_gt hnot
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hlarge
  have hcenter : a / (n : ℝ) < 1 / 4 := by
    apply (div_lt_iff₀ hnpos).mpr
    linarith
  have hhit : α - a / (n : ℝ) < 1 / 4 := by
    exact (abs_lt.mp hn.2).2
  linarith

theorem hits_finite (a α : ℝ) (hα : 1 / 2 ≤ α) :
    (hitSet a radius α).Finite := by
  obtain ⟨N, hN⟩ := hits_bounded a α hα
  exact (Finset.finite_toSet (Finset.range N)).subset
    (fun n hn => Finset.mem_coe.mpr (Finset.mem_range.mpr (hN n hn)))

theorem fails_on_interval (a α : ℝ) (hα : α ∈ failureInterval) :
    ¬InfinitelyApproximable a radius α :=
  (hits_finite a α hα.1).not_infinite

theorem failureInterval_volume : volume failureInterval = ENNReal.ofReal (1 / 4) := by
  rw [failureInterval, Real.volume_Icc]
  norm_num

theorem failureInterval_volume_pos : 0 < volume failureInterval := by
  rw [failureInterval_volume]
  positivity

theorem not_ae_of_interval_positive (μ : Measure ℝ) (a : ℝ)
    (hμ : 0 < μ failureInterval) :
    ¬(∀ᵐ α ∂μ, InfinitelyApproximable a radius α) := by
  intro h
  have hzero := ae_iff.mp h
  have hle : μ failureInterval ≤ μ {α | ¬InfinitelyApproximable a radius α} :=
    measure_mono (fun α hα => fails_on_interval a α hα)
  rw [hzero] at hle
  exact (not_lt_of_ge hle) hμ

theorem not_ae_real (a : ℝ) :
    ¬(∀ᵐ α ∂volume, InfinitelyApproximable a radius α) :=
  not_ae_of_interval_positive volume a failureInterval_volume_pos

theorem failureInterval_subset_unit : failureInterval ⊆ Icc (0 : ℝ) 1 := by
  intro α hα
  constructor <;> linarith [hα.1, hα.2]

theorem unit_failureInterval_volume :
    volume.restrict (Icc (0 : ℝ) 1) failureInterval = ENNReal.ofReal (1 / 4) := by
  rw [Measure.restrict_apply (show MeasurableSet failureInterval from measurableSet_Icc)]
  rw [inter_eq_self_of_subset_left failureInterval_subset_unit]
  exact failureInterval_volume

theorem not_ae_unit (a : ℝ) :
    ¬(∀ᵐ α ∂volume.restrict (Icc (0 : ℝ) 1), InfinitelyApproximable a radius α) := by
  apply not_ae_of_interval_positive
  rw [unit_failureInterval_volume]
  positivity

/-- The same failure holds on every domain containing the displayed interval. -/
theorem not_ae_restrict (a : ℝ) (s : Set ℝ) (hs : failureInterval ⊆ s) :
    ¬(∀ᵐ α ∂volume.restrict s, InfinitelyApproximable a radius α) := by
  apply not_ae_of_interval_positive
  rw [Measure.restrict_apply (show MeasurableSet failureInterval from measurableSet_Icc)]
  rw [inter_eq_self_of_subset_left hs]
  exact failureInterval_volume_pos

theorem not_ae_unit_open (a : ℝ) :
    ¬(∀ᵐ α ∂volume.restrict (Ioo (0 : ℝ) 1), InfinitelyApproximable a radius α) := by
  apply not_ae_restrict
  intro α hα
  constructor <;> linarith [hα.1, hα.2]

theorem not_ae_unit_half_open (a : ℝ) :
    ¬(∀ᵐ α ∂volume.restrict (Ico (0 : ℝ) 1), InfinitelyApproximable a radius α) := by
  apply not_ae_restrict
  intro α hα
  constructor <;> linarith [hα.1, hα.2]

/-- Both standard measure-domain readings fail for every fixed real numerator. -/
theorem literal_claim_false (a : ℝ) :
    ¬LiteralClaim volume a ∧ ¬LiteralClaim (volume.restrict (Icc (0 : ℝ) 1)) a := by
  constructor
  · intro h
    exact not_ae_real a (h radius (fun n _hn => radius_pos n) radius_diverges)
  · intro h
    exact not_ae_unit a (h radius (fun n _hn => radius_pos n) radius_diverges)

theorem nonnegative_literal_claim_false (a : ℝ) :
    ¬NonnegativeLiteralClaim volume a ∧
      ¬NonnegativeLiteralClaim (volume.restrict (Icc (0 : ℝ) 1)) a := by
  constructor
  · intro h
    exact not_ae_real a (h radius (fun n _hn => (radius_pos n).le) radius_diverges)
  · intro h
    exact not_ae_unit a (h radius (fun n _hn => (radius_pos n).le) radius_diverges)

end Conjecture331
