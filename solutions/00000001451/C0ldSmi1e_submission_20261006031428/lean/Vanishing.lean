import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Tactic

namespace Vanishing

open Filter Set Topology

/-- Arbitrarily near zero, no natural number lies between positive fixed
multiples of `sqrt ε`. -/
theorem exists_sqrt_gap
    (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∀ n : ℕ,
      ¬ (a * Real.sqrt ε ≤ (n : ℝ) ∧ (n : ℝ) ≤ b * Real.sqrt ε) := by
  let t : ℝ := min (Real.sqrt δ) (1 / b) / 2
  have hm : 0 < min (Real.sqrt δ) (1 / b) :=
    lt_min (Real.sqrt_pos.2 hδ) (one_div_pos.mpr hb)
  have ht : 0 < t := half_pos hm
  have htδ : t < Real.sqrt δ :=
    lt_of_lt_of_le (half_lt_self hm) (min_le_left _ _)
  have htb : t < 1 / b :=
    lt_of_lt_of_le (half_lt_self hm) (min_le_right _ _)
  have heδ : t ^ 2 < δ := by
    have hs := Real.sq_sqrt hδ.le
    nlinarith
  have hbt : b * t < 1 := by
    have hx := (lt_div_iff₀ hb).mp htb
    nlinarith
  have hsqrt : Real.sqrt (t ^ 2) = t := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
  refine ⟨t ^ 2, sq_pos_of_pos ht, heδ, ?_⟩
  rintro n ⟨hlo, hhi⟩
  rw [hsqrt] at hlo hhi
  have hn : n < 1 := by
    exact_mod_cast lt_of_le_of_lt hhi hbt
  have hz : n = 0 := by omega
  rw [hz] at hlo
  norm_num at hlo
  exact (not_le_of_gt (mul_pos ha ht)) hlo

/-- No positive square-root sandwich can hold for a natural-valued function. -/
theorem not_nat_sqrt_bounds
    (N : ℝ → ℕ) (a b δ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) :
    ¬ (∀ ε : ℝ, 0 < ε → ε < δ →
      a * Real.sqrt ε ≤ (N ε : ℝ) ∧ (N ε : ℝ) ≤ b * Real.sqrt ε) := by
  intro h
  obtain ⟨ε, hε, hεδ, hgap⟩ := exists_sqrt_gap a b δ ha hb hδ
  exact hgap (N ε) (h ε hε hεδ)

/-- The obstruction also holds when the natural-number witness may be chosen
separately for each positive error. -/
theorem not_exists_nat_sqrt_bounds
    (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) :
    ¬ (∀ ε : ℝ, 0 < ε → ε < δ → ∃ n : ℕ,
      a * Real.sqrt ε ≤ (n : ℝ) ∧ (n : ℝ) ≤ b * Real.sqrt ε) := by
  intro h
  obtain ⟨ε, hε, hεδ, hgap⟩ := exists_sqrt_gap a b δ ha hb hδ
  obtain ⟨n, hn⟩ := h ε hε hεδ
  exact hgap n hn

/-- In dimension two, the stated exponent `(d - 1) / 2` is exactly the
square-root exponent. -/
theorem dimension_two_power (ε : ℝ) :
    ε ^ (((2 : ℝ) - 1) / 2) = Real.sqrt ε := by
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- The same gap in the exact real-power notation of the dimension-two rate. -/
theorem exists_dimension_two_power_gap
    (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∀ n : ℕ,
      ¬ (a * ε ^ (((2 : ℝ) - 1) / 2) ≤ (n : ℝ) ∧
        (n : ℝ) ≤ b * ε ^ (((2 : ℝ) - 1) / 2)) := by
  simpa only [dimension_two_power] using exists_sqrt_gap a b δ ha hb hδ

/-- Existentially quantified version of the obstruction. -/
theorem no_nat_sqrt_bounds (N : ℝ → ℕ) :
    ¬ ∃ a b δ : ℝ, 0 < a ∧ 0 < b ∧ 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        a * Real.sqrt ε ≤ (N ε : ℝ) ∧ (N ε : ℝ) ≤ b * Real.sqrt ε := by
  rintro ⟨a, b, δ, ha, hb, hδ, h⟩
  exact not_nat_sqrt_bounds N a b δ ha hb hδ h

/-- Asymptotic equivalence to a positive square-root rate entails an explicit
positive two-sided bound on a punctured interval. -/
theorem sqrt_bounds_of_isEquivalent
    (f : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (h : Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ)) f
      (fun ε => c * Real.sqrt ε)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      (c / 2) * Real.sqrt ε ≤ f ε ∧ f ε ≤ (2 * c) * Real.sqrt ε := by
  obtain ⟨φ, hφ, heq⟩ := h.exists_eq_mul
  have hbounds : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 / 2 : ℝ) < φ ε ∧ φ ε < 2 :=
    hφ (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨δ, hδ, hlocal⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hbounds.and heq)
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨hφlow, hφhigh⟩ := (hlocal ⟨hε, hεδ⟩).1
  have heqε : f ε = φ ε * (c * Real.sqrt ε) := (hlocal ⟨hε, hεδ⟩).2
  have hpos : 0 ≤ c * Real.sqrt ε := (mul_pos hc (Real.sqrt_pos.2 hε)).le
  constructor
  · calc
      c / 2 * Real.sqrt ε = (1 / 2) * (c * Real.sqrt ε) := by ring
      _ ≤ φ ε * (c * Real.sqrt ε) := mul_le_mul_of_nonneg_right hφlow.le hpos
      _ = f ε := heqε.symm
  · calc
      f ε = φ ε * (c * Real.sqrt ε) := heqε
      _ ≤ 2 * (c * Real.sqrt ε) := mul_le_mul_of_nonneg_right hφhigh.le hpos
      _ = (2 * c) * Real.sqrt ε := by ring

/-- A natural-valued function is never asymptotically equivalent at zero from
the right to a positive square-root rate. -/
theorem not_nat_isEquivalent_sqrt
    (N : ℝ → ℕ) (c : ℝ) (hc : 0 < c) :
    ¬ Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ)) (fun ε => (N ε : ℝ))
      (fun ε => c * Real.sqrt ε) := by
  intro h
  obtain ⟨δ, hδ, hbounds⟩ := sqrt_bounds_of_isEquivalent (fun ε => (N ε : ℝ)) c hc h
  exact not_nat_sqrt_bounds N (c / 2) (2 * c) δ (by positivity) (by positivity) hδ hbounds

/-- Dimension-two version in the exact real-power notation. -/
theorem not_nat_isEquivalent_dimension_two_power
    (N : ℝ → ℕ) (c : ℝ) (hc : 0 < c) :
    ¬ Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ)) (fun ε => (N ε : ℝ))
      (fun ε => c * ε ^ (((2 : ℝ) - 1) / 2)) := by
  simpa only [dimension_two_power] using not_nat_isEquivalent_sqrt N c hc

end Vanishing
