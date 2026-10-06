import Geometry
import Vanishing

/-!
The printed positive exponent is retained exactly. We refute literal equality,
a positive leading asymptotic constant, and even the weaker two-sided order.
Minima are attained geometric witnesses, not totalized infima.
-/
namespace TLMC1451

/-- The literal formula, even restricted to a sufficiently small interval. -/
def PrintedExactFormula (d : ℕ) : Prop :=
  ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ → ∃ n : ℕ,
      IsMinimumFacetCount d ε n ∧
      (n : ℝ) = c * ε ^ (((d : ℝ) - 1) / 2)

/-- The weakest usual positive optimal-order reading: two-sided constant bounds. -/
def PrintedThetaOrder (d : ℕ) : Prop :=
  ∃ a b δ : ℝ, 0 < a ∧ 0 < b ∧ 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ → ∃ n : ℕ,
      IsMinimumFacetCount d ε n ∧
      a * ε ^ (((d : ℝ) - 1) / 2) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ b * ε ^ (((d : ℝ) - 1) / 2)

/-- A positive leading constant in the standard epsilon-delta definition of
`N(ε) / (c * ε^((d-1)/2)) → 1` as `ε → 0+`.
The unique attained minimum at each error is quantified relationally. -/
def PrintedAsymptoticConstant (d : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ → ∃ n : ℕ,
      IsMinimumFacetCount d ε n ∧
      |(n : ℝ) / (c * ε ^ (((d : ℝ) - 1) / 2)) - 1| < η

theorem exact_implies_theta {d : ℕ} (h : PrintedExactFormula d) :
    PrintedThetaOrder d := by
  obtain ⟨c, δ, hc, hδ, h⟩ := h
  refine ⟨c, c, δ, hc, hc, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨n, hn, heq⟩ := h ε hε hεδ
  exact ⟨n, hn, heq.ge, heq.le⟩

theorem asymptotic_implies_theta {d : ℕ} (h : PrintedAsymptoticConstant d) :
    PrintedThetaOrder d := by
  obtain ⟨c, hc, h⟩ := h
  obtain ⟨δ, hδ, h⟩ := h (1 / 2) (by norm_num)
  refine ⟨c / 2, 2 * c, δ, by positivity, by positivity, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨n, hn, hratio⟩ := h ε hε hεδ
  have hp : 0 < ε ^ (((d : ℝ) - 1) / 2) := Real.rpow_pos_of_pos hε _
  have hcp : 0 < c * ε ^ (((d : ℝ) - 1) / 2) := mul_pos hc hp
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hratio
  have hlo' : 1 / 2 < (n : ℝ) / (c * ε ^ (((d : ℝ) - 1) / 2)) := by linarith
  have hhi' : (n : ℝ) / (c * ε ^ (((d : ℝ) - 1) / 2)) < 2 := by linarith
  have hlo'' := (lt_div_iff₀ hcp).mp hlo'
  have hhi'' := (div_lt_iff₀ hcp).mp hhi'
  exact ⟨n, hn, by nlinarith, by nlinarith⟩

/-- Even a two-sided positive order with the printed exponent is impossible in
`ℝ²`, with the exact source volume error and actual finite geometric facets. -/
theorem dimension_two_not_theta : ¬ PrintedThetaOrder 2 := by
  rintro ⟨a, b, δ, ha, hb, hδ, h⟩
  obtain ⟨ε, hε, hεδ, hgap⟩ :=
    Vanishing.exists_dimension_two_power_gap a b δ ha hb hδ
  obtain ⟨n, _, hlo, hhi⟩ := h ε hε hεδ
  exact hgap n ⟨hlo, hhi⟩

theorem dimension_two_not_exact : ¬ PrintedExactFormula 2 :=
  fun h => dimension_two_not_theta (exact_implies_theta h)

theorem dimension_two_not_asymptotic : ¬ PrintedAsymptoticConstant 2 :=
  fun h => dimension_two_not_theta (asymptotic_implies_theta h)

/-- The dimension-uniform literal reading of the conjecture is false. -/
theorem conjecture_exact_false : ¬ (∀ d : ℕ, 2 ≤ d → PrintedExactFormula d) :=
  fun h => dimension_two_not_exact (h 2 le_rfl)

/-- The dimension-uniform leading-constant reading of the conjecture is false. -/
theorem conjecture_asymptotic_false : ¬ (∀ d : ℕ, 2 ≤ d → PrintedAsymptoticConstant d) :=
  fun h => dimension_two_not_asymptotic (h 2 le_rfl)

/-- The dimension-uniform optimal-order reading of the conjecture is false. -/
theorem conjecture_order_false : ¬ (∀ d : ℕ, 2 ≤ d → PrintedThetaOrder d) :=
  fun h => dimension_two_not_theta (h 2 le_rfl)

end TLMC1451
