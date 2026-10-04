import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
noncomputable section
namespace AuctionRevenue

def law : PMF Unit := PMF.pure ()
def μ : Measure Unit := law.toMeasure
instance : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure law.toMeasure)
def value (_ : Fin 2) (_ : Unit) : ℝ := 1

theorem independent_values : IndepFun (value 0) (value 1) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  change μ ({ω : Unit | (1 : ℝ) ∈ s} ∩ {ω : Unit | (1 : ℝ) ∈ t}) =
    μ {ω : Unit | (1 : ℝ) ∈ s} * μ {ω : Unit | (1 : ℝ) ∈ t}
  by_cases hs : (1 : ℝ) ∈ s <;> by_cases ht : (1 : ℝ) ∈ t <;> simp [hs, ht]

abbrev Bids := Fin 2 → ℝ
def admissible (b : Bids) : Prop := ∀ i, 0 ≤ b i
def truthful : Bids := fun _ => 1
def winner (b : Bids) : Fin 2 := if b 0 ≥ b 1 then 0 else 1
def allocation (b : Bids) (i : Fin 2) : ℝ := if winner b = i then 1 else 0
def firstPrice (b : Bids) : ℝ := b (winner b)
def dropoutPrice (b : Bids) : ℝ := min (b 0) (b 1)
def payment (price : Bids → ℝ) (b : Bids) (i : Fin 2) : ℝ :=
  if winner b = i then price b else 0
def utility (price : Bids → ℝ) (b : Bids) (i : Fin 2) : ℝ :=
  allocation b i - payment price b i
def deviation (i : Fin 2) (r : ℝ) : Bids := Function.update truthful i r
def Nash (price : Bids → ℝ) (b : Bids) : Prop :=
  ∀ i r, 0 ≤ r → utility price (Function.update b i r) i ≤ utility price b i

-- This is the first price at which an ascending clock makes some bidder drop out.
def FirstDropout (b : Bids) (p : ℝ) : Prop :=
  0 ≤ p ∧ (∃ i, b i ≤ p) ∧
  ∀ q, 0 ≤ q → q < p → ∀ i, q < b i

theorem actual_first_dropout (b : Bids) (hb : admissible b) :
    FirstDropout b (dropoutPrice b) := by
  refine ⟨le_min (hb 0) (hb 1), ?_, ?_⟩
  · by_cases h : b 0 ≤ b 1
    · exact ⟨0, by simp [dropoutPrice, min_eq_left h]⟩
    · exact ⟨1, by simp [dropoutPrice, min_eq_right (le_of_not_ge h)]⟩
  · intro q _ hq i
    fin_cases i
    · exact lt_of_lt_of_le hq (min_le_left _ _)
    · exact lt_of_lt_of_le hq (min_le_right _ _)

theorem dropout_unique (b : Bids) (hb : admissible b) (p : ℝ)
    (h : FirstDropout b p) : p = dropoutPrice b := by
  have hd := actual_first_dropout b hb
  apply le_antisymm
  · by_contra hh
    have hp : dropoutPrice b < p := lt_of_not_ge hh
    obtain ⟨i, hi⟩ := hd.2.1
    exact (not_lt_of_ge hi) (h.2.2 _ hd.1 hp i)
  · obtain ⟨i, hi⟩ := h.2.1
    fin_cases i
    · exact le_trans (min_le_left _ _) hi
    · exact le_trans (min_le_right _ _) hi

theorem winner_maximizes (b : Bids) (i : Fin 2) : b i ≤ b (winner b) := by
  fin_cases i <;> by_cases h : b 1 ≤ b 0 <;> simp [winner, h] <;> linarith

theorem allocation_feasible (b : Bids) : ∑ i, allocation b i = 1 := by
  by_cases h : b 1 ≤ b 0 <;> simp [allocation, winner, h, Fin.sum_univ_two]

theorem revenue_is_payments (price : Bids → ℝ) (b : Bids) :
    ∑ i, payment price b i = price b := by
  by_cases h : b 1 ≤ b 0 <;> simp [payment, winner, h, Fin.sum_univ_two]

theorem truthful_admissible : admissible truthful := by intro i; norm_num [truthful]
theorem truthful_utilities (price : Bids → ℝ) (hp : price truthful = 1) :
    ∀ i, utility price truthful i = 0 := by
  intro i
  unfold utility payment allocation
  split <;> simp [hp]

theorem first_truthful_price : firstPrice truthful = 1 := by simp [firstPrice, truthful]
theorem english_truthful_price : dropoutPrice truthful = 1 := by simp [dropoutPrice, truthful]

theorem first_deviation (i : Fin 2) (r : ℝ) :
    utility firstPrice (deviation i r) i ≤ 0 := by
  fin_cases i <;>
    by_cases h : r ≥ 1 <;>
    by_cases h' : r ≤ 1 <;>
    simp [utility, payment, allocation, firstPrice, winner, deviation, truthful,
      Function.update, h, h'] <;> linarith

theorem english_deviation (i : Fin 2) (r : ℝ) :
    utility dropoutPrice (deviation i r) i ≤ 0 := by
  fin_cases i <;>
    by_cases h : r ≥ 1 <;>
    by_cases h' : r ≤ 1 <;>
    simp [utility, payment, allocation, dropoutPrice, winner, deviation, truthful,
      Function.update, h, h', min_eq_left, min_eq_right] <;> linarith

theorem first_equilibrium : Nash firstPrice truthful := by
  intro i r _
  rw [truthful_utilities firstPrice first_truthful_price i]
  exact first_deviation i r

theorem english_equilibrium : Nash dropoutPrice truthful := by
  intro i r _
  rw [truthful_utilities dropoutPrice english_truthful_price i]
  exact english_deviation i r

-- All values and strategies are deterministic, so these are also Bayesian equilibria.
def expectedRevenue (price : Bids → ℝ) : ℝ :=
  ∫ _ : Unit, (∑ i, payment price truthful i) ∂μ

theorem expected_revenue (price : Bids → ℝ) :
    expectedRevenue price = price truthful := by
  unfold expectedRevenue
  simp only [revenue_is_payments]
  simp

theorem actual_revenues :
    expectedRevenue firstPrice = 1 ∧ expectedRevenue dropoutPrice = 1 := by
  simp [expected_revenue, first_truthful_price, english_truthful_price]

theorem counterexample :
    IndepFun (value 0) (value 1) μ ∧ admissible truthful ∧
    FirstDropout truthful 1 ∧ Nash firstPrice truthful ∧ Nash dropoutPrice truthful ∧
    expectedRevenue dropoutPrice - expectedRevenue firstPrice = 0 ∧
    ¬ (0 < expectedRevenue dropoutPrice - expectedRevenue firstPrice) := by
  refine ⟨independent_values, truthful_admissible, ?_, first_equilibrium,
    english_equilibrium, ?_, ?_⟩
  · simpa [english_truthful_price] using actual_first_dropout truthful truthful_admissible
  · rw [actual_revenues.1, actual_revenues.2]; norm_num
  · rw [actual_revenues.1, actual_revenues.2]; norm_num

#print axioms independent_values
#print axioms actual_first_dropout
#print axioms dropout_unique
#print axioms allocation_feasible
#print axioms first_equilibrium
#print axioms english_equilibrium
#print axioms actual_revenues
#print axioms counterexample
end AuctionRevenue
