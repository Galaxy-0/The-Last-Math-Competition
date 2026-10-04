import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
namespace CoalitionVCG
inductive Allocation | none | first | second deriving DecidableEq
open Allocation
abbrev Bids := Fin 2 → ℝ
def Nonnegative (b : Bids) : Prop := ∀ i, 0 ≤ b i
def receives : Allocation → Fin 2 → Bool
  | Allocation.none, _ => false
  | first, i => i == 0
  | second, i => i == 1
def welfare (b : Bids) : Allocation → ℝ
  | Allocation.none => 0 | first => b 0 | second => b 1
def winner (b : Bids) : Allocation := if b 1 ≤ b 0 then first else second
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0
def othersWelfare (b : Bids) (i : Fin 2) (a : Allocation) : ℝ :=
  if receives a (other i) then b (other i) else 0
def withoutBest (b : Bids) (i : Fin 2) : ℝ := max 0 (b (other i))
def payment (b : Bids) (i : Fin 2) : ℝ :=
  withoutBest b i - othersWelfare b i (winner b)
def values : Bids := ![2, 1]
def utility (b : Bids) (i : Fin 2) : ℝ :=
  (if receives (winner b) i then values i else 0) - payment b i
def truth : Bids := values
def coalitionReport : Bids := ![2, 0]
def unilateral (i : Fin 2) (r : ℝ) : Bids := Function.update truth i r
def singleGain (i : Fin 2) (r : ℝ) := utility (unilateral i r) i - utility truth i
def coalition : Finset (Fin 2) := Finset.univ
def coalitionGain := ∑ i ∈ coalition, (utility coalitionReport i - utility truth i)

theorem winner_maximizes (b : Bids) (hb : Nonnegative b) :
    ∀ a, welfare b a ≤ welfare b (winner b) := by
  intro a
  unfold winner
  split_ifs with h
  · cases a <;> simp only [welfare]
    · exact hb 0
    · exact le_rfl
    · exact h
  · cases a <;> simp only [welfare]
    · exact hb 1
    · exact le_of_lt (lt_of_not_ge h)
    · exact le_rfl

theorem withoutBest_is_actual_maximum (b : Bids) (i : Fin 2) :
    (∀ a, receives a i = false → othersWelfare b i a ≤ withoutBest b i) ∧
    (∃ a, receives a i = false ∧ othersWelfare b i a = withoutBest b i) := by
  fin_cases i <;> constructor
  · intro a ha
    cases a <;> simp [receives, othersWelfare, other, withoutBest] at ha ⊢
  · by_cases h : 0 ≤ b 1
    · exact ⟨second, by simp [receives], by simp [othersWelfare, receives, other, withoutBest, max_eq_right h]⟩
    · exact ⟨Allocation.none, rfl, by simp [othersWelfare, receives, other, withoutBest, max_eq_left (le_of_not_ge h)]⟩
  · intro a ha
    cases a <;> simp [receives, othersWelfare, other, withoutBest] at ha ⊢
  · by_cases h : 0 ≤ b 0
    · exact ⟨first, by simp [receives], by simp [othersWelfare, receives, other, withoutBest, max_eq_right h]⟩
    · exact ⟨Allocation.none, rfl, by simp [othersWelfare, receives, other, withoutBest, max_eq_left (le_of_not_ge h)]⟩

theorem truthful_utilities : utility truth 0 = 1 ∧ utility truth 1 = 0 := by
  norm_num [utility, payment, withoutBest, othersWelfare, receives, winner, truth, values, other]

theorem coalition_utilities : utility coalitionReport 0 = 2 ∧ utility coalitionReport 1 = 0 := by
  norm_num [utility, payment, withoutBest, othersWelfare, receives, winner, coalitionReport, values, other]

theorem unilateral_gain_nonpositive (i : Fin 2) (r : ℝ) (_hr : 0 ≤ r) :
    singleGain i r ≤ 0 := by
  fin_cases i
  · by_cases h : 1 ≤ r
    · simp [singleGain, utility, unilateral, payment, withoutBest, othersWelfare,
        receives, winner, truth, values, other, h]
    · simp [singleGain, utility, unilateral, payment, withoutBest, othersWelfare,
        receives, winner, truth, values, other, h, max_eq_right _hr]
  · by_cases h : r ≤ 2
    · simp [singleGain, utility, unilateral, payment, withoutBest, othersWelfare,
        receives, winner, truth, values, other, h, max_eq_right _hr]
    · simp [singleGain, utility, unilateral, payment, withoutBest, othersWelfare,
        receives, winner, truth, values, other, h]

theorem single_gain_maximum_zero (i : Fin 2) :
    (∀ r, 0 ≤ r → singleGain i r ≤ 0) ∧
    (∃ r, 0 ≤ r ∧ singleGain i r = 0) := by
  constructor
  · exact unilateral_gain_nonpositive i
  · refine ⟨truth i, ?_, ?_⟩
    · fin_cases i <;> norm_num [truth, values]
    · simp [singleGain, unilateral]

theorem actual_coalition_gain : coalitionGain = 1 := by
  norm_num [coalitionGain, coalition, Fin.sum_univ_two, truthful_utilities.1,
    truthful_utilities.2, coalition_utilities.1, coalition_utilities.2]

theorem coalition_card : coalition.card = 2 := by simp [coalition]

theorem reports_admissible : Nonnegative truth ∧ Nonnegative coalitionReport := by
  constructor <;> intro i <;> fin_cases i <;> norm_num [truth, values, coalitionReport]

theorem subadditivity_counterexample :
    Nonnegative truth ∧ Nonnegative coalitionReport ∧
    (∀ i, (∀ r, 0 ≤ r → singleGain i r ≤ 0) ∧
      ∃ r, 0 ≤ r ∧ singleGain i r = 0) ∧
    coalitionGain > (coalition.card : ℝ) * 0 := by
  exact ⟨reports_admissible.1, reports_admissible.2, single_gain_maximum_zero,
    by rw [actual_coalition_gain, coalition_card]; norm_num⟩
end CoalitionVCG
#print axioms CoalitionVCG.winner_maximizes
#print axioms CoalitionVCG.withoutBest_is_actual_maximum
#print axioms CoalitionVCG.single_gain_maximum_zero
#print axioms CoalitionVCG.actual_coalition_gain
#print axioms CoalitionVCG.subadditivity_counterexample
