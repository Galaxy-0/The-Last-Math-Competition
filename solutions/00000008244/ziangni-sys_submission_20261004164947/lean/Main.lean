import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section
namespace SinglePeakedCrossing
abbrev Agent := Fin 3
abbrev Alternative := Fin 3

def alternativePosition : Alternative → ℝ := ![0,2,3]
def agentPosition : Agent → ℝ := ![0,5/4,7/4]
def utility (v : Agent) (a : Alternative) : ℝ :=
  -(alternativePosition a - agentPosition v)^2

-- Ranks zero, one, two: abc, bac, bca respectively.
def rank : Agent → Alternative → Fin 3 :=
  ![![0,1,2], ![1,0,2], ![2,0,1]]
def Pref (v : Agent) (a b : Alternative) : Prop := rank v a < rank v b
instance (v : Agent) : DecidableRel (Pref v) :=
  fun a b => inferInstanceAs (Decidable (rank v a < rank v b))

theorem actual_utility_preference (v : Agent) (a b : Alternative) :
    Pref v a b ↔ utility v b < utility v a := by
  fin_cases v <;> fin_cases a <;> fin_cases b <;>
    norm_num [Pref, rank, utility, alternativePosition, agentPosition, Fin.lt_def, Fin.ext_iff]

theorem strict_total_preferences :
    ∀ v, Irreflexive (Pref v) ∧ Transitive (Pref v) ∧
      ∀ a b, a ≠ b → Pref v a b ∨ Pref v b a := by
  unfold Irreflexive Transitive
  decide

theorem distinct_preferences :
    ∀ v w, v ≠ w → ∃ a b,
      (Pref v a b ∧ ¬ Pref w a b) ∨ (Pref w a b ∧ ¬ Pref v a b) := by decide

theorem alternatives_on_axis :
    ∀ a b, a < b → alternativePosition a < alternativePosition b := by
  intro a b
  fin_cases a <;> fin_cases b <;> norm_num [alternativePosition]
theorem agents_in_order :
    ∀ v w, v < w → agentPosition v < agentPosition w := by
  intro v w
  fin_cases v <;> fin_cases w <;> norm_num [agentPosition]

-- Strict preference rises to a peak and falls away on each side of the same axis.
def SinglePeaked : Prop :=
  ∀ v, ∃ peak : Alternative,
    (∀ a b, a < b → b ≤ peak → Pref v b a) ∧
    (∀ a b, peak ≤ a → a < b → Pref v a b)

-- Each ordered-pair comparison set is an initial or final voter segment.
def LowerComparison (a b : Alternative) : Prop :=
  ∀ v w, v ≤ w → Pref w a b → Pref v a b
def UpperComparison (a b : Alternative) : Prop :=
  ∀ v w, v ≤ w → Pref v a b → Pref w a b
def SingleCrossing : Prop :=
  ∀ a b, LowerComparison a b ∨ UpperComparison a b

theorem single_peaked : SinglePeaked := by unfold SinglePeaked; decide
theorem single_crossing : SingleCrossing := by
  unfold SingleCrossing LowerComparison UpperComparison
  decide

def supporters (a b : Alternative) : Finset Agent :=
  Finset.univ.filter (fun v => Pref v a b)
def MajorityPref (a b : Alternative) : Prop :=
  Fintype.card Agent < 2*(supporters a b).card
theorem median_winner : ∀ a, a ≠ 1 → MajorityPref 1 a := by
  unfold MajorityPref
  decide

def dimension : ℕ := Module.finrank ℝ ℝ
theorem one_dimension : dimension = 1 := Module.finrank_self ℝ
theorem bound_failure : 2^dimension*dimension < Fintype.card Agent := by
  norm_num [one_dimension]

theorem counterexample :
    (∀ v a b, Pref v a b ↔ utility v b < utility v a) ∧
    (∀ v, Irreflexive (Pref v) ∧ Transitive (Pref v) ∧
      ∀ a b, a ≠ b → Pref v a b ∨ Pref v b a) ∧
    (∀ v w, v ≠ w → ∃ a b,
      (Pref v a b ∧ ¬ Pref w a b) ∨ (Pref w a b ∧ ¬ Pref v a b)) ∧
    SinglePeaked ∧ SingleCrossing ∧ dimension = 1 ∧
    2^dimension*dimension < Fintype.card Agent :=
  ⟨actual_utility_preference, strict_total_preferences, distinct_preferences,
    single_peaked, single_crossing, one_dimension, bound_failure⟩

#print axioms actual_utility_preference
#print axioms strict_total_preferences
#print axioms distinct_preferences
#print axioms alternatives_on_axis
#print axioms agents_in_order
#print axioms single_peaked
#print axioms single_crossing
#print axioms median_winner
#print axioms one_dimension
#print axioms counterexample
end SinglePeakedCrossing
