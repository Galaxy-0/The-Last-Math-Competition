import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
noncomputable section
open scoped Topology
namespace TLMC414
-- One-row Young diagram (3); terminal cell is column 3, row 1.
-- From column 1 choose column 2 or 3 equiprobably; from 2 go to 3.
def hitFrom3 : ℝ := 1
def hitFrom2 : ℝ := hitFrom3
def hitFrom1 : ℝ := (hitFrom2 + hitFrom3) / 2
def visitProbability : ℝ := (hitFrom1 + hitFrom2 + hitFrom3) / 3
theorem visits_terminal : visitProbability = 1 := by
  norm_num [visitProbability, hitFrom1, hitFrom2, hitFrom3]
theorem bound_fails : ¬ |visitProbability - (3 - 1 : ℝ)| ≤ (3 : ℝ) ^ (- (1/2 : ℝ)) := by
  rw [visits_terminal]
  have h : (3 : ℝ) ^ (- (1/2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  norm_num at ⊢
  linarith
#print axioms visits_terminal
#print axioms bound_fails
end TLMC414
