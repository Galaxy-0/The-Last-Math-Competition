import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
noncomputable section
open scoped Topology
namespace TLMC217
open Filter

def tower : ℕ → ℝ
  | 0 => 1
  | n+1 => (1 : ℝ) ^ (tower n)
theorem tower_one (n : ℕ) : tower n = 1 := by
  cases n <;> simp [tower]
theorem tower_limit : Tendsto tower atTop (𝓝 (1 : ℝ)) := by
  have heq : tower = (fun _ : ℕ => (1 : ℝ)) := funext tower_one
  rw [heq]
  exact tendsto_const_nhds
theorem algebraic_interior : IsAlgebraic ℚ (1 : ℝ) ∧
    Real.exp (-Real.exp 1) < 1 ∧ 1 < Real.exp (1 / Real.exp 1) := by
  refine ⟨isAlgebraic_one, ?_, ?_⟩
  · exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos 1))
  · exact Real.one_lt_exp_iff.mpr (one_div_pos.mpr (Real.exp_pos 1))
theorem not_transcendental : ¬ Transcendental ℚ (1 : ℝ) := by
  exact not_not.mpr isAlgebraic_one
#print axioms tower_limit
#print axioms algebraic_interior
#print axioms not_transcendental
end TLMC217
