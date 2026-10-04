import Conjecture428.Expectation
import Conjecture428.Asymptotics

/-! Disproof of the exact proposed additive asymptotic for the actual uniform mean. -/

noncomputable section
open Filter
open scoped Topology

namespace Conjecture428

/-- The source's statement with an arbitrary real constant and an additive `o(1)`
remainder, expressed as convergence of the exact remainder to zero. -/
def ClaimedExpansion : Prop :=
  ∃ c : ℝ, Tendsto (fun n => meanDurfee n - (mainTerm n + c)) atTop (𝓝 0)

theorem proposed_excess_tendsto_atTop :
    Tendsto (fun n => mainTerm n - meanDurfee n) atTop atTop :=
  mainTerm_sub_tendsto_atTop meanDurfee meanDurfee_le_sqrt

theorem no_finite_additive_correction (c : ℝ) :
    ¬ Tendsto (fun n => meanDurfee n - mainTerm n) atTop (𝓝 c) :=
  no_constant_correction meanDurfee meanDurfee_le_sqrt c

theorem conjecture_false : ¬ ClaimedExpansion := by
  rintro ⟨c, hc⟩
  apply no_finite_additive_correction c
  have h := hc.add (tendsto_const_nhds (x := c))
  convert h using 1
  · funext n
    dsimp
    ring
  · simp

end Conjecture428
