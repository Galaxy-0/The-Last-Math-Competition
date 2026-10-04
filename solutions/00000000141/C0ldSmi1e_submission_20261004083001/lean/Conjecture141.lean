import Conjecture141.Counting
import Conjecture141.Growth
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! The actual counting function is not asymptotic to the conjectured expression. -/
noncomputable section
open Filter
open scoped Topology Asymptotics

namespace Conjecture141

/-- The primary asymptotic assertion of the source, using Mathlib's actual equivalence relation. -/
def ConjectureClaim : Prop :=
  (fun n : ℕ => (N n : ℝ)) ~[atTop] proposedCount sourceConstant

theorem count_not_proposed_ratio_limit (c : ℝ) (hc : 0 < c) :
    ¬ Tendsto (fun n : ℕ => (N n : ℝ) / proposedCount c n) atTop (𝓝 1) :=
  no_proposed_asymptotic_of_factorial_lower N factorial_le_count_even c hc

/-- The failure is not specific to the printed leading constant. -/
theorem count_not_asymptotic (c : ℝ) (hc : 0 < c) :
    ¬ ((fun n : ℕ => (N n : ℝ)) ~[atTop] proposedCount c) := by
  intro h
  have hnz : ∀ᶠ n : ℕ in atTop, proposedCount c n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ne_of_gt (proposedCount_pos c hc n (by omega))
  exact count_not_proposed_ratio_limit c hc
    ((Asymptotics.isEquivalent_iff_tendsto_one hnz).mp h)

/-- Direct negation of the conjecture's first assertion with its exact positive constant. -/
theorem conjecture141_disproof : ¬ ConjectureClaim :=
  count_not_asymptotic sourceConstant sourceConstant_pos

end Conjecture141
