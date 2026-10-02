import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open Filter
open scoped Topology
noncomputable section
namespace TLMC714
variable (p : ℕ) [hp : Fact p.Prime]
def term (q : ℕ → ℕ) (n : ℕ) : ℚ_[p] := (p : ℚ_[p]) ^ (-(q n : ℤ))
theorem norm_lower (q : ℕ → ℕ) (n : ℕ) : 1 ≤ ‖term p q n‖ := by
  simp only [term, Padic.norm_p_zpow, neg_neg, zpow_natCast]
  exact one_le_pow₀ (by exact_mod_cast hp.out.one_lt.le)
theorem no_term_limit (q : ℕ → ℕ) : ¬ Tendsto (term p q) atTop (𝓝 0) := by
  intro h
  have hn := h.norm
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa using ge_of_tendsto hn (Filter.Eventually.of_forall (norm_lower p q))
  norm_num at hbad
theorem no_series (q : ℕ → ℕ) : ¬ Summable (term p q) := by
  intro h
  exact no_term_limit p q h.tendsto_atTop_zero
-- Nat.nth Prime enumerates 2,3,5,...; shifting to a one-based index changes nothing.
theorem prime_series_diverges : ¬ Summable (term p (Nat.nth Nat.Prime)) :=
  no_series p _
#print axioms no_series
#print axioms prime_series_diverges
end TLMC714
