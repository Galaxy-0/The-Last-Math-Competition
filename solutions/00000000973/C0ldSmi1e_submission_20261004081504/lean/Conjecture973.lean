import Conjecture973.BoundedSet

/-! The order-two obstruction applies to every union of two genuine complex disks. -/

noncomputable section

namespace Conjecture973

/-- The explicit low-order assertion in both language versions of conjecture 973. -/
def SmallOrderClaim (K : Set ℂ) : Prop :=
  ∀ n : ℕ, 0 < n → n < 15 → SpectralSetOrder K n

def twoClosedDisks (a b : ℂ) (r s : ℝ) : Set ℂ :=
  Metric.closedBall a r ∪ Metric.closedBall b s

def twoOpenDisks (a b : ℂ) (r s : ℝ) : Set ℂ :=
  Metric.ball a r ∪ Metric.ball b s

theorem twoClosedDisks_nonempty (a b : ℂ) (r s : ℝ) (hr : 0 ≤ r) :
    (twoClosedDisks a b r s).Nonempty :=
  ⟨a, Or.inl (Metric.mem_closedBall_self hr)⟩

theorem twoClosedDisks_bounded (a b : ℂ) (r s : ℝ) :
    ∃ B : ℝ, ∀ z ∈ twoClosedDisks a b r s, ‖z‖ ≤ B := by
  refine ⟨max (‖a‖ + r) (‖b‖ + s), ?_⟩
  intro z hz
  rcases hz with hz | hz
  · exact (norm_le_of_mem_closedBall hz).trans (le_max_left _ _)
  · exact (norm_le_of_mem_closedBall hz).trans (le_max_right _ _)

/-- No geometric arrangement of two nonempty closed disks repairs the order-two claim. -/
theorem twoClosedDisks_not_spectralSetOrder_two (a b : ℂ) (r s : ℝ)
    (hr : 0 ≤ r) : ¬ SpectralSetOrder (twoClosedDisks a b r s) 2 :=
  boundedSet_not_spectralSetOrder_two _ (twoClosedDisks_nonempty a b r s hr)
    (twoClosedDisks_bounded a b r s)

/-- The same conclusion holds if "disk" is read as an open disk. -/
theorem twoOpenDisks_not_spectralSetOrder_two (a b : ℂ) (r s : ℝ)
    (hr : 0 < r) : ¬ SpectralSetOrder (twoOpenDisks a b r s) 2 := by
  apply boundedSet_not_spectralSetOrder_two
  · exact ⟨a, Or.inl (Metric.mem_ball_self hr)⟩
  · obtain ⟨B, hB⟩ := twoClosedDisks_bounded a b r s
    refine ⟨B, fun z hz => hB z ?_⟩
    rcases hz with hz | hz
    · exact Or.inl (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz).le)
    · exact Or.inr (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz).le)

/-- This negates a necessary, explicitly stated clause of the original conjecture. -/
theorem conjecture973_disproof_closed (a b : ℂ) (r s : ℝ) (hr : 0 ≤ r) :
    ¬ SmallOrderClaim (twoClosedDisks a b r s) := by
  intro h
  exact twoClosedDisks_not_spectralSetOrder_two a b r s hr (h 2 (by norm_num) (by norm_num))

theorem conjecture973_disproof_open (a b : ℂ) (r s : ℝ) (hr : 0 < r) :
    ¬ SmallOrderClaim (twoOpenDisks a b r s) := by
  intro h
  exact twoOpenDisks_not_spectralSetOrder_two a b r s hr (h 2 (by norm_num) (by norm_num))

end Conjecture973
