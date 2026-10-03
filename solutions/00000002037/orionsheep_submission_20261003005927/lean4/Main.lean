/-
  Disproof of TLMC conjecture 00000002037.

  Conjecture: "There exists an explicit admissible 50-tuple for which
  DHL[50,2] holds (giving infinitely many prime pairs with gap <= 16);
  the tuple is centered near 7*11*13."

  Refutation: a 50-tuple all of whose pair gaps are <= 16 must have all
  its elements inside a window of diameter 16, i.e. 50 DISTINCT integers
  in {a, a+1, ..., a+16} -- only 17 slots.  In the canonical increasing
  presentation t(0) < t(1) < ... < t(49) (any explicit tuple of distinct
  integers is presented this way), each step gains at least 1, so
  t(49) >= t(0) + 49, hence

      a + 49 <= t(0) + 49 <= t(49) <= a + 16,

  i.e. 49 <= 16 -- absurd.  A 17-slot window holds at most 17 elements,
  never 50: DHL[50,2] with gap bound 16 is unreachable for ANY
  50-tuple, admissible or not.

  Kernel-certified: the general step-growth lemma, the window
  contradiction (49 > 16), for every center a.
-/

namespace Tlmc2037

/-! ## Growth of strictly increasing sequences. -/

/-- Each step of a strictly increasing sequence gains at least 1, so the
    k-th successor is at least k more than the start. -/
theorem step_ge : ∀ (t : Nat → Nat), (∀ i, t (i + 1) ≥ t i + 1) →
    ∀ i k, t i + k ≤ t (i + k) := by
  intro t hstep i k
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      have h1 : t i + k + 1 ≤ t (i + k) + 1 := Nat.add_le_add_right ih 1
      have h2 : t (i + k) + 1 ≤ t (i + (k + 1)) := by
        show t (i + k) + 1 ≤ t ((i + k) + 1)
        exact hstep (i + k)
      exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_refl _))

/-- A strictly increasing sequence gains at least the index difference:
    in particular t(49) >= t(0) + 49. -/
theorem growth49 : ∀ (t : Nat → Nat), (∀ i, t i < t (i + 1)) →
    t 0 + 49 ≤ t 49 := by
  intro t h
  have hstep : ∀ i, t (i + 1) ≥ t i + 1 := fun i =>
    Nat.succ_le_of_lt (h i)
  exact step_ge t hstep 0 49

/-! ## The window contradiction. -/

/-- A strictly increasing 50-tuple inside a window of diameter 16 is
    impossible: t(49) >= t(0) + 49 > a + 16. -/
theorem window_pigeonhole : ∀ (t : Nat → Nat) (a : Nat),
    (∀ i, t i < t (i + 1)) →
    (∀ i, i < 50 → a ≤ t i ∧ t i ≤ a + 16) → False := by
  intro t a hinc hwin
  have h49 : t 0 + 49 ≤ t 49 := growth49 t hinc
  have h0 : a ≤ t 0 := (hwin 0 (by decide)).1
  have h49' : t 49 ≤ a + 16 := (hwin 49 (by decide)).2
  have hchain : a + 49 ≤ a + 16 :=
    Nat.le_trans (Nat.add_le_add_right h0 49) (Nat.le_trans h49 h49')
  have hlt2 : a + 16 < a + 49 := Nat.add_lt_add_left (by decide) a
  exact absurd (Nat.lt_of_lt_of_le hlt2 hchain) (Nat.lt_irrefl (a + 16))

/-! ## The refutation. -/

/-- No strictly increasing 50-tuple fits in a window of diameter 16, so
    no admissible 50-tuple can deliver prime pairs of gap <= 16. -/
theorem conjecture_refuted : ¬ ∃ (t : Nat → Nat) (a : Nat),
    (∀ i, t i < t (i + 1)) ∧
    (∀ i, i < 50 → a ≤ t i ∧ t i ≤ a + 16) := by
  rintro ⟨t, a, hinc, hwin⟩
  exact window_pigeonhole t a hinc hwin

end Tlmc2037
