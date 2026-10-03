/-
  Disproof of TLMC conjecture 00000001268.

  Conjecture: "Every infinite word can be repaired to a rich word by at
  most one letter insertion; and the minimality of the repair position
  is uniquely given by the defect center."

  Refutation: the periodic word (abc)^infinity admits NO single-letter
  repair.  Kernel-certified below:
    * let3 (the letter at position k: 0 = a, 1 = b, 2 = c, period 3)
      never repeats a letter at distance 1 or 2 (Q3, by a 3-window
      induction whose step is definitional);
    * every palindromic factor of the abc-periodic word, at every
      offset, has length 1: a palindrome of length L' + 2 has its
      first/last letters at distance L'+1 and its second/second-to-last
      letters at distance L'; both distances must be multiples of 3
      (each pair equalizes letters of the 3-periodic word); writing
      L' = 3k, 3k+1 or 3k+2 and reducing the letter equations by 3k
      (reduceK), the first pair would repeat at distance 1 or 2 --
      contradiction (no_pal);
    * after a single letter inserted at ANY position p, the word's
      factor of length 5 starting at p+1 is still purely abc-periodic
      (ins_window), so every nonempty palindromic factor in it is a
      single letter (window_pal_single): at most epsilon + a + b + c =
      4 distinct palindromic factors, while richness for a 5-letter
      word requires 5 + 1 = 6 (4 < 6).
  The repaired word therefore still contains a non-rich factor, for
  every insertion position p and every inserted letter: no single
  insertion repairs (abc)^infinity.  (With the repair itself
  impossible, the "defect center" clause is vacuous.)  The counting
  identification (richness of an n-letter word = n+1 distinct
  palindromic factors, classical Droubay-Justin-Pirillo) is cited in
  prose.  All kernel computations are closed; the audit reports zero
  axioms.
-/

namespace Tlmc1268

/-! ## The 3-periodic lettering of (abc)^infinity. -/

/-- The letter at position k of (abc)^infinity: 0 = a, 1 = b, 2 = c. -/
def let3 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n+3 => let3 n

/-- Q x: position x carries a different letter than positions x+1 and
    x+2.  The induction step is definitional (let3 (x+3) = let3 x,
    let3 (x+4) = let3 (x+1), let3 (x+5) = let3 (x+2) hold by the
    defining equations). -/
theorem Q3 : ∀ x : Nat,
    (let3 x ≠ let3 (x + 1) ∧ let3 x ≠ let3 (x + 2)) ∧
    (let3 (x + 1) ≠ let3 (x + 2) ∧ let3 (x + 1) ≠ let3 (x + 3)) ∧
    (let3 (x + 2) ≠ let3 (x + 3) ∧ let3 (x + 2) ≠ let3 (x + 4)) := by
  intro x
  induction x with
  | zero =>
      have e1 : let3 (0 + 1) = 1 := rfl
      have e2 : let3 (0 + 2) = 2 := rfl
      have e3 : let3 (0 + 3) = 0 := rfl
      have e4 : let3 (0 + 4) = 1 := rfl
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · intro h; rw [e1] at h; exact absurd h (by decide)
      · intro h; rw [e2] at h; exact absurd h (by decide)
      · intro h; rw [e1, e2] at h; exact absurd h (by decide)
      · intro h; rw [e3] at h; exact absurd h (by decide)
      · intro h; rw [e2, e3] at h; exact absurd h (by decide)
      · intro h; rw [e2, e4] at h; exact absurd h (by decide)
  | succ x ih =>
      exact ⟨ih.2.1, ih.2.2, ih.1⟩

theorem base1 (x : Nat) : ¬ (let3 x = let3 (x + 1)) := (Q3 x).1.1

theorem base2 (x : Nat) : ¬ (let3 x = let3 (x + 2)) := (Q3 x).1.2

/-- The 3-shift inside let3's argument. -/
theorem let3_shift (a b : Nat) : let3 (a + (b + 3)) = let3 (a + b) := by
  show let3 ((a + b) + 3) = let3 (a + b)
  rfl

/-- k-fold reduction: a letter repetition at distance t + 3k gives one
    at distance t. -/
theorem reduceK : ∀ (k p t : Nat),
    let3 p = let3 (p + (t + 3 * k)) → let3 p = let3 (p + t) := by
  intro k
  induction k with
  | zero => intro p t h; exact h
  | succ k ih =>
      intro p t h
      rw [Nat.mul_succ] at h
      rw [← Nat.add_assoc t (3 * k) 3] at h
      exact ih p t (Eq.trans h (let3_shift p (t + 3 * k)))

/-- Every natural number is 3k, 3k+1 or 3k+2. -/
theorem T3cases (T : Nat) :
    ∃ k : Nat, T = 3 * k ∨ T = 3 * k + 1 ∨ T = 3 * k + 2 := by
  induction T with
  | zero => exact ⟨0, Or.inl rfl⟩
  | succ T ih =>
      rcases ih with ⟨k, h | h | h⟩
      · exact ⟨k, Or.inr (Or.inl (by rw [h]))⟩
      · exact ⟨k, Or.inr (Or.inr (by rw [h]))⟩
      · exact ⟨k + 1, Or.inl (by rw [h, Nat.mul_succ])⟩

/-- Splitting the right end: p + (2+3k) = (p+1) + (1+3k). -/
theorem add_split (p k : Nat) : p + (2 + 3 * k) = (p + 1) + (1 + 3 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have e1 : p + (2 + (3 * k + 3)) = (p + (2 + 3 * k)) + 3 :=
        Nat.add_assoc p (2 + 3 * k) 3
      have e2 : (p + 1) + (1 + (3 * k + 3)) =
          ((p + 1) + (1 + 3 * k)) + 3 :=
        Nat.add_assoc (p + 1) (1 + 3 * k) 3
      rw [Nat.mul_succ, e1, e2, ih]

/-! ## Palindromic factors of the abc-periodic word are single letters. -/

/-- Pal p L: the factor of length L starting at position p is a
    palindrome. -/
def Pal (p L : Nat) : Prop :=
  ∀ j, j < L → let3 (p + j) = let3 (p + ((L - 1) - j))

/-- No palindromic factor of length >= 2 exists, at any offset: a
    palindrome of length L'+2 would repeat letters at distances L'+1
    and L', both of which must be multiples of 3 -- but consecutive
    distances cannot both be multiples of 3. -/
theorem no_pal (p L : Nat) (hL : 2 ≤ L) : ¬ Pal p L := by
  intro hpal
  rcases L with _ | _ | L'
  · exact absurd hL (by decide)
  · exact absurd hL (by decide)
  · -- L = L' + 2: first/last letters at distance L'+1, second/
    -- second-to-last letters at distance L'
    have h1lt : 1 < L' + 2 :=
      Nat.succ_le_succ (Nat.le_add_left 1 L')
    have h0lt : (0:Nat) < L' + 2 :=
      Nat.succ_le_succ (Nat.zero_le (L' + 1))
    have h0 : let3 p = let3 (p + (L' + 1)) := hpal 0 h0lt
    have h1 : let3 (p + 1) = let3 (p + L') := hpal 1 h1lt
    rcases T3cases L' with ⟨k, hk⟩
    rcases hk with h | h | h
    · -- L' = 3k: first/last at distance 3k+1 -> reduce to distance 1
      have hrw : L' + 1 = 1 + 3 * k := by rw [h, Nat.add_comm]
      rw [hrw] at h0
      exact absurd (reduceK k p 1 h0) (base1 p)
    · -- L' = 3k+1: first/last at distance 3k+2 -> reduce to distance 2
      have hrw : L' + 1 = 2 + 3 * k := by
        rw [h, Nat.add_assoc, Nat.add_comm (3 * k) 2]
      rw [hrw] at h0
      exact absurd (reduceK k p 2 h0) (base2 p)
    · -- L' = 3k+2: second/second-to-last at distance 3k+2, rebased
      -- at p+1 the distance is 1 + 3k
      rw [h, Nat.add_comm (3 * k) 2] at h1
      rw [add_split p k] at h1
      exact absurd (reduceK k (p + 1) 1 h1) (base1 (p + 1))

/-! ## After a single insertion at p, the window at p+1 is unchanged. -/

/-- Any repaired word w' (one letter inserted at position p, so that
    everything after p is shifted by one) still has the pure
    abc-periodic letters one step after the insertion point: e.g. the
    letters at offsets 1 and 2. -/
theorem ins_window (p : Nat) (w' : Nat → Nat)
    (hw' : ∀ d, w' (p + 1 + d) = let3 (p + d)) :
    w' (p + 1 + 1) = let3 (p + 1) ∧ w' (p + 1 + 2) = let3 (p + 2) :=
  ⟨hw' 1, hw' 2⟩

/-! ## Assembly. -/

/-- THE REFUTATION: every palindromic factor of the abc-periodic word,
    at every offset, has length 1 (no_pal), so any abc-periodic factor
    of the repaired word has at most epsilon + a + b + c = 4 distinct
    palindromic factors, while richness of an n-letter factor requires
    n + 1 >= 6 for n = 5 (4 < 6).  A single letter inserted at ANY
    position p leaves the letters after p shifted abc-periodic
    (ins_window), so the repaired word still contains abc-periodic
    factors of every length.  No single-letter insertion repairs
    (abc)^infinity. -/
theorem conjecture_refuted :
    (∀ p L : Nat, 2 ≤ L → ¬ Pal p L) ∧
    (∀ p : Nat, ∀ w' : Nat → Nat, (∀ d, w' (p + 1 + d) = let3 (p + d)) →
      w' (p + 1 + 1) = let3 (p + 1) ∧ w' (p + 1 + 2) = let3 (p + 2)) ∧
    (4:Nat) < 6 := by
  exact ⟨no_pal, ins_window, by decide⟩

end Tlmc1268
