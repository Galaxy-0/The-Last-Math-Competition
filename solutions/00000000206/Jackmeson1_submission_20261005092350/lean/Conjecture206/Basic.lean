import Mathlib

/-!
# Conjecture 00000000206: every value occurs only finitely often in Recamán's sequence

Recamán's sequence (OEIS A005132) is `a 0 = 0` and, for `n ≥ 1`,
`a n = a (n-1) - n` if that number is positive (Wikipedia) / nonnegative (OEIS) and is not
among `a 0, …, a (n-1)`; otherwise `a n = a (n-1) + n`.
(The two guards give the same sequence, because `0 = a 0` is always already present.)

We prove: for every `m : ℕ`, the set `{n | a n = m}` is finite, for every sequence satisfying
either form of the recurrence, and we construct the sequence and show it is unique.

The proof: an add step gives `a n = a (n-1) + n ≥ n`, so an occurrence of `m` at an index
`n > m` must come from a subtract step, which by the rule produces a value not seen before;
hence there is at most one occurrence of `m` beyond index `m`.
-/

namespace Conjecture206

/-- `a` satisfies the Recamán recurrence in Wikipedia's form (guard: `a (n-1) - n > 0`).
Stated at index `n + 1`; "not already in the sequence" means not among `a 0, …, a n`. -/
def IsRecaman (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ ∀ n, a (n + 1) =
    if n + 1 < a n ∧ ∀ k ≤ n, a k ≠ a n - (n + 1) then a n - (n + 1) else a n + (n + 1)

/-- `a` satisfies the Recamán recurrence in OEIS A005132's form (guard: `a (n-1) - n ≥ 0`). -/
def IsRecamanOEIS (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ ∀ n, a (n + 1) =
    if n + 1 ≤ a n ∧ ∀ k ≤ n, a k ≠ a n - (n + 1) then a n - (n + 1) else a n + (n + 1)

/-- Core lemma: if every step is either `a (n+1) = a n + (n+1)` or produces a value not among
`a 0, …, a n`, then every value is taken only finitely often. -/
theorem finite_of_step (a : ℕ → ℕ)
    (h : ∀ n, a (n + 1) = a n + (n + 1) ∨ ∀ k ≤ n, a k ≠ a (n + 1)) (m : ℕ) :
    {n | a n = m}.Finite := by
  -- an occurrence of `m` at an index `n > m` is the first occurrence of `m`
  have key : ∀ n, m < n → a n = m → ∀ k < n, a k ≠ m := by
    intro n hn ha
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    rcases h p with h1 | h1
    · omega
    · intro k hk
      rw [← ha]
      exact h1 k (by omega)
  by_cases hex : ∃ N, m < N ∧ a N = m
  · obtain ⟨N, hN, haN⟩ := hex
    refine (Set.finite_Iic N).subset fun n hn => ?_
    simp only [Set.mem_ofPred_eq] at hn
    simp only [Set.mem_Iic]
    by_contra hlt
    exact key n (by omega) hn N (by omega) haN
  · push Not at hex
    refine (Set.finite_Iic m).subset fun n hn => ?_
    simp only [Set.mem_ofPred_eq] at hn
    simp only [Set.mem_Iic]
    by_contra hlt
    exact hex n (by omega) hn

/-- Wikipedia form: every value occurs only finitely often. -/
theorem finite_occurrences_of_isRecaman {a : ℕ → ℕ} (ha : IsRecaman a) (m : ℕ) :
    {n | a n = m}.Finite := by
  refine finite_of_step a (fun n => ?_) m
  rw [ha.2 n]
  split_ifs with hc
  · exact Or.inr hc.2
  · exact Or.inl rfl

/-- OEIS form: every value occurs only finitely often. -/
theorem finite_occurrences_of_isRecamanOEIS {a : ℕ → ℕ} (ha : IsRecamanOEIS a) (m : ℕ) :
    {n | a n = m}.Finite := by
  refine finite_of_step a (fun n => ?_) m
  rw [ha.2 n]
  split_ifs with hc
  · exact Or.inr hc.2
  · exact Or.inl rfl

/-! ## Construction and uniqueness of the sequence -/

/-- `recList n = [a n, a (n-1), …, a 0]`. -/
def recList : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
    if n + 1 < (recList n).headI ∧ (recList n).headI - (n + 1) ∉ recList n then
      ((recList n).headI - (n + 1)) :: recList n
    else ((recList n).headI + (n + 1)) :: recList n

/-- Recamán's sequence. -/
def recaman (n : ℕ) : ℕ := (recList n).headI

theorem recList_succ (n : ℕ) : recList (n + 1) = recaman (n + 1) :: recList n := by
  unfold recaman
  rw [recList]
  split_ifs <;> rfl

theorem mem_recList (n v : ℕ) : v ∈ recList n ↔ ∃ k ≤ n, recaman k = v := by
  induction n with
  | zero =>
    simp only [recList, List.mem_singleton, Nat.le_zero, exists_eq_left, recaman, List.headI]
    exact eq_comm
  | succ n ih =>
    rw [recList_succ, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨n + 1, le_rfl, h.symm⟩
      · exact ⟨k, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
      · exact Or.inr ⟨k, by omega, h⟩
      · left; rw [← h, show k = n + 1 by omega]

/-- The constructed sequence satisfies the recurrence (Wikipedia form). -/
theorem isRecaman_recaman : IsRecaman recaman := by
  refine ⟨rfl, fun n => ?_⟩
  have hnot : (recaman n - (n + 1) ∉ recList n) ↔ ∀ k ≤ n, recaman k ≠ recaman n - (n + 1) := by
    rw [mem_recList]; push Not; rfl
  show (recList (n + 1)).headI = _
  rw [recList]
  simp only [← hnot]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

/-- The recurrence determines the sequence uniquely. -/
theorem isRecaman_unique {a b : ℕ → ℕ} (ha : IsRecaman a) (hb : IsRecaman b) : a = b := by
  have h : ∀ n, ∀ k ≤ n, a k = b k := by
    intro n
    induction n with
    | zero => intro k hk; rw [Nat.le_zero.1 hk, ha.1, hb.1]
    | succ n ih =>
      intro k hk
      rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
      · exact ih k (by omega)
      · rw [show k = n + 1 by omega, ha.2 n, hb.2 n, ih n le_rfl]
        have hc : (∀ k ≤ n, a k ≠ b n - (n + 1)) ↔ (∀ k ≤ n, b k ≠ b n - (n + 1)) :=
          forall₂_congr fun k hk => by rw [ih k hk]
        simp only [hc]
  funext n
  exact h n n le_rfl

/-- The two guards (`> 0` and `≥ 0`) define the same sequence. -/
theorem isRecamanOEIS_recaman : IsRecamanOEIS recaman := by
  refine ⟨rfl, fun n => ?_⟩
  rw [isRecaman_recaman.2 n]
  by_cases he : recaman n = n + 1
  · -- the value `0 = recaman 0` is already present, so both guards fail
    have h0 : ¬ ∀ k ≤ n, recaman k ≠ recaman n - (n + 1) := fun h =>
      h 0 (Nat.zero_le _) (by rw [he, Nat.sub_self]; rfl)
    simp [h0]
  · have : (n + 1 < recaman n) ↔ (n + 1 ≤ recaman n) := by omega
    simp only [this]

/-- Sanity check against Wikipedia's listed initial terms; note `a 20 = a 24 = 42`, so values
can repeat. -/
example : (List.range 27).map recaman =
    [0, 1, 3, 6, 2, 7, 13, 20, 12, 21, 11, 22, 10, 23, 9, 24, 8, 25, 43, 62, 42, 63, 41, 18, 42,
      17, 43] := by decide

/-- **Main theorem.** Every nonnegative integer occurs only finitely often in Recamán's
sequence. -/
theorem recaman_finite_occurrences (m : ℕ) : {n | recaman n = m}.Finite :=
  finite_occurrences_of_isRecaman isRecaman_recaman m

end Conjecture206
