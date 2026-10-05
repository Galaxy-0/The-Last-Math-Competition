import Mathlib

/-!
# Conjecture 00000008185 is false

Hardy–Littlewood's `G(k)` is the least positive integer `s` such that every sufficiently large
integer is a sum of at most `s` positive `k`-th powers. The conjecture's last clause says that the
"high-dimensional generalization `G(k) = k`" of `G(4) = 16` first holds at a threshold `k ≥ 7`.

We prove the classical lower bound behind its failure from scratch: for every `k ≥ 2` and every
`M` there is `n ≥ M` that is not a sum of at most `k` positive `k`-th powers (a counting argument:
there are only `C(t + k, k)` multisets of `k` bases in `{0, …, t}`, fewer than `t ^ k - M`). Hence
`k` powers never suffice, `G(k) ≠ k` for every `k ≥ 2` (and `G(k) ≥ k + 1` whenever `G(k)` is
attained), while `G(1) = 1`.
-/

open Finset

namespace C8185

/-- `n` is a sum of at most `s` positive `k`-th powers. -/
def IsSumAtMost (k s n : ℕ) : Prop :=
  ∃ l : List ℕ, l.length ≤ s ∧ (∀ a ∈ l, 0 < a) ∧ (l.map (· ^ k)).sum = n

/-- Every sufficiently large integer is a sum of at most `s` positive `k`-th powers. -/
def Suffices (k s : ℕ) : Prop := ∃ N, ∀ n ≥ N, IsSumAtMost k s n

/-- Hardy–Littlewood's `G(k)`: the least `s` that suffices for all sufficiently large integers
(`sInf ∅ = 0` is Lean's junk value; it is never needed below). -/
noncomputable def waringG (k : ℕ) : ℕ := sInf {s | Suffices k s}

/-- The base `a mod (t + 1)` as an element of `Fin (t + 1)` (only used for `a ≤ t`). -/
def toFin (t a : ℕ) : Fin (t + 1) := ⟨a % (t + 1), Nat.mod_lt _ t.succ_pos⟩

/-- Sum of `k`-th powers of a multiset of `k` bases in `{0, …, t}`. -/
def powSum (k t : ℕ) (m : Sym (Fin (t + 1)) k) : ℕ :=
  (Multiset.map (fun b : Fin (t + 1) => (b : ℕ) ^ k) m.1).sum

/-- A sum of at most `k` positive `k`-th powers that is `≤ t ^ k` is `powSum k t m` for some
multiset `m` of `k` bases in `{0, …, t}` (pad with zeros). -/
lemma mem_image_powSum {k t n : ℕ} (hk : k ≠ 0) (h : IsSumAtMost k k n) (hn : n ≤ t ^ k) :
    n ∈ (univ : Finset (Sym (Fin (t + 1)) k)).image (powSum k t) := by
  obtain ⟨l, hlen, -, hsum⟩ := h
  set l' := l ++ List.replicate (k - l.length) 0 with hl'
  have hle : ∀ a ∈ l', a ≤ t := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · have h1 : a ^ k ≤ n := hsum ▸ List.le_sum_of_mem (List.mem_map_of_mem ha)
      exact (Nat.pow_le_pow_iff_left hk).1 (h1.trans hn)
    · rw [List.eq_of_mem_replicate ha]; exact Nat.zero_le _
  let m : Sym (Fin (t + 1)) k :=
    ⟨((l'.map (toFin t) : List (Fin (t + 1))) : Multiset (Fin (t + 1))), by
      simp [l']; omega⟩
  refine mem_image.2 ⟨m, mem_univ _, ?_⟩
  show (Multiset.map (fun b : Fin (t + 1) => (b : ℕ) ^ k) ((l'.map (toFin t) : List _) : Multiset _)).sum = n
  rw [Multiset.map_coe, Multiset.sum_coe, List.map_map]
  have hc : ∀ a ∈ l', ((fun b : Fin (t + 1) => (b : ℕ) ^ k) ∘ toFin t) a = a ^ k := by
    intro a ha
    simp [toFin, Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hle a ha))]
  rw [List.map_congr_left hc, hl', List.map_append, List.sum_append, hsum]
  simp [zero_pow hk]

/-- `4 ^ k + 1 ≤ 3 ^ k * k!` for `k ≥ 2`. -/
lemma four_pow_lt (k : ℕ) (hk : 2 ≤ k) : 4 ^ k + 1 ≤ 3 ^ k * k.factorial := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ, pow_succ, Nat.factorial_succ]
    have : 4 ≤ 3 * (k + 1) := by omega
    nlinarith [Nat.zero_le (3 ^ k * k.factorial)]

/-- The counting inequality `C(t + k, k) + M ≤ t ^ k` for `t = 3k + 4^k M`, `k ≥ 2`. -/
lemma choose_add_le (k M : ℕ) (hk : 2 ≤ k) :
    (3 * k + 4 ^ k * M + k).choose k + M ≤ (3 * k + 4 ^ k * M) ^ k := by
  set t := 3 * k + 4 ^ k * M
  set C := (t + k).choose k
  -- `k! * C ≤ (t + k) ^ k`
  have h1 : k.factorial * C ≤ (t + k) ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.descFactorial_le_pow _ _
  -- `3^k (t + k)^k ≤ 4^k t^k`
  have h2 : 3 ^ k * (t + k) ^ k ≤ 4 ^ k * t ^ k := by
    rw [← mul_pow, ← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  -- `t + 1 ≤ C`
  have h3 : t + 1 ≤ C := by
    have : (t + 1).choose t ≤ (t + k).choose t := Nat.choose_le_choose t (by omega)
    rw [Nat.choose_succ_self_right] at this
    simpa [C, Nat.choose_symm_add] using this
  have h4 := four_pow_lt k hk
  have h5 : 4 ^ k * M ≤ t := by omega
  have hpos : 0 < 4 ^ k := by positivity
  -- `(4^k + 1) C ≤ 4^k t^k`
  have h6 : (4 ^ k + 1) * C ≤ 4 ^ k * t ^ k :=
    calc (4 ^ k + 1) * C ≤ 3 ^ k * k.factorial * C := Nat.mul_le_mul_right _ h4
      _ = 3 ^ k * (k.factorial * C) := by ring
      _ ≤ 3 ^ k * (t + k) ^ k := Nat.mul_le_mul_left _ h1
      _ ≤ 4 ^ k * t ^ k := h2
  have h7 : 4 ^ k * (C + M) ≤ 4 ^ k * t ^ k := by nlinarith
  exact Nat.le_of_mul_le_mul_left h7 hpos

/-- **Key lemma.** For `k ≥ 2`, there are arbitrarily large integers that are not sums of at
most `k` positive `k`-th powers. -/
theorem exists_not_sum (k : ℕ) (hk : 2 ≤ k) (M : ℕ) : ∃ n ≥ M, ¬ IsSumAtMost k k n := by
  set t := 3 * k + 4 ^ k * M
  have hc : (t + k).choose k + M ≤ t ^ k := choose_add_le k M hk
  by_contra hcon
  push Not at hcon
  have hsub : Icc M (t ^ k) ⊆ (univ : Finset (Sym (Fin (t + 1)) k)).image (powSum k t) :=
    fun n hn => mem_image_powSum (by omega) (hcon n (mem_Icc.1 hn).1) (mem_Icc.1 hn).2
  have hcard := card_le_card hsub
  have himg := card_image_le (s := (univ : Finset (Sym (Fin (t + 1)) k))) (f := powSum k t)
  rw [card_univ, Sym.card_sym_eq_choose, Fintype.card_fin] at himg
  rw [Nat.card_Icc] at hcard
  have : t + 1 + k - 1 = t + k := by omega
  rw [this] at himg
  omega

/-- `k` powers do not suffice for `k ≥ 2`, nor does any `s ≤ k`. -/
theorem not_suffices (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (hs : s ≤ k) : ¬ Suffices k s := by
  rintro ⟨N, hN⟩
  obtain ⟨n, hn, hnot⟩ := exists_not_sum k hk N
  obtain ⟨l, hl, hpos, hsum⟩ := hN n hn
  exact hnot ⟨l, hl.trans hs, hpos, hsum⟩

/-- `G(k) ≠ k` for every `k ≥ 2`. -/
theorem waringG_ne (k : ℕ) (hk : 2 ≤ k) : waringG k ≠ k := by
  intro h
  have hne : {s | Suffices k s}.Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty] at he
    simp only [waringG, he, Nat.sInf_empty] at h
    omega
  have := Nat.sInf_mem hne
  rw [show sInf {s | Suffices k s} = k from h] at this
  exact not_suffices k hk k le_rfl this

/-- `G(k) ≥ k + 1` for `k ≥ 2` whenever some number of powers suffices (Hilbert–Waring). -/
theorem waringG_ge (k : ℕ) (hk : 2 ≤ k) (hne : ∃ s, Suffices k s) : k + 1 ≤ waringG k := by
  by_contra h
  push Not at h
  exact not_suffices k hk _ (by unfold waringG at h; omega) (Nat.sInf_mem (s := {s | Suffices k s}) hne)

/-- `G(1) = 1`. -/
theorem waringG_one : waringG 1 = 1 := by
  have h1 : Suffices 1 1 := ⟨1, fun n hn => ⟨[n], by simp, by simp; omega, by simp⟩⟩
  have h0 : ¬ Suffices 1 0 := by
    rintro ⟨N, hN⟩
    obtain ⟨l, hl, -, hsum⟩ := hN (N + 1) (by omega)
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)] at hsum
    simp at hsum
  apply le_antisymm (Nat.sInf_le h1)
  rw [Nat.one_le_iff_ne_zero]
  intro h
  rcases Nat.sInf_eq_zero.1 h with h | h
  · exact h0 h
  · exact (Set.eq_empty_iff_forall_notMem.1 h) 1 h1

/-- **Conjecture 00000008185 is false** (its "seventh-power threshold" clause). For every
`k ≥ 2`, `G(k) ≠ k` (indeed `k` positive `k`-th powers never suffice for all large integers),
while `G(1) = 1`. Consequently each of the following readings of "`G(k) = k` first holds at a
threshold `k ≥ 7`" is false: `G(7) = 7`; `G(k) = k` for all `k ≥ 7`; `G(k) = k` for all `k` beyond
some threshold `K ≥ 7`; the least `k ≥ 2` with `G(k) = k` exists and is `≥ 7`; and the least
`k ≥ 1` with `G(k) = k` is `≥ 7`. -/
theorem conjecture_8185_false :
    (∀ k, 2 ≤ k → ∀ N, ∃ n ≥ N, ¬ IsSumAtMost k k n) ∧
    (∀ k, 2 ≤ k → waringG k ≠ k) ∧ waringG 1 = 1 ∧
    waringG 7 ≠ 7 ∧
    ¬ (∀ k, 7 ≤ k → waringG k = k) ∧
    ¬ (∃ K, 7 ≤ K ∧ ∀ k, K ≤ k → waringG k = k) ∧
    ¬ (∃ k, 2 ≤ k ∧ waringG k = k) ∧
    ¬ (∃ k₀, 7 ≤ k₀ ∧ waringG k₀ = k₀ ∧ ∀ k, 1 ≤ k → waringG k = k → k₀ ≤ k) := by
  refine ⟨exists_not_sum, waringG_ne, waringG_one, waringG_ne 7 (by norm_num),
    fun h => waringG_ne 7 (by norm_num) (h 7 le_rfl),
    fun ⟨K, _, h⟩ => waringG_ne K (by omega) (h K le_rfl),
    fun ⟨k, hk, h⟩ => waringG_ne k hk h,
    fun ⟨k₀, h7, _, hmin⟩ => ?_⟩
  have := hmin 1 le_rfl waringG_one
  omega

end C8185
