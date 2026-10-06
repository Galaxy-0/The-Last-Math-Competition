import Mathlib

/-!
# Conjecture 00000000211: the lucky primes contain no twin pair

The conjecture asserts (among other things) that the intersection of the lucky numbers
(OEIS A000959) with the primes contains infinitely many twin pairs.

We define the lucky sieve stage by stage, starting from the positive integers
`1, 2, 3, ...`.  Stage `k` is an increasing enumeration `stage k : ℕ → ℕ` (0-indexed) of
the numbers surviving the first `k` rounds.  Round `k + 1` deletes every `m`-th survivor
(1-indexed positions `m, 2m, 3m, ...`) of stage `k`, where the sieving number is
`m = stage k (max 1 k)`, i.e. `m = 2, 3, 7, 9, 13, ...` (the 2nd number of `1, 2, 3, ...`,
then the 2nd, 3rd, 4th, ... survivor).  A number is lucky iff it survives every round.

After the first two rounds only numbers `≡ 1, 3 (mod 6)` survive, and later rounds only
delete numbers.  Hence two lucky primes never differ by `2`: the set of twin pairs in the
intersection is empty, so it is not infinite, and the conjunction in the conjecture fails
whatever the density clause means.
-/

namespace Conjecture211

/-! ## One round of the sieve -/

/-- One sieve round.  `L` enumerates the current survivors in increasing order (0-indexed);
the round deletes the survivors at 1-indexed positions `m, 2m, 3m, ...`.  The `j`-th
remaining survivor (0-indexed) sits at 0-indexed position `j + j / (m - 1)` of `L`. -/
def deleteEvery (m : ℕ) (L : ℕ → ℕ) : ℕ → ℕ := fun j => L (j + j / (m - 1))

/-- `deleteEvery m L` enumerates exactly the entries of `L` whose 1-indexed position is not a
multiple of `m` (for `m ≥ 2`). -/
theorem range_deleteEvery (m : ℕ) (hm : 2 ≤ m) (L : ℕ → ℕ) :
    Set.range (deleteEvery m L) = L '' {i | (i + 1) % m ≠ 0} := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
  have hd : 1 ≤ d := by omega
  have hd' : d + 1 - 1 = d := by omega
  ext x
  simp only [Set.mem_range, deleteEvery, hd', Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨j + j / d, ?_, rfl⟩
    have h1 := Nat.div_add_mod j d
    have h2 := Nat.mod_lt j (show 0 < d by omega)
    have h3 : j + j / d + 1 = (d + 1) * (j / d) + (j % d + 1) := by
      nlinarith
    rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  · rintro ⟨i, hi, rfl⟩
    have h1 := Nat.div_add_mod i (d + 1)
    have h2 := Nat.mod_lt i (show 0 < d + 1 by omega)
    have h3 : i % (d + 1) ≠ d := by
      intro h
      apply hi
      have : i + 1 = (d + 1) * (i / (d + 1) + 1) := by nlinarith
      rw [this, Nat.mul_mod_right]
    have h4 : i % (d + 1) < d := by omega
    refine ⟨d * (i / (d + 1)) + i % (d + 1), ?_⟩
    have h5 : (d * (i / (d + 1)) + i % (d + 1)) / d = i / (d + 1) := by
      rw [add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h4, zero_add]
    rw [h5]
    congr 1
    nlinarith

theorem deleteEvery_strictMono (m : ℕ) {L : ℕ → ℕ} (hL : StrictMono L) :
    StrictMono (deleteEvery m L) := by
  intro a b hab
  apply hL
  have := Nat.div_le_div_right (c := m - 1) hab.le
  omega

/-! ## The lucky sieve -/

/-- `stage k` enumerates (increasingly, 0-indexed) the survivors after `k` rounds.
`stage 0` is the list of positive integers; round `k + 1` deletes every
`stage k (max 1 k)`-th survivor. -/
def stage : ℕ → ℕ → ℕ
  | 0 => fun i => i + 1
  | k + 1 => deleteEvery (stage k (max 1 k)) (stage k)

/-- The sieving number of round `k + 1`. -/
def sievingNumber (k : ℕ) : ℕ := stage k (max 1 k)

theorem stage_succ (k : ℕ) : stage (k + 1) = deleteEvery (sievingNumber k) (stage k) := rfl

/-- A positive integer is lucky iff it survives every round of the sieve. -/
def IsLucky (n : ℕ) : Prop := ∀ k, n ∈ Set.range (stage k)

theorem stage_ge (k i : ℕ) : i + 1 ≤ stage k i := by
  induction k generalizing i with
  | zero => simp [stage]
  | succ k ih =>
    exact le_trans (Nat.succ_le_succ (Nat.le_add_right i _)) (ih _)

theorem stage_strictMono (k : ℕ) : StrictMono (stage k) := by
  induction k with
  | zero => intro a b h; simp [stage]; omega
  | succ k ih => exact deleteEvery_strictMono _ ih

theorem two_le_sievingNumber (k : ℕ) : 2 ≤ sievingNumber k := by
  have := stage_ge k (max 1 k)
  simp only [sievingNumber]
  omega

/-- Each stage really is the previous one with every `m`-th survivor deleted. -/
theorem range_stage_succ (k : ℕ) :
    Set.range (stage (k + 1)) =
      stage k '' {i | (i + 1) % sievingNumber k ≠ 0} :=
  range_deleteEvery _ (two_le_sievingNumber k) _

theorem range_stage_succ_subset (k : ℕ) : Set.range (stage (k + 1)) ⊆ Set.range (stage k) := by
  rintro _ ⟨j, rfl⟩
  exact ⟨_, rfl⟩

theorem range_stage_anti {k l : ℕ} (h : k ≤ l) : Set.range (stage l) ⊆ Set.range (stage k) := by
  induction l, h using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact (range_stage_succ_subset l).trans ih

/-! ## The first two rounds -/

theorem stage_one (j : ℕ) : stage 1 j = 2 * j + 1 := by
  show stage 0 (j + j / (stage 0 (max 1 0) - 1)) = 2 * j + 1
  simp [stage]
  omega

theorem stage_two (j : ℕ) : stage 2 j = 2 * (j + j / 2) + 1 := by
  show stage 1 (j + j / (stage 1 (max 1 1) - 1)) = 2 * (j + j / 2) + 1
  simp only [stage_one]
  norm_num

theorem stage_two_mod_six (j : ℕ) : stage 2 j % 6 = 1 ∨ stage 2 j % 6 = 3 := by
  rw [stage_two]
  omega

/-- Every lucky number is congruent to `1` or `3` modulo `6`. -/
theorem IsLucky.mod_six {n : ℕ} (h : IsLucky n) : n % 6 = 1 ∨ n % 6 = 3 := by
  obtain ⟨j, rfl⟩ := h 2
  exact stage_two_mod_six j

/-! ## Sanity checks: the sieve reproduces OEIS A000959 -/

/-- Entries before the sieving position are never deleted again. -/
theorem stage_succ_of_lt {k j : ℕ} (h : j < k) : stage (k + 1) j = stage k j := by
  rw [stage_succ]
  have := stage_ge k (max 1 k)
  have h0 : j / (sievingNumber k - 1) = 0 :=
    Nat.div_eq_of_lt (by simp only [sievingNumber]; omega)
  simp [deleteEvery, h0]

theorem stage_stable {k l j : ℕ} (hj : j < k) (h : k ≤ l) : stage l j = stage k j := by
  induction l, h using Nat.le_induction with
  | base => rfl
  | succ l hl ih => rw [stage_succ_of_lt (by omega), ih]

/-- The `j`-th lucky number (0-indexed). -/
def lucky (j : ℕ) : ℕ := stage (j + 1) j

/-- The lucky numbers are exactly the values `lucky j`. -/
theorem isLucky_iff (n : ℕ) : IsLucky n ↔ ∃ j, lucky j = n := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h (n + 1)
    have := stage_ge (n + 1) i
    exact ⟨i, by rw [lucky, ← stage_stable (Nat.lt_succ_self i) (by omega : i + 1 ≤ n + 1), hi]⟩
  · rintro ⟨j, rfl⟩ l
    rcases le_total (j + 1) l with h | h
    · exact ⟨j, stage_stable (Nat.lt_succ_self j) h⟩
    · exact range_stage_anti h ⟨j, rfl⟩

theorem lucky_strictMono : StrictMono lucky := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  simp only [lucky]
  rw [← stage_stable (Nat.lt_succ_self j) (Nat.le_succ (j + 1))]
  exact stage_strictMono _ (Nat.lt_succ_self j)

theorem stage_ge_two_mul (k i : ℕ) : 2 * i + 1 ≤ stage (k + 1) i := by
  induction k generalizing i with
  | zero => rw [stage_one]
  | succ k ih => exact le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_add_right i _)) 1) (ih _)

/-- From round 2 on, round `k + 1` deletes every `s`-th survivor, where `s = lucky k` is the
`(k + 1)`-th lucky number counted from 1 (so the sieving numbers are `2, 3, 7, 9, 13, ...`). -/
theorem sievingNumber_eq_lucky {k : ℕ} (hk : 1 ≤ k) : sievingNumber k = lucky k := by
  obtain ⟨k, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hm := stage_ge_two_mul k (k + 1)
  have hmax : max 1 (k + 1) = k + 1 := by omega
  have h0 : (k + 1) / (stage (k + 1) (k + 1) - 1) = 0 := Nat.div_eq_of_lt (by omega)
  show stage (k + 1) (max 1 (k + 1)) =
    stage (k + 1) ((k + 1) + (k + 1) / (stage (k + 1) (max 1 (k + 1)) - 1))
  rw [hmax, h0, add_zero]

/-- The sieving numbers of the first five rounds are `2, 3, 7, 9, 13`. -/
theorem sievingNumber_first_five :
    (List.range 5).map sievingNumber = [2, 3, 7, 9, 13] := by decide

/-- The first ten lucky numbers agree with OEIS A000959. -/
theorem lucky_first_ten :
    (List.range 10).map lucky = [1, 3, 7, 9, 13, 15, 21, 25, 31, 33] := by decide

/-- The sieve deletes `5`. -/
theorem not_isLucky_five : ¬ IsLucky 5 := fun h => by have := h.mod_six; omega

/-- There are infinitely many lucky numbers. -/
theorem isLucky_infinite : {n | IsLucky n}.Infinite := by
  have : {n | IsLucky n} = Set.range lucky := by
    ext n; simp [isLucky_iff]
  rw [this]
  exact Set.infinite_range_of_injective lucky_strictMono.injective

/-! ## No twin pair among the lucky primes -/

/-- The intersection of the lucky numbers with the primes. -/
def luckyPrimes : Set ℕ := {p | IsLucky p ∧ p.Prime}

/-- Twin pairs in the intersection: pairs `(p, p + 2)` with both members lucky primes. -/
def twinPairs : Set (ℕ × ℕ) := {pq | pq.1 ∈ luckyPrimes ∧ pq.2 ∈ luckyPrimes ∧ pq.2 = pq.1 + 2}

theorem three_dvd_of_mod_six {n : ℕ} (h : n % 6 = 3) : 3 ∣ n := by omega

/-- A lucky prime `p` for which `p + 2` is prime must be `3`. -/
theorem eq_three_of_luckyPrime_of_prime_add_two {p : ℕ} (hp : p ∈ luckyPrimes)
    (hq : (p + 2).Prime) : p = 3 := by
  obtain ⟨hl, hpr⟩ := hp
  rcases hl.mod_six with h | h
  · have h3 : 3 ∣ p + 2 := by omega
    rcases hq.eq_one_or_self_of_dvd 3 h3 with h' | h'
    · omega
    · have : p = 1 := by omega
      exact absurd (this ▸ hpr) Nat.not_prime_one
  · rcases hpr.eq_one_or_self_of_dvd 3 (three_dvd_of_mod_six h) with h' | h'
    · omega
    · omega

/-- No two lucky primes differ by `2`. -/
theorem luckyPrimes_no_gap_two {p q : ℕ} (hp : p ∈ luckyPrimes) (hq : q ∈ luckyPrimes) :
    q ≠ p + 2 := by
  rintro rfl
  have h3 := eq_three_of_luckyPrime_of_prime_add_two hp hq.2
  subst h3
  have := hq.1.mod_six
  omega

theorem twinPairs_eq_empty : twinPairs = ∅ := by
  ext ⟨p, q⟩
  simp only [twinPairs, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hp, hq, rfl⟩
  exact luckyPrimes_no_gap_two hp hq rfl

theorem twinPairs_not_infinite : ¬ twinPairs.Infinite := by
  rw [twinPairs_eq_empty]
  exact Set.finite_empty.not_infinite

/-- The formalizer's restatement fails: there are no (in particular, not infinitely many)
`p` with `p` and `p + 2` both lucky primes. -/
theorem twin_lucky_primes_not_infinite :
    ¬ {p : ℕ | p.Prime ∧ IsLucky p ∧ (p + 2).Prime ∧ IsLucky (p + 2)}.Infinite := by
  have : {p : ℕ | p.Prime ∧ IsLucky p ∧ (p + 2).Prime ∧ IsLucky (p + 2)} = ∅ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2, h3, h4⟩
    exact luckyPrimes_no_gap_two ⟨h2, h1⟩ ⟨h4, h3⟩ rfl
  rw [this]
  exact Set.finite_empty.not_infinite

/-- Weaker reading (only the smaller member needs to be a lucky prime): the only such `p`
is `3`, so there are finitely many. -/
theorem weak_twin_finite : {p | p ∈ luckyPrimes ∧ (p + 2).Prime}.Finite :=
  (Set.finite_singleton 3).subset fun _ hp => eq_three_of_luckyPrime_of_prime_add_two hp.1 hp.2

/-- **Conjecture 00000000211 is false.**  Whatever the density clause `DensityClaim` means,
the conjunction "`DensityClaim` and the lucky-prime intersection contains infinitely many
twin pairs" fails, because that intersection contains no twin pair at all. -/
theorem conjecture211_false (DensityClaim : Prop) :
    ¬ (DensityClaim ∧ twinPairs.Infinite) :=
  fun h => twinPairs_not_infinite h.2

end Conjecture211
