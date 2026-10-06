import Mathlib

/-!
# Conjecture 00000009939 is false

Persistence entropy (Atienza, Gonzalez-Diaz, Rucco; Atienza, Gonzalez-Diaz, Soriano-Trigueros) of a
barcode with finite bars of lengths `l_1, ..., l_n` and total length `L = l_1 + ... + l_n` is
`E = - sum_i p_i log p_i` with `p_i = l_i / L`, i.e. `E = sum_i negMulLog (l_i / L)`.

The conjecture asserts that `E - (contribution of a longest bar) <= (1/2) log n`, where the
contribution of the bar `I` is its own summand `negMulLog (l_I / L)` (Chinese text:
"entropy minus the longest bar's contribution").  We refute this:

* `bound_fails_every_count`: for every bar count `n >= 2` there is a barcode with `n` pairwise
  distinct bars and a unique longest bar violating the bound (the bars `[0,2)` and `[i,i+1)`,
  `i < n - 1`); for `n = 3` the bars `[0,2), [0,1), [1,2)` give `E - c = log 2 > (1/2) log 3`.
* `conjecture9939_false`: the universal inequality `ConjecturedBound` is false.
* `no_constant_below_one`: no constant `c < 1` can replace `1/2`.
* `binary_reading_false`, `minEntropy_reading_false`: the bound also fails if the longest bar's
  "Shannon entropy" is read as the binary entropy `h(p_max)` or as `-log p_max`.

Natural logarithm throughout (both sides of the inequality scale by the same factor under a change
of base).
-/

open Real

namespace Conjecture9939

noncomputable section

/-- A finite persistence bar `[birth, death)` with `birth < death`. -/
structure Bar where
  birth : ℝ
  death : ℝ
  birth_lt_death : birth < death

/-- The length (persistence) `death - birth` of a bar. -/
def Bar.length (I : Bar) : ℝ := I.death - I.birth

lemma Bar.length_pos (I : Bar) : 0 < I.length := sub_pos.mpr I.birth_lt_death

/-- A persistence barcode: a finite multiset of finite bars. -/
abbrev Barcode := Multiset Bar

/-- Total length `L = sum_i l_i`. -/
def totalLength (B : Barcode) : ℝ := (B.map Bar.length).sum

/-- The contribution `-p log p` (with `p = l_I / L`) of the bar `I` to the persistence entropy. -/
def contribution (B : Barcode) (I : Bar) : ℝ := negMulLog (I.length / totalLength B)

/-- Persistence entropy `E(B) = - sum_i p_i log p_i`, `p_i = l_i / L`, summed over the bars of `B`
with multiplicity. -/
def persistenceEntropy (B : Barcode) : ℝ := (B.map (contribution B)).sum

/-- The number of bars (with multiplicity). -/
def barCount (B : Barcode) : ℕ := Multiset.card B

/-- `I` is a longest bar of `B`. -/
def IsLongestBar (B : Barcode) (I : Bar) : Prop := I ∈ B ∧ ∀ J ∈ B, J.length ≤ I.length

/-- The conjectured inequality: for every nonempty barcode and every longest bar `I`,
`E(B) - contribution(I) <= (1/2) log (number of bars)`. -/
def ConjecturedBound : Prop :=
  ∀ B : Barcode, B ≠ 0 → ∀ I : Bar, IsLongestBar B I →
    persistenceEntropy B - contribution B I ≤ (1 / 2) * log (barCount B)

/-- Alternative reading: the longest bar's "Shannon entropy" is the binary entropy `h(p_max)`. -/
def BinaryBound : Prop :=
  ∀ B : Barcode, B ≠ 0 → ∀ I : Bar, IsLongestBar B I →
    persistenceEntropy B - binEntropy (I.length / totalLength B) ≤ (1 / 2) * log (barCount B)

/-- Alternative reading: the longest bar's "Shannon entropy" is its self-information
`-log p_max` (the min-entropy of the length distribution). -/
def MinEntropyBound : Prop :=
  ∀ B : Barcode, B ≠ 0 → ∀ I : Bar, IsLongestBar B I →
    persistenceEntropy B - (-log (I.length / totalLength B)) ≤ (1 / 2) * log (barCount B)

/-! ## The witness family: one bar `[0,a)` and `m` unit bars `[i,i+1)`, `i < m` -/

/-- The bar `[0, a)`. -/
def longBar (a : ℝ) (ha : 0 < a) : Bar := ⟨0, a, ha⟩

/-- The unit bar `[i, i+1)`. -/
def unitBar (i : ℕ) : Bar := ⟨i, i + 1, by linarith⟩

/-- The barcode `{[0,a)} + {[i,i+1) : i < m}`. -/
def spike (a : ℝ) (ha : 0 < a) (m : ℕ) : Barcode :=
  longBar a ha ::ₘ (Multiset.range m).map unitBar

variable {a : ℝ} {ha : 0 < a} {m : ℕ}

lemma length_longBar : (longBar a ha).length = a := by simp [longBar, Bar.length]

lemma length_unitBar (i : ℕ) : (unitBar i).length = 1 := by simp [unitBar, Bar.length]

lemma unitBar_injective : Function.Injective unitBar := by
  intro i j h
  have := congrArg Bar.birth h
  simpa [unitBar] using this

lemma spike_ne_zero : spike a ha m ≠ 0 := Multiset.cons_ne_zero

/-- For `a ≠ 1` the bars of `spike a ha m` are pairwise distinct intervals. -/
lemma spike_nodup (h1 : a ≠ 1) : (spike a ha m).Nodup := by
  rw [spike, Multiset.nodup_cons]
  refine ⟨?_, (Multiset.nodup_range m).map unitBar_injective⟩
  intro hmem
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  have := congrArg Bar.length hi
  rw [length_unitBar, length_longBar] at this
  exact h1 this.symm

lemma barCount_spike : barCount (spike a ha m) = m + 1 := by simp [barCount, spike]

lemma totalLength_spike : totalLength (spike a ha m) = a + m := by
  have : (Bar.length ∘ unitBar) = fun _ => (1 : ℝ) := by funext i; simp [length_unitBar]
  simp only [totalLength, spike, Multiset.map_cons, Multiset.sum_cons, Multiset.map_map, this,
    Multiset.map_const', Multiset.card_range, Multiset.sum_replicate, length_longBar,
    nsmul_eq_mul, mul_one]

lemma entropy_spike : persistenceEntropy (spike a ha m) =
    negMulLog (a / (a + m)) + m * negMulLog (1 / (a + m)) := by
  have hc : contribution (spike a ha m) = fun I => negMulLog (I.length / (a + m)) := by
    funext I; rw [contribution, totalLength_spike]
  rw [persistenceEntropy, hc]
  have : ((fun I : Bar => negMulLog (I.length / (a + m))) ∘ unitBar) =
      fun _ => negMulLog (1 / (a + m)) := by funext i; simp [length_unitBar]
  simp only [spike, Multiset.map_cons, Multiset.sum_cons, Multiset.map_map, this,
    Multiset.map_const', Multiset.card_range, Multiset.sum_replicate, length_longBar,
    nsmul_eq_mul]

lemma mem_spike {I : Bar} : I ∈ spike a ha m ↔ I = longBar a ha ∨ ∃ i < m, unitBar i = I := by
  simp [spike]

lemma isLongest_longBar (h1 : 1 ≤ a) : IsLongestBar (spike a ha m) (longBar a ha) := by
  refine ⟨Multiset.mem_cons_self _ _, fun J hJ => ?_⟩
  rcases mem_spike.1 hJ with rfl | ⟨i, -, rfl⟩
  · exact le_rfl
  · rw [length_unitBar, length_longBar]; exact h1

/-- For `a > 1` the bar `[0,a)` is the unique longest bar. -/
lemma longest_eq (h1 : 1 < a) {I : Bar} (hI : IsLongestBar (spike a ha m) I) :
    I = longBar a ha := by
  rcases mem_spike.1 hI.1 with h | ⟨i, -, rfl⟩
  · exact h
  · have := hI.2 _ (Multiset.mem_cons_self _ _)
    rw [length_unitBar, length_longBar] at this
    linarith

/-- The gap `E - contribution(longest bar)` of `spike a ha m` equals `(m/L) log L`, `L = a + m`. -/
lemma gap_spike (h1 : 1 < a) {I : Bar} (hI : IsLongestBar (spike a ha m) I) :
    persistenceEntropy (spike a ha m) - contribution (spike a ha m) I =
      m / (a + m) * log (a + m) := by
  rw [longest_eq h1 hI, entropy_spike, contribution, totalLength_spike, length_longBar]
  rw [show negMulLog (1 / (a + m)) = -(1 / (a + m)) * log (1 / (a + m)) from rfl, one_div,
    log_inv]
  ring

/-! ## Main reading -/

/-- The key inequality `(1/2) log (m+1) < (m/(m+2)) log (m+2)` for `m >= 1`. -/
lemma key_ineq (hm : 1 ≤ m) :
    (1 / 2) * log ((m : ℝ) + 1) < (m : ℝ) / (2 + m) * log (2 + m) := by
  rcases Nat.lt_or_ge m 2 with h | h
  · obtain rfl : m = 1 := by omega
    have h89 : log 8 < log 9 := log_lt_log (by norm_num) (by norm_num)
    have e8 : log 8 = 3 * log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; norm_num
    have e9 : log 9 = 2 * log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]; norm_num
    norm_num
    linarith
  · have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast h
    have h1 : (1 / 2 : ℝ) ≤ m / (2 + m) := by rw [le_div_iff₀ (by positivity)]; linarith
    have h2 : log ((m : ℝ) + 1) < log (2 + m) := log_lt_log (by positivity) (by linarith)
    have h4 : 0 ≤ log (2 + (m : ℝ)) := log_nonneg (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right h1 h4]

/-- For every bar count `n >= 2` there is a barcode with exactly `n` pairwise distinct bars and a
unique longest bar such that, for its (every) longest bar `I`,
`E(B) - contribution(I) > (1/2) log n`. -/
theorem bound_fails_every_count (n : ℕ) (hn : 2 ≤ n) :
    ∃ B : Barcode, B ≠ 0 ∧ barCount B = n ∧ B.Nodup ∧ (∃ I, IsLongestBar B I) ∧
      (∀ I J, IsLongestBar B I → IsLongestBar B J → I = J) ∧
      ∀ I, IsLongestBar B I → (1 / 2) * log (barCount B) < persistenceEntropy B - contribution B I := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨spike 2 two_pos m, spike_ne_zero, barCount_spike, spike_nodup (by norm_num),
    ⟨_, isLongest_longBar (by norm_num)⟩,
    fun I J hI hJ => (longest_eq (by norm_num) hI).trans (longest_eq (by norm_num) hJ).symm,
    fun I hI => ?_⟩
  rw [gap_spike (by norm_num) hI, barCount_spike]
  push_cast
  exact key_ineq (by omega)

/-- The concrete witness `n = 3`: bars `[0,2), [0,1), [1,2)` (lengths `2, 1, 1`), for which
`E - contribution(longest) = log 2 > (1/2) log 3`. -/
theorem witness_211 :
    (spike 2 two_pos 2).map Bar.length = {2, 1, 1} ∧
    persistenceEntropy (spike 2 two_pos 2) - contribution (spike 2 two_pos 2) (longBar 2 two_pos)
      = log 2 ∧
    (1 / 2) * log (barCount (spike 2 two_pos 2)) < log 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have : (Bar.length ∘ unitBar) = fun _ => (1 : ℝ) := by funext i; simp [length_unitBar]
    simp only [spike, Multiset.map_cons, Multiset.map_map, this, Multiset.map_const',
      Multiset.card_range, length_longBar]
    rfl
  · rw [gap_spike (by norm_num) (isLongest_longBar (by norm_num))]
    have e4 : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
    push_cast
    norm_num
    rw [e4]; ring
  · rw [barCount_spike]
    have h34 : log 3 < log 4 := log_lt_log (by norm_num) (by norm_num)
    have e4 : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
    push_cast
    norm_num
    linarith

/-- **Main theorem.** The conjectured inequality
`E(B) - contribution(longest bar) <= (1/2) log (number of bars)` is false. -/
theorem conjecture9939_false : ¬ ConjecturedBound := by
  intro h
  obtain ⟨B, hB0, -, -, ⟨I, hI⟩, -, hlt⟩ := bound_fails_every_count 3 (by norm_num)
  have := h B hB0 I hI
  linarith [hlt I hI]

/-- No constant `c < 1` works in place of `1/2`: for every `c < 1` some barcode with a unique
longest bar has `E(B) - contribution(longest) > c log (number of bars)`. -/
theorem no_constant_below_one (c : ℝ) (hc : c < 1) :
    ∃ B : Barcode, B ≠ 0 ∧ (∃ I, IsLongestBar B I) ∧
      ∀ I, IsLongestBar B I → c * log (barCount B) < persistenceEntropy B - contribution B I := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / (1 - c))
  have h1c : 0 < 1 - c := by linarith
  have hmpos : (0 : ℝ) < m := lt_trans (by positivity) hm
  refine ⟨spike 2 two_pos m, spike_ne_zero, ⟨_, isLongest_longBar (by norm_num)⟩, fun I hI => ?_⟩
  rw [gap_spike (by norm_num) hI, barCount_spike]
  push_cast
  have hcm : c < m / (2 + m) := by
    rw [lt_div_iff₀ (by positivity)]
    have := (div_lt_iff₀ h1c).1 hm
    nlinarith
  have hl : 0 < log ((m : ℝ) + 1) := log_pos (by linarith)
  have hl2 : log ((m : ℝ) + 1) < log (2 + m) := log_lt_log (by positivity) (by linarith)
  have hq : 0 < (m : ℝ) / (2 + m) := by positivity
  nlinarith [mul_lt_mul_of_pos_left hl2 hq, mul_lt_mul_of_pos_right hcm hl]

/-! ## Alternative readings of "the Shannon entropy of the longest bar" -/

lemma binGap_spike (hm : 0 < m) :
    persistenceEntropy (spike a ha m) - binEntropy (a / (a + m)) = m / (a + m) * log m := by
  have hL : (0 : ℝ) < a + m := by positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [entropy_spike, binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    show 1 - a / (a + m) = m / (a + m) by field_simp; ring]
  simp only [negMulLog, one_div, log_inv, log_div hm'.ne' hL.ne']
  field_simp
  ring

lemma minGap_spike :
    persistenceEntropy (spike a ha m) - (-log (a / (a + m))) = m / (a + m) * log a := by
  have hL : (0 : ℝ) < a + m := by positivity
  rw [entropy_spike]
  simp only [negMulLog, one_div, log_inv, log_div ha.ne' hL.ne']
  field_simp
  ring

/-- Binary-entropy reading refuted by one bar of length 16 and 48 unit bars:
gap `(3/4) log 48 > (1/2) log 49`. -/
theorem binary_reading_false : ¬ BinaryBound := by
  intro h
  have := h (spike 16 (by norm_num) 48) spike_ne_zero _ (isLongest_longBar (by norm_num))
  rw [length_longBar, totalLength_spike, binGap_spike (by norm_num), barCount_spike] at this
  have hlt : log ((49 : ℝ) ^ 2) < log ((48 : ℝ) ^ 3) := log_lt_log (by norm_num) (by norm_num)
  rw [log_pow, log_pow] at hlt
  push_cast at this hlt
  norm_num at this
  linarith

/-- Min-entropy reading refuted by the same barcode: gap `(3/4) log 16 = log 8 > log 7 =
(1/2) log 49`. -/
theorem minEntropy_reading_false : ¬ MinEntropyBound := by
  intro h
  have := h (spike 16 (by norm_num) 48) spike_ne_zero _ (isLongest_longBar (by norm_num))
  rw [length_longBar, totalLength_spike, minGap_spike, barCount_spike] at this
  have hlt : log ((49 : ℝ) ^ 2) < log ((16 : ℝ) ^ 3) := log_lt_log (by norm_num) (by norm_num)
  rw [log_pow, log_pow] at hlt
  push_cast at this hlt
  norm_num at this
  linarith

end

end Conjecture9939
