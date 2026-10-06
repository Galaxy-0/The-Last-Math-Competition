import Mathlib

/-!
# Conjecture 00000000172 (Somos binary density) is false under its own definition

The conjecture *defines* `σ = lim σ_n^{1/n}`, where `σ_1 = 1` and `σ_n = σ_{n-1} + σ_{⌊n/2⌋}`
(`n ≥ 2`; this is OEIS A033485: 1, 2, 3, 5, 7, 10, …), and conjectures that the density of 1's in the
binary expansion of `σ` diverges, that the counting function of the 1's grows as `Θ(log log n)`,
and that this gives a proof of the irrationality of `σ`.

We show that, for *every* real sequence satisfying the stated recurrence, `σ_n^{1/n} → 1`.
The proof: `1 ≤ σ_n`, `σ_n` is monotone, `σ_n ≤ n σ_{⌊n/2⌋}`, hence `σ_n ≤ n^{⌊log₂ n⌋ + 1}`, so
`0 ≤ log σ_n / n ≤ ((log n)²/log 2 + log n)/n → 0`.  Hence `σ = 1`, which is rational, and
every binary expansion of `1` is `1.000…` or `0.111…`; for these the number of 1's among the
first `n` digits is `0` or `n` (plus any fixed offset `c` for counting conventions of the integer
part), which is not `Θ(log log n)`, and the density converges (to `0` or `1`).

Note: the name "Somos's constant" usually refers to a different number (`≈ 1.6616`, from the
quadratic recurrence `g_n = n g_{n-1}^2`); this file uses the definition written in the conjecture.
-/

open Real Filter Finset Asymptotics Topology

namespace C172

/-- `a` satisfies the conjecture's definition: `σ_1 = 1` and `σ_n = σ_{n-1} + σ_{⌊n/2⌋}` for all
`n ≥ 2`.  (The value `a 0` is unconstrained and never used.) -/
structure IsSomosSeq (a : ℕ → ℝ) : Prop where
  one : a 1 = 1
  recur : ∀ n, 2 ≤ n → a n = a (n - 1) + a (n / 2)

/-- A concrete such sequence (OEIS A033485), so the definition is not vacuous. -/
def A : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => A (n + 1) + A ((n + 2) / 2)
decreasing_by all_goals omega

theorem isSomosSeq_A : IsSomosSeq (fun n => (A n : ℝ)) where
  one := by simp [A]
  recur n hn := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [show m + 2 - 1 = m + 1 by omega]
    rw [A]; push_cast; ring

variable {a : ℕ → ℝ}

theorem one_le (ha : IsSomosSeq a) : ∀ n, 1 ≤ n → 1 ≤ a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      rw [ha.one]
    · rw [ha.recur n h]
      have h1 := ih (n - 1) (by omega) (by omega)
      have h2 := ih (n / 2) (by omega) (by omega)
      linarith

theorem mono (ha : IsSomosSeq a) {m : ℕ} (hm : 1 ≤ m) : ∀ n, m ≤ n → a m ≤ a n := by
  intro n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
    rw [ha.recur (n + 1) (by omega), Nat.add_sub_cancel]
    have := one_le ha ((n + 1) / 2) (by omega)
    linarith

theorem le_mul_half (ha : IsSomosSeq a) : ∀ n, 2 ≤ n → a n ≤ n * a (n / 2) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rw [ha.recur 2 le_rfl]; norm_num [ha.one]
  | succ n hn ih =>
    rw [ha.recur (n + 1) (by omega), Nat.add_sub_cancel]
    have hm := mono ha (m := n / 2) (by omega) ((n + 1) / 2) (by omega)
    have hpos := one_le ha ((n + 1) / 2) (by omega)
    push_cast
    nlinarith

/-- `σ_n ≤ n^{⌊log₂ n⌋ + 1}`. -/
theorem le_pow (ha : IsSomosSeq a) : ∀ n, 1 ≤ n → a n ≤ (n : ℝ) ^ (Nat.log 2 n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      simp [ha.one]
    · have h1 := le_mul_half ha n h
      have h2 := ih (n / 2) (by omega) (by omega)
      have hlog : Nat.log 2 (n / 2) + 1 = Nat.log 2 n := by
        rw [Nat.log_div_base]; have := Nat.log_pos one_lt_two h; omega
      rw [hlog] at h2
      have h3 : ((n / 2 : ℕ) : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) ^ Nat.log 2 n :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self n 2) _
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      calc a n ≤ n * a (n / 2) := h1
        _ ≤ n * (n : ℝ) ^ Nat.log 2 n := mul_le_mul_of_nonneg_left (h2.trans h3) hn0
        _ = (n : ℝ) ^ (Nat.log 2 n + 1) := by ring

theorem log_le (ha : IsSomosSeq a) {n : ℕ} (hn : 1 ≤ n) :
    log (a n) ≤ (log n / log 2 + 1) * log n := by
  have hpos : 0 < a n := lt_of_lt_of_le one_pos (one_le ha n hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl2 := log_pos (one_lt_two : (1 : ℝ) < 2)
  have hlogn : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn)
  have h1 : log (a n) ≤ (Nat.log 2 n + 1 : ℕ) * log n := by
    rw [← log_pow]; exact log_le_log hpos (le_pow ha n hn)
  have h2 : (Nat.log 2 n : ℝ) ≤ log n / log 2 := by
    rw [le_div_iff₀ hl2, ← log_pow]
    exact log_le_log (by positivity) (by exact_mod_cast Nat.pow_log_le_self 2 (by omega))
  push_cast at h1
  nlinarith

/-- **For every sequence satisfying the definition, `σ_n^{1/n} → 1`.** -/
theorem tendsto_root (ha : IsSomosSeq a) :
    Tendsto (fun n : ℕ => a n ^ ((1 : ℝ) / n)) atTop (𝓝 1) := by
  have hl2 := log_pos (one_lt_two : (1 : ℝ) < 2)
  have t1 := ((tendsto_pow_log_div_mul_add_atTop (log 2) 0 2 hl2.ne').comp
    tendsto_natCast_atTop_atTop)
  have t2 := ((tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop)
  have hsq : Tendsto (fun n : ℕ => log (a n) / n) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using t1.add t2) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact div_nonneg (log_nonneg (one_le ha n hn)) (Nat.cast_nonneg n)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have := log_le ha hn
      rw [div_add_div _ _ (by positivity) hn0.ne', div_le_div_iff₀ hn0 (by positivity)]
      have e : (log n / log 2 + 1) * log n * (log 2 * n * n) =
          (log n ^ 2 * n + log 2 * n * log n) * n := by field_simp
      have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ log 2 * n * n)
      linarith
  have := (continuous_exp.tendsto 0).comp hsq
  rw [exp_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Function.comp, rpow_def_of_pos (lt_of_lt_of_le one_pos (one_le ha n hn))]
  ring_nf

/-- Number of 1's among the first `n` binary digits `d 0, …, d (n-1)` after the point. -/
def onesCount (d : ℕ → ℕ) (n : ℕ) : ℕ := ((range n).filter (fun k => d k = 1)).card

/-- `(m, d)` is a binary expansion of `x`: digits `d k ∈ {0, 1}` and
`x = m + ∑_{k ≥ 0} d k / 2^{k+1}`. -/
def IsBinaryExpansion (x : ℝ) (m : ℤ) (d : ℕ → ℕ) : Prop :=
  (∀ k, d k ≤ 1) ∧ x = m + ∑' k, (d k : ℝ) / 2 ^ (k + 1)

/-- The only binary expansions of `1` are `1.000…` and `0.111…`. -/
theorem expansion_of_one {m : ℤ} {d : ℕ → ℕ} (h : IsBinaryExpansion 1 m d) :
    (∀ k, d k = 0) ∨ (∀ k, d k = 1) := by
  obtain ⟨hd, hx⟩ := h
  set f : ℕ → ℝ := fun k => (d k : ℝ) / 2 ^ (k + 1)
  have hg2 : ∀ k : ℕ, (1 : ℝ) / 2 / 2 ^ k = 1 / 2 ^ (k + 1) := fun k => by ring
  have hf0 : ∀ k, 0 ≤ f k := fun k => by positivity
  have hfle : ∀ k, f k ≤ 1 / 2 / 2 ^ k := fun k => by
    rw [hg2]; exact div_le_div_of_nonneg_right (by exact_mod_cast hd k) (by positivity)
  have hg := summable_geometric_two' 1
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hfle hg
  have hS1 : ∑' k, f k ≤ 1 := (hfs.tsum_le_tsum hfle hg).trans (tsum_geometric_two' 1).le
  have hS0 : 0 ≤ ∑' k, f k := tsum_nonneg hf0
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hm1 : (m : ℝ) ≤ 1 := by linarith
  have hm : m = 0 ∨ m = 1 := by
    have : 0 ≤ m := by exact_mod_cast hm0
    have : m ≤ 1 := by exact_mod_cast hm1
    omega
  rcases hm with rfl | rfl
  · right
    intro k
    by_contra hk
    have hk0 : d k = 0 := by have := hd k; omega
    have hS : ∑' k, f k = 1 := by push_cast at hx; linarith
    have hh := hg.sub hfs
    have hsum : ∑' j, (1 / 2 / 2 ^ j - f j) = 0 := by
      rw [hg.tsum_sub hfs, tsum_geometric_two', hS, sub_self]
    have := hh.le_tsum k (fun j _ => sub_nonneg.2 (hfle j))
    simp only [hsum, f, hk0, Nat.cast_zero, zero_div, sub_zero] at this
    have : (0 : ℝ) < 1 / 2 / 2 ^ k := by positivity
    linarith
  · left
    intro k
    by_contra hk
    have hk1 : d k = 1 := by have := hd k; omega
    have hS : ∑' k, f k = 0 := by push_cast at hx; linarith
    have := hfs.le_tsum k (fun j _ => hf0 j)
    simp only [hS, f, hk1, Nat.cast_one] at this
    have : (0 : ℝ) < 1 / 2 ^ (k + 1) := by positivity
    linarith

theorem tendsto_loglog : Tendsto (fun n : ℕ => log (log (n : ℝ))) atTop atTop :=
  tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem loglog_isLittleO : (fun n : ℕ => log (log (n : ℝ))) =o[atTop] fun n : ℕ => (n : ℝ) :=
  ((isLittleO_log_id_atTop.comp_tendsto tendsto_log_atTop).trans
    isLittleO_log_id_atTop).comp_tendsto tendsto_natCast_atTop_atTop

/-- A function equal to a constant, or to `c + n`, is not `Θ(log log n)`, and `F(n)/n` converges. -/
theorem refute (c : ℝ) (F : ℕ → ℝ) (hF : (∀ n, F n = c) ∨ (∀ n, F n = c + n)) :
    ¬ (F =Θ[atTop] fun n : ℕ => log (log (n : ℝ))) ∧
      ∃ L, Tendsto (fun n : ℕ => F n / n) atTop (𝓝 L) := by
  rcases hF with hF | hF
  · have hF' : F = fun _ => c := funext hF
    subst hF'
    refine ⟨fun h => ?_, 0, tendsto_const_div_atTop_nhds_zero_nat c⟩
    obtain ⟨C, hC⟩ := h.2.bound
    obtain ⟨n, h1, h2⟩ := (hC.and (tendsto_loglog.eventually_gt_atTop (C * ‖c‖))).exists
    linarith [le_norm_self (log (log (n : ℝ)))]
  · have hF' : F = fun n : ℕ => c + (n : ℝ) := funext hF
    subst hF'
    refine ⟨fun h => ?_, 1, ?_⟩
    · have hlo := (h.1.trans_isLittleO loglog_isLittleO).def (by norm_num : (0 : ℝ) < 1 / 2)
      obtain ⟨n, h1, h2⟩ :=
        (hlo.and (tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * |c| + 1))).exists
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast] at h1
      have := le_abs_self (c + n)
      have := neg_abs_le c
      linarith
    · have := (tendsto_const_div_atTop_nhds_zero_nat c).add_const 1
      rw [zero_add] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp

/-- **Main theorem (conjecture 00000000172 is false).**  For every sequence `a` satisfying the
conjecture's definition and every `σ` with `a n ^ (1/n) → σ`: `σ = 1`; `σ` is not irrational; and
for every binary expansion `(m, d)` of `σ` and every fixed offset `c` (for any counting
convention of the integer-part digits), the counting function `c + #{k < n : d k = 1}` is not
`Θ(log log n)`, and the density `(c + #{k < n : d k = 1})/n` converges (so it does not diverge,
in particular it does not tend to `+∞`). -/
theorem conjecture_172_false (a : ℕ → ℝ) (ha : IsSomosSeq a) (σ : ℝ)
    (hσ : Tendsto (fun n : ℕ => a n ^ ((1 : ℝ) / n)) atTop (𝓝 σ)) :
    σ = 1 ∧ ¬ Irrational σ ∧
    ∀ (m : ℤ) (d : ℕ → ℕ), IsBinaryExpansion σ m d → ∀ c : ℝ,
      ¬ ((fun n : ℕ => c + (onesCount d n : ℝ)) =Θ[atTop] fun n : ℕ => log (log (n : ℝ))) ∧
      (∃ L, Tendsto (fun n : ℕ => (c + (onesCount d n : ℝ)) / n) atTop (𝓝 L)) ∧
      ¬ Tendsto (fun n : ℕ => (c + (onesCount d n : ℝ)) / n) atTop atTop := by
  have hσ1 : σ = 1 := tendsto_nhds_unique hσ (tendsto_root ha)
  subst hσ1
  refine ⟨rfl, not_irrational_one, fun m d hexp c => ?_⟩
  have hF : (∀ n, c + (onesCount d n : ℝ) = c) ∨ (∀ n, c + (onesCount d n : ℝ) = c + n) := by
    rcases expansion_of_one hexp with h0 | h1
    · left; intro n; simp [onesCount, h0]
    · right; intro n; simp [onesCount, h1]
  obtain ⟨hT, L, hL⟩ := refute c _ hF
  exact ⟨hT, ⟨L, hL⟩, not_tendsto_atTop_of_tendsto_nhds hL⟩

/-- The conjecture's `σ` exists (for the concrete sequence `A`) and equals `1`. -/
theorem sigma_eq_one : Tendsto (fun n : ℕ => (A n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 1) :=
  tendsto_root isSomosSeq_A

end C172
