import Mathlib

/-!
# Conjecture 00000007665 is false

The statement defines the q-Airy function

  `A_q(z) = ∑_{n ≥ 0} (-1)^n q^{n(n-1)/2} z^n / (q;q)_n`,   `(q;q)_n = ∏_{k=1}^{n} (1 - q^k)`,

and conjectures, for algebraic `q ∈ (0,1)`, that all zeros of `A_q` are real and simple, that the
`k`-th zero `z_k` on the negative half-axis satisfies `z_k = -q^{-k}(1 + O(q^{k/2}))`, and a
further (unspecified) spacing law for the `z_k`.

We prove that for every real `q ∈ (0,1)` the function `A_q` has **no zero on the closed negative
real half-axis**: for `x ≤ 0` every term `(-1)^n q^{n(n-1)/2} x^n / (q;q)_n = q^{n(n-1)/2} |x|^n /
(q;q)_n` is a nonnegative real number, the series converges (ratio test), and its `n = 0` term is
`1`, so `A_q(x) ≥ 1`. Hence there is no sequence of negative zeros `z_k`, and the asymptotic clause
fails for every `q ∈ (0,1)`, in particular for the algebraic number `q = 1/2`. We also show that the
asymptotic clause read for arbitrary complex zeros (without the words "on the negative half-axis")
is incompatible with the clause "all zeros are real".

Conventions: `n * (n - 1) / 2` is natural-number division (exact, equal to `n.choose 2`);
`q^{-k}` is written `(q ^ k)⁻¹` and `q^{k/2}` is written `(√q) ^ k`.
-/

open Filter Topology

namespace C7665

/-- The q-Pochhammer symbol `(q;q)_n = ∏_{k=1}^{n} (1 - q^k)` (empty product `1` for `n = 0`). -/
def qPoch (q : ℝ) (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, (1 - q ^ (k + 1))

/-- The q-Airy function of the statement,
`A_q(z) = ∑_{n ≥ 0} (-1)^n q^{n(n-1)/2} z^n / (q;q)_n`, as a complex function. -/
noncomputable def qAiry (q : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1) ^ n * (q : ℂ) ^ (n * (n - 1) / 2) * z ^ n / (qPoch q n : ℂ)

/-- Clause 1 of the conjecture: all zeros of `A_q` are real and simple. -/
def AllZerosRealSimple (q : ℝ) : Prop :=
  ∀ z : ℂ, qAiry q z = 0 → z.im = 0 ∧ deriv (qAiry q) z ≠ 0

/-- Clause 2 of the conjecture, literally: there are zeros `z_k` of `A_q` on the negative
half-axis (for all large `k`) with `z_k = -q^{-k}(1 + O(q^{k/2}))`, i.e.
`|z_k + q^{-k}| ≤ C q^{-k} q^{k/2}` for `k ≥ K`. (Any enumeration of the negative zeros that
satisfies the clause gives such a sequence, so this is implied by the clause.) -/
def NegZerosAsymptotic (q : ℝ) : Prop :=
  ∃ (z : ℕ → ℝ) (C : ℝ) (K : ℕ), ∀ k ≥ K, z k < 0 ∧ qAiry q (z k) = 0 ∧
    |z k + (q ^ k)⁻¹| ≤ C * (q ^ k)⁻¹ * Real.sqrt q ^ k

/-- Clause 2 without the words "on the negative half-axis": complex zeros `z_k` of `A_q` with
`|z_k + q^{-k}| ≤ C q^{-k} q^{k/2}` for `k ≥ K`. -/
def ZerosAsymptotic (q : ℝ) : Prop :=
  ∃ (z : ℕ → ℂ) (C : ℝ) (K : ℕ), ∀ k ≥ K, qAiry q (z k) = 0 ∧
    ‖z k + (((q ^ k)⁻¹ : ℝ) : ℂ)‖ ≤ C * (q ^ k)⁻¹ * Real.sqrt q ^ k

lemma qPoch_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : 0 < qPoch q n := by
  unfold qPoch
  apply Finset.prod_pos
  intro k _
  have : q ^ (k + 1) < 1 := pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero k)
  linarith

lemma qPoch_succ (q : ℝ) (n : ℕ) : qPoch q (n + 1) = qPoch q n * (1 - q ^ (n + 1)) := by
  simp [qPoch, Finset.prod_range_succ]

/-- The real terms `q^{n(n-1)/2} y^n / (q;q)_n`; for `x ≤ 0` the terms of `A_q(x)` are these
with `y = -x`. -/
noncomputable def term (q y : ℝ) (n : ℕ) : ℝ := q ^ (n.choose 2) * y ^ n / qPoch q n

lemma term_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    0 ≤ term q y n :=
  div_nonneg (mul_nonneg (pow_nonneg hq0.le _) (pow_nonneg hy _)) (qPoch_pos hq0 hq1 n).le

lemma term_succ {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (y : ℝ) (n : ℕ) :
    term q y (n + 1) = term q y n * (q ^ n * y / (1 - q ^ (n + 1))) := by
  have h1 : 0 < 1 - q ^ (n + 1) := by
    have : q ^ (n + 1) < 1 := pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero n)
    linarith
  have h2 := qPoch_pos hq0 hq1 n
  have hc : (n + 1).choose 2 = n + n.choose 2 := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
  unfold term
  rw [qPoch_succ, hc, pow_add]
  field_simp
  ring

/-- Ratio test: the real series `∑ q^{n(n-1)/2} y^n / (q;q)_n` converges for `y ≥ 0`. -/
lemma term_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {y : ℝ} (hy : 0 ≤ y) :
    Summable (term q y) := by
  apply summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num)
  have ht : Tendsto (fun n : ℕ => q ^ n * y) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).mul_const y
  have hε : (0 : ℝ) < (1 - q) / 2 := by linarith
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  rw [Real.norm_of_nonneg (term_nonneg hq0 hq1 hy _), Real.norm_of_nonneg (term_nonneg hq0 hq1 hy _),
    term_succ hq0 hq1]
  have hfac : q ^ n * y / (1 - q ^ (n + 1)) ≤ 1 / 2 := by
    have h1 : q ^ (n + 1) ≤ q := pow_le_of_le_one hq0.le hq1.le (Nat.succ_ne_zero n)
    have h1' : 0 < 1 - q ^ (n + 1) := by linarith
    rw [div_le_iff₀ h1']
    nlinarith
  calc term q y n * (q ^ n * y / (1 - q ^ (n + 1))) ≤ term q y n * (1 / 2) :=
        mul_le_mul_of_nonneg_left hfac (term_nonneg hq0 hq1 hy _)
    _ = 1 / 2 * term q y n := by ring

/-- On the closed negative half-axis, `A_q(x)` is the real number `∑ q^{n(n-1)/2} (-x)^n/(q;q)_n`. -/
lemma qAiry_ofReal_of_nonpos (q x : ℝ) :
    qAiry q (x : ℂ) = ((∑' n : ℕ, term q (-x) n : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold qAiry
  congr 1
  ext n
  unfold term
  rw [← Nat.choose_two_right]
  push_cast
  rw [neg_pow (x : ℂ) n]
  ring

/-- `A_q(x) ≥ 1` for `x ≤ 0` (as a real number). -/
lemma one_le_tsum_term {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : x ≤ 0) :
    1 ≤ ∑' n : ℕ, term q (-x) n := by
  have hy : 0 ≤ -x := by linarith
  have h := (term_summable hq0 hq1 hy).le_tsum 0 (fun j _ => term_nonneg hq0 hq1 hy j)
  simpa [term, qPoch] using h

/-- **Key fact.** For `0 < q < 1`, `A_q` has no zero on the closed negative half-axis. -/
theorem qAiry_ne_zero_of_nonpos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : x ≤ 0) :
    qAiry q (x : ℂ) ≠ 0 := by
  rw [qAiry_ofReal_of_nonpos]
  have := one_le_tsum_term hq0 hq1 hx
  exact_mod_cast (show (∑' n : ℕ, term q (-x) n) ≠ 0 by linarith)

/-- The literal asymptotic clause fails for every `q ∈ (0,1)`: there are no negative zeros. -/
theorem not_negZerosAsymptotic {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ¬ NegZerosAsymptotic q := by
  rintro ⟨z, C, K, h⟩
  obtain ⟨hneg, hzero, -⟩ := h K le_rfl
  exact qAiry_ne_zero_of_nonpos hq0 hq1 hneg.le hzero

/-- Clause 1 ("all zeros real") and clause 2 read for arbitrary complex zeros are incompatible,
for every `q ∈ (0,1)`: the asymptotics force `Re z_k < 0` for large `k`, and a real zero must be
`> 0`. -/
theorem not_allZerosReal_and_zerosAsymptotic {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ¬ (AllZerosRealSimple q ∧ ZerosAsymptotic q) := by
  rintro ⟨hreal, z, C, K, h⟩
  have hs0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs1 : Real.sqrt q < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using hq1
  have ht : Tendsto (fun k : ℕ => C * Real.sqrt q ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1).const_mul C
  obtain ⟨k, hk1, hkK⟩ :=
    ((ht.eventually (gt_mem_nhds one_pos)).and (eventually_ge_atTop K)).exists
  obtain ⟨hzero, hbound⟩ := h k hkK
  have him := (hreal _ hzero).1
  set a := (z k).re
  have hza : z k = (a : ℂ) := Complex.ext (by simp [a]) (by simp [him])
  set Q : ℝ := (q ^ k)⁻¹
  have hQ : 0 < Q := inv_pos.mpr (pow_pos hq0 k)
  rw [hza, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs] at hbound
  have h1 : a + Q ≤ |a + Q| := le_abs_self _
  have h2 : C * Q * Real.sqrt q ^ k < Q := by
    have : C * Q * Real.sqrt q ^ k = Q * (C * Real.sqrt q ^ k) := by ring
    rw [this]
    nlinarith
  have ha : a < 0 := by linarith
  rw [hza] at hzero
  exact qAiry_ne_zero_of_nonpos hq0 hq1 ha.le hzero

lemma isAlgebraic_half : IsAlgebraic ℚ (1 / 2 : ℝ) := by
  have := isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (1 / 2 : ℚ)
  simpa using this

/-- **Main theorem (conjecture 00000007665 is false).** For any formalization `Spacing` of the
third clause (the spacing law), the conjunction "for every algebraic `q ∈ (0,1)`: all zeros of
`A_q` are real and simple, the negative zeros satisfy `z_k = -q^{-k}(1 + O(q^{k/2}))`, and
`Spacing q`" is false; the counterexample is `q = 1/2`. -/
theorem conjecture_7665_false (Spacing : ℝ → Prop) :
    ¬ ∀ q : ℝ, IsAlgebraic ℚ q → 0 < q → q < 1 →
      AllZerosRealSimple q ∧ NegZerosAsymptotic q ∧ Spacing q := by
  intro h
  exact not_negZerosAsymptotic (q := 1 / 2) (by norm_num) (by norm_num)
    (h (1 / 2) isAlgebraic_half (by norm_num) (by norm_num)).2.1

/-- Same conclusion when clause 2 is read for arbitrary complex zeros (not assumed to lie on the
negative half-axis): it contradicts clause 1 at `q = 1/2`. -/
theorem conjecture_7665_false' (Spacing : ℝ → Prop) :
    ¬ ∀ q : ℝ, IsAlgebraic ℚ q → 0 < q → q < 1 →
      AllZerosRealSimple q ∧ ZerosAsymptotic q ∧ Spacing q := by
  intro h
  obtain ⟨h1, h2, -⟩ := h (1 / 2) isAlgebraic_half (by norm_num) (by norm_num)
  exact not_allZerosReal_and_zerosAsymptotic (q := 1 / 2) (by norm_num) (by norm_num) ⟨h1, h2⟩

end C7665
