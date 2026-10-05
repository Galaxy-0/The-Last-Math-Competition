import Mathlib

/-!
# Conjecture 00000002181 is false

The conjecture asserts: "Sensitivity is always at most `sqrt 2 * log n` times the spectral norm"
(of a Boolean function on `n` variables), and further that "the bound is controlled by the pointer
maxima of real hypercubical faces".  The conjecture is a conjunction, so it is false as soon as its
first clause is false.  We refute the first clause with the parity function `x_1 xor ... xor x_n`:

* parity is sensitive to every bit at every input, so its sensitivity is `n`
  (at every point, hence also its maximum and average sensitivity);
* its Fourier (Walsh) `l1` norm, the spectral norm, equals `1`, both for the `+-1` output
  encoding `(-1)^f` and for the `0/1` output encoding (for `n >= 1`);
* `sqrt 2 * log n < n` for every `n >= 1`, for the natural logarithm and for `log_2`.

So the bound fails for every `n >= 1` (in particular for every `n >= 2`, where `log n > 0`), and
even `C * log n * (spectral norm) < sensitivity` holds for all large `n`, for every constant `C`;
this covers every logarithm base `b > 1`, since `log_b n = log n / log b`.  The same
unbounded failure holds inside the class of linear threshold functions, witnessed by AND
(sensitivity `n`, spectral norm `<= 3` for `+-1` output and `= 1` for `0/1` output).

Conventions: inputs are `x : Fin n -> Bool`; a bit `b` has sign `(-1)^b`, i.e. `false -> 1`,
`true -> -1`; Walsh characters are `chi_S(x) = prod_{i in S} (-1)^{x_i}`; Fourier coefficients
are normalised, `fhat(S) = 2^{-n} * sum_x g(x) chi_S(x)`; the spectral norm is
`sum_S |fhat(S)|`; `log` is `Real.log` (natural logarithm) and `Real.logb 2` is `log_2`.
-/

open Finset Real

namespace C2181

/-- A Boolean function on `n` bits. -/
abbrev BoolFun (n : ℕ) := (Fin n → Bool) → Bool

/-- The input `x` with bit `i` flipped. -/
def flipBit {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

/-- Sensitivity of `f` at the input `x`: the number of bits whose flip changes `f(x)`. -/
def sensAt {n : ℕ} (f : BoolFun n) (x : Fin n → Bool) : ℕ :=
  (univ.filter fun i => f (flipBit x i) ≠ f x).card

/-- The (maximum) sensitivity `s(f) = max_x s(f, x)`. -/
def sensitivity {n : ℕ} (f : BoolFun n) : ℕ :=
  univ.sup (sensAt f)

/-- The average sensitivity (total influence) `2^{-n} * sum_x s(f, x)`. -/
noncomputable def avgSensitivity {n : ℕ} (f : BoolFun n) : ℝ :=
  (∑ x, (sensAt f x : ℝ)) / 2 ^ n

/-- The sign `(-1)^b` of a bit: `false ↦ 1`, `true ↦ -1`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- The Walsh character `chi_S(x) = prod_{i in S} (-1)^{x_i}`. -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  ∏ i ∈ S, sgn (x i)

/-- The normalised Fourier (Walsh) coefficient `ghat(S) = 2^{-n} * sum_x g(x) chi_S(x)`. -/
noncomputable def fourierCoeff {n : ℕ} (g : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ x, g x * chi S x) / 2 ^ n

/-- The spectral norm (Fourier `l1` norm) `sum_S |ghat(S)|`. -/
noncomputable def spectralNorm {n : ℕ} (g : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), |fourierCoeff g S|

/-- The `+-1` output encoding `x ↦ (-1)^{f(x)}`. -/
def pmEnc {n : ℕ} (f : BoolFun n) : (Fin n → Bool) → ℝ := fun x => sgn (f x)

/-- The `0/1` output encoding `x ↦ [f(x) = true]`. -/
def zoEnc {n : ℕ} (f : BoolFun n) : (Fin n → Bool) → ℝ := fun x => if f x then 1 else 0

/-- The parity function: `true` iff an odd number of input bits are `true`. -/
def parity (n : ℕ) : BoolFun n :=
  fun x => decide (Odd (univ.filter fun i => x i = true).card)

/-! ## Elementary facts about signs -/

lemma sgn_not (b : Bool) : sgn (!b) = -sgn b := by
  cases b <;> simp [sgn]

lemma sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by
  cases b <;> norm_num [sgn]

/-- The sign of the parity is the product of the signs of the bits. -/
lemma sgn_parity {n : ℕ} (x : Fin n → Bool) : sgn (parity n x) = ∏ i, sgn (x i) := by
  have h : ∏ i, sgn (x i) = (-1 : ℝ) ^ (univ.filter fun i => x i = true).card := by
    unfold sgn
    rw [Finset.prod_ite]
    simp [Finset.prod_const]
  rw [h, parity]
  rcases Nat.even_or_odd (univ.filter fun i => x i = true).card with he | ho
  · rw [he.neg_one_pow]
    have : ¬ Odd (univ.filter fun i => x i = true).card := Nat.not_odd_iff_even.mpr he
    simp [sgn, this]
  · rw [ho.neg_one_pow]
    simp [sgn, ho]

/-- Flipping any bit flips the parity. -/
lemma parity_flipBit {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    parity n (flipBit x i) ≠ parity n x := by
  intro h
  have key : sgn (parity n (flipBit x i)) = -sgn (parity n x) := by
    rw [sgn_parity, sgn_parity, ← Finset.mul_prod_erase univ _ (mem_univ i),
      ← Finset.mul_prod_erase univ (fun j => sgn (x j)) (mem_univ i)]
    have hrest : ∏ j ∈ univ.erase i, sgn (flipBit x i j) = ∏ j ∈ univ.erase i, sgn (x j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [flipBit, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hrest, flipBit, Function.update_self, sgn_not]
    ring
  rw [h] at key
  have := sgn_ne_zero (parity n x)
  exact this (by linarith)

/-! ## Sensitivity of parity -/

/-- Parity is sensitive to every bit at every input. -/
theorem parity_sensAt {n : ℕ} (x : Fin n → Bool) : sensAt (parity n) x = n := by
  unfold sensAt
  rw [Finset.filter_true_of_mem fun i _ => parity_flipBit x i]
  simp

/-- The (maximum) sensitivity of parity on `n` bits is `n`. -/
theorem parity_sensitivity (n : ℕ) : sensitivity (parity n) = n := by
  unfold sensitivity
  rw [show sensAt (parity n) = fun _ => n from funext parity_sensAt]
  exact Finset.sup_const univ_nonempty n

/-- The average sensitivity of parity on `n` bits is `n`. -/
theorem parity_avgSensitivity (n : ℕ) : avgSensitivity (parity n) = n := by
  unfold avgSensitivity
  simp only [parity_sensAt, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-! ## Fourier coefficients of parity -/

/-- A sum over the cube of a product of one-bit functions factorises. -/
lemma sum_prod_bits {n : ℕ} (h : Fin n → Bool → ℝ) :
    ∑ x : Fin n → Bool, ∏ i, h i (x i) = ∏ i, (h i true + h i false) := by
  rw [← Fintype.prod_sum]
  simp

lemma chi_eq {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    chi S x = ∏ i, (if i ∈ S then sgn (x i) else 1) := by
  rw [chi, Fintype.prod_ite_mem]

/-- `sum_x chi_S(x) = 2^n [S = empty]`. -/
lemma sum_chi {n : ℕ} (S : Finset (Fin n)) :
    ∑ x, chi S x = if S = ∅ then 2 ^ n else 0 := by
  simp only [chi_eq]
  refine (sum_prod_bits (fun i b => if i ∈ S then sgn b else 1)).trans ?_
  split_ifs with hS
  · subst hS; simp; norm_num
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi, sgn])

/-- `sum_x (-1)^{parity x} chi_S(x) = 2^n [S = univ]`. -/
lemma sum_parity_chi {n : ℕ} (S : Finset (Fin n)) :
    ∑ x, pmEnc (parity n) x * chi S x = if S = univ then 2 ^ n else 0 := by
  simp only [pmEnc, sgn_parity, chi_eq, ← Finset.prod_mul_distrib]
  refine (sum_prod_bits (fun i b => sgn b * if i ∈ S then sgn b else 1)).trans ?_
  split_ifs with hS
  · subst hS; simp [sgn]; norm_num
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
      by_contra hc
      push Not at hc
      exact hS (Finset.eq_univ_of_forall hc)
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi, sgn])

/-- Fourier coefficients of `(-1)^{parity}`: `1` at `S = univ`, `0` elsewhere. -/
theorem fourierCoeff_pm_parity {n : ℕ} (S : Finset (Fin n)) :
    fourierCoeff (pmEnc (parity n)) S = if S = univ then 1 else 0 := by
  rw [fourierCoeff, sum_parity_chi]
  split_ifs <;> simp

/-- Fourier coefficients of the `0/1` parity (for `n >= 1`): `1/2` at the empty set,
`-1/2` at `univ`, `0` elsewhere. -/
theorem fourierCoeff_zo_parity {n : ℕ} (S : Finset (Fin n)) :
    fourierCoeff (zoEnc (parity n)) S =
      (if S = ∅ then 1 / 2 else 0) - (if S = univ then 1 / 2 else 0) := by
  have hz : ∀ x, zoEnc (parity n) x = (1 - pmEnc (parity n) x) / 2 := by
    intro x
    unfold zoEnc pmEnc sgn
    cases parity n x <;> norm_num
  have : ∑ x, zoEnc (parity n) x * chi S x =
      (∑ x, chi S x) / 2 - (∑ x, pmEnc (parity n) x * chi S x) / 2 := by
    simp only [hz, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [fourierCoeff, this, sum_chi, sum_parity_chi]
  split_ifs <;> field_simp <;> norm_num

/-! ## Spectral norm of parity -/

/-- The spectral norm of `(-1)^{parity}` is `1`. -/
theorem spectralNorm_pm_parity (n : ℕ) : spectralNorm (pmEnc (parity n)) = 1 := by
  unfold spectralNorm
  simp only [fourierCoeff_pm_parity]
  rw [Finset.sum_congr rfl (g := fun S => if S = univ then (1 : ℝ) else 0)
    (fun S _ => by split_ifs <;> simp)]
  simp

/-- The spectral norm of the `0/1` parity on `n >= 1` bits is `1`. -/
theorem spectralNorm_zo_parity {n : ℕ} (hn : 1 ≤ n) : spectralNorm (zoEnc (parity n)) = 1 := by
  have hne : (∅ : Finset (Fin n)) ≠ univ := by
    intro h
    have : (⟨0, hn⟩ : Fin n) ∈ (∅ : Finset (Fin n)) := h ▸ mem_univ _
    simp at this
  unfold spectralNorm
  simp only [fourierCoeff_zo_parity]
  rw [Finset.sum_congr rfl (g := fun S => (if S = ∅ then (1 / 2 : ℝ) else 0) +
      (if S = univ then (1 / 2 : ℝ) else 0)) (fun S _ => by
        by_cases h0 : S = ∅
        · subst h0; norm_num [hne]
        · by_cases h1 : S = univ
          · subst h1; norm_num [h0]
          · simp [h0, h1])]
  rw [Finset.sum_add_distrib]
  simp
  norm_num

/-! ## The logarithmic bound is too small -/

/-- `log x <= x / e` for `x > 0`. -/
lemma log_le_div_e {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx (Real.exp_pos 1))
  rw [Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

lemma sqrt_two_lt_three_halves : √2 < 3 / 2 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

/-- `sqrt 2 * log n < n` for `n >= 1` (natural logarithm). -/
theorem sqrt_two_mul_log_lt {n : ℕ} (hn : 1 ≤ n) : √2 * Real.log n < n := by
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have he := Real.exp_one_gt_d9
  have hl := log_le_div_e hx
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hs := sqrt_two_lt_three_halves
  have hs0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have h1 : Real.log n * Real.exp 1 ≤ n := by
    rwa [le_div_iff₀ (Real.exp_pos 1)] at hl
  nlinarith

/-- `sqrt 2 * log_2 n < n` for `n >= 1`. -/
theorem sqrt_two_mul_logb_lt {n : ℕ} (hn : 1 ≤ n) : √2 * Real.logb 2 n < n := by
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have he := Real.exp_one_gt_d9
  have h2 := Real.log_two_gt_d9
  have hl := log_le_div_e hx
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hs := sqrt_two_lt_three_halves
  have hs0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have h1 : Real.log n * Real.exp 1 ≤ n := by
    rwa [le_div_iff₀ (Real.exp_pos 1)] at hl
  have hlog2 : 0 < Real.log 2 := by linarith
  rw [Real.logb, mul_div_assoc', div_lt_iff₀ hlog2]
  have hel : √2 < Real.exp 1 * Real.log 2 := by
    nlinarith [mul_lt_mul'' he h2 (by norm_num) (by norm_num)]
  rcases eq_or_lt_of_le hn with h1n | h2n
  · subst h1n; simp; exact hlog2
  · have hpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast h2n)
    have s1 : √2 * Real.log n < Real.exp 1 * Real.log 2 * Real.log n :=
      mul_lt_mul_of_pos_right hel hpos
    nlinarith

/-- For every constant `C`, `C * log n < n` for all large `n`. -/
lemma const_mul_log_lt (C : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * Real.log n < n := by
  refine ⟨⌈(2 * |C| + 1) ^ 2⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : (⌈(2 * |C| + 1) ^ 2⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hceil := Nat.le_ceil ((2 * |C| + 1) ^ 2)
  have hbig : (2 * |C| + 1) ^ 2 < (n : ℝ) := by linarith
  have hx : (0 : ℝ) < n := by nlinarith [abs_nonneg C]
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by
    have : (1 : ℝ) ≤ (2 * |C| + 1) ^ 2 := by nlinarith [abs_nonneg C]
    linarith)
  -- `log n <= 2 * sqrt n`
  have hrp := Real.log_le_rpow_div hx.le (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow, div_div_eq_mul_div, div_one] at hrp
  have hsq : 2 * |C| + 1 < √n := by
    rw [show 2 * |C| + 1 = √((2 * |C| + 1) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt (by positivity) hbig
  have hsn : √n * √n = n := Real.mul_self_sqrt hx.le
  have hC : C * Real.log n ≤ |C| * Real.log n :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
  nlinarith [abs_nonneg C, Real.sqrt_nonneg (n : ℝ)]

/-! ## A second witness: AND, a linear threshold function -/

/-- The AND function: `true` iff every input bit is `true`. -/
def andFun (n : ℕ) : BoolFun n := fun x => decide (∀ i, x i = true)

/-- `f` is a linear threshold function: `f(x) = [theta <= sum_i w_i x_i]` for some real weights
`w` and threshold `theta` (bits read as `0/1`). -/
def IsLTF {n : ℕ} (f : BoolFun n) : Prop :=
  ∃ (w : Fin n → ℝ) (θ : ℝ), ∀ x, f x = decide (θ ≤ ∑ i, w i * (if x i then (1 : ℝ) else 0))

/-- AND is a linear threshold function: weights `1`, threshold `n`. -/
theorem andFun_threshold (n : ℕ) (x : Fin n → Bool) :
    andFun n x = decide ((n : ℝ) ≤ ∑ i, (if x i then (1 : ℝ) else 0)) := by
  have hle : ∀ i ∈ (univ : Finset (Fin n)), (if x i then (1 : ℝ) else 0) ≤ 1 :=
    fun i _ => by split_ifs <;> norm_num
  have key : (n : ℝ) ≤ ∑ i, (if x i then (1 : ℝ) else 0) ↔ ∀ i, x i = true := by
    constructor
    · intro h i
      by_contra hi
      have hlt := Finset.sum_lt_sum hle ⟨i, mem_univ i, by simp [hi]⟩
      rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hlt
      linarith
    · intro h
      simp [h]
  simp only [andFun, key]

/-- AND on `n` bits has sensitivity `n` (attained at the all-`true` input). -/
theorem andFun_sensitivity (n : ℕ) : sensitivity (andFun n) = n := by
  refine le_antisymm (Finset.sup_le fun x _ => ?_) ?_
  · exact (Finset.card_filter_le _ _).trans (by simp)
  · refine le_trans (le_of_eq ?_) (Finset.le_sup (f := sensAt (andFun n)) (mem_univ fun _ => true))
    unfold sensAt
    rw [Finset.filter_true_of_mem fun i _ => ?_]
    · simp
    · simp only [andFun, flipBit]
      intro h
      have := of_decide_eq_true (h.trans (by simp))
      simpa using this i

lemma abs_chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : |chi S x| = 1 := by
  rw [chi, Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ => by cases x i <;> simp [sgn]

lemma sum_zo_and_chi {n : ℕ} (S : Finset (Fin n)) :
    ∑ x, zoEnc (andFun n) x * chi S x = chi S fun _ => true := by
  rw [Finset.sum_eq_single (fun _ => true)]
  · simp [zoEnc, andFun]
  · intro x _ hx
    have : ¬ ∀ i, x i = true := fun h => hx (funext h)
    simp [zoEnc, andFun, this]
  · simp

/-- The spectral norm of the `0/1` AND is `1`. -/
theorem spectralNorm_zo_and (n : ℕ) : spectralNorm (zoEnc (andFun n)) = 1 := by
  unfold spectralNorm fourierCoeff
  simp only [sum_zo_and_chi, abs_div, abs_chi, abs_pow, abs_two, sum_const, card_univ,
    Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- The spectral norm of `(-1)^{AND}` is at most `3`. -/
theorem spectralNorm_pm_and_le (n : ℕ) : spectralNorm (pmEnc (andFun n)) ≤ 3 := by
  have hpm : ∀ S, fourierCoeff (pmEnc (andFun n)) S =
      (∑ x, chi S x) / 2 ^ n - 2 * fourierCoeff (zoEnc (andFun n)) S := by
    intro S
    unfold fourierCoeff
    rw [mul_div_assoc', ← sub_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold pmEnc zoEnc sgn
    cases andFun n x <;> norm_num
    ring
  have h1 : ∑ S : Finset (Fin n), |(∑ x, chi S x) / 2 ^ n| = 1 := by
    simp only [sum_chi]
    rw [Finset.sum_congr rfl (g := fun S => if S = ∅ then (1 : ℝ) else 0)
      (fun S _ => by split_ifs <;> simp)]
    simp
  have h2 := spectralNorm_zo_and n
  unfold spectralNorm at h2 ⊢
  calc ∑ S, |fourierCoeff (pmEnc (andFun n)) S|
      ≤ ∑ S : Finset (Fin n), (|(∑ x, chi S x) / 2 ^ n| +
          2 * |fourierCoeff (zoEnc (andFun n)) S|) := by
        refine Finset.sum_le_sum fun S _ => ?_
        rw [hpm]
        refine (abs_sub _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_two]
    _ = 3 := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]; norm_num

/-! ## Main theorems -/

/-- The first clause of the conjecture, for a chosen logarithm `L` and output encoding `enc`:
for every `n >= 2` and every Boolean function `f` on `n` bits, `s(f) <= sqrt 2 * L n * ||fhat||_1`.
(Restricting to `n >= 2` only weakens the clause, avoiding the degenerate `log 1 = 0`.) -/
def FirstClause (L : ℝ → ℝ) (enc : ∀ {n : ℕ}, BoolFun n → (Fin n → Bool) → ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ f : BoolFun n, (sensitivity f : ℝ) ≤ √2 * L n * spectralNorm (enc f)

/-- For every `n >= 1`, parity on `n` bits violates the bound, for both logarithms
(`ln`, `log_2`) and both output encodings (`+-1`, `0/1`). -/
theorem parity_violates (n : ℕ) (hn : 1 ≤ n) :
    √2 * Real.log n * spectralNorm (pmEnc (parity n)) < sensitivity (parity n) ∧
    √2 * Real.logb 2 n * spectralNorm (pmEnc (parity n)) < sensitivity (parity n) ∧
    √2 * Real.log n * spectralNorm (zoEnc (parity n)) < sensitivity (parity n) ∧
    √2 * Real.logb 2 n * spectralNorm (zoEnc (parity n)) < sensitivity (parity n) := by
  rw [spectralNorm_pm_parity, spectralNorm_zo_parity hn, parity_sensitivity]
  simp only [mul_one]
  exact ⟨sqrt_two_mul_log_lt hn, sqrt_two_mul_logb_lt hn, sqrt_two_mul_log_lt hn,
    sqrt_two_mul_logb_lt hn⟩

/-- Conjecture 00000002181 is false: its first clause fails for the natural logarithm and for
`log_2`, with either output encoding (witness: parity on `n` bits, any `n >= 2`). -/
theorem conjecture_2181_false :
    ¬ FirstClause Real.log pmEnc ∧ ¬ FirstClause (Real.logb 2) pmEnc ∧
    ¬ FirstClause Real.log zoEnc ∧ ¬ FirstClause (Real.logb 2) zoEnc := by
  have h := parity_violates 2 (by norm_num)
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · exact absurd (hc 2 le_rfl (parity 2)) (not_le.mpr h.1)
  · exact absurd (hc 2 le_rfl (parity 2)) (not_le.mpr h.2.1)
  · exact absurd (hc 2 le_rfl (parity 2)) (not_le.mpr h.2.2.1)
  · exact absurd (hc 2 le_rfl (parity 2)) (not_le.mpr h.2.2.2)

/-- No bound `s(f) <= C * log n * ||fhat||_1` holds, for any constant `C` (hence for any
logarithm base): parity violates it for all large `n`, in both encodings. -/
theorem no_log_bound (C : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    C * Real.log n * spectralNorm (pmEnc (parity n)) < sensitivity (parity n) ∧
    C * Real.log n * spectralNorm (zoEnc (parity n)) < sensitivity (parity n) := by
  obtain ⟨N, hN⟩ := const_mul_log_lt C
  refine ⟨N + 1, fun n hn => ?_⟩
  rw [spectralNorm_pm_parity, spectralNorm_zo_parity (by omega), parity_sensitivity]
  simp only [mul_one]
  exact ⟨hN n (by omega), hN n (by omega)⟩

/-- AND is a linear threshold function. -/
theorem andFun_isLTF (n : ℕ) : IsLTF (andFun n) :=
  ⟨fun _ => 1, n, fun x => by simpa using andFun_threshold n x⟩

/-- Even on linear threshold functions no bound `s(f) <= C * log n * ||fhat||_1` holds, for any
constant `C` (so for any logarithm base, as `log_b n = log n / log b`): AND violates it for all
large `n`, in both encodings. -/
theorem and_no_log_bound (C : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    C * Real.log n * spectralNorm (pmEnc (andFun n)) < sensitivity (andFun n) ∧
    C * Real.log n * spectralNorm (zoEnc (andFun n)) < sensitivity (andFun n) := by
  obtain ⟨N, hN⟩ := const_mul_log_lt (3 * |C|)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have h3 := hN n (by omega)
  have hsn : 0 ≤ spectralNorm (pmEnc (andFun n)) := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hle := spectralNorm_pm_and_le n
  have hC : C * Real.log n ≤ |C| * Real.log n := mul_le_mul_of_nonneg_right (le_abs_self C) hlog
  have hCl : 0 ≤ |C| * Real.log n := mul_nonneg (abs_nonneg C) hlog
  rw [spectralNorm_zo_and, andFun_sensitivity, mul_one]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hle hCl, mul_le_mul_of_nonneg_right hC hsn]

end C2181
