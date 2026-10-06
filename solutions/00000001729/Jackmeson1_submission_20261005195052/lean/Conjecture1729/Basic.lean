import Mathlib

/-!
# Conjecture 00000001729: Campana points of `(P¹, ½[0] + ½[1] + ½[∞])`

The conjecture claims that the number of Campana points of the orbifold `(P¹, 2[0]+2[1]+2[∞])`
(multiplicity 2 at `0`, `1`, `∞`, i.e. `Δ = ½[0] + ½[1] + ½[∞]`) of height at most `B` is
`c · √B / √(log B)`.

A point of `P¹(ℚ)` off the support `{0, 1, ∞}` is a rational `x ≠ 0, 1`.  Writing `x = a / b` in lowest
terms (`a = x.num`, `b = x.den > 0`), its `p`-adic intersection numbers with `[0]`, `[∞]`, `[1]` on the
standard model `P¹_ℤ` are `v_p(a)`, `v_p(b)`, `v_p(a - b)`; the Campana condition for multiplicity 2 is
that each of them is `0` or at least `2`.  The naive height is `H(a/b) = max(|a|, b)`.

We prove `N(64 K⁴) ≥ K² / 2` for every `K` (from primitive Pythagorean triples), hence
`N(B)` is not `O(√B / √(log B))`; this refutes the exact, the asymptotic (`~ c √B/√log B`) and the
order-of-magnitude readings, for the naive height and for every height `H^κ`, `0 < κ ≤ 1`
(this includes the orbifold anticanonical height `H^{1/2}`).
-/

open Filter Asymptotics Finset Real

namespace C1729

/-- Campana condition of multiplicity `2` for the integer `n` at every prime: the `p`-adic valuation of
`n` is `0` or at least `2`. -/
def Mult2 (n : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → padicValInt p n = 0 ∨ 2 ≤ padicValInt p n

/-- `x ∈ P¹(ℚ) \ {0, 1, ∞}` is a Campana point of `(P¹, ½[0] + ½[1] + ½[∞])` (model `P¹_ℤ`):
with `x = a / b` in lowest terms (`a = x.num`, `b = x.den > 0`), the intersection numbers
`v_p(a)` (with `[0]`), `v_p(b)` (with `[∞]`) and `v_p(a - b)` (with `[1]`) are each `0` or `≥ 2`. -/
def IsCampanaPoint (x : ℚ) : Prop :=
  x ≠ 0 ∧ x ≠ 1 ∧ Mult2 x.num ∧ Mult2 (x.den : ℤ) ∧ Mult2 (x.num - x.den)

/-- Naive height on `P¹(ℚ)`: `H(a / b) = max(|a|, b)` for `a / b` in lowest terms. -/
def height (x : ℚ) : ℕ := max x.num.natAbs x.den

/-- `N(B)`: the number of Campana points of naive height at most `B`. -/
noncomputable def campanaCount (B : ℝ) : ℕ :=
  Set.ncard {x : ℚ | IsCampanaPoint x ∧ (height x : ℝ) ≤ B}

/-- The count for the height `H^κ`: Campana points with `H(x)^κ ≤ B`. -/
noncomputable def campanaCountPow (κ B : ℝ) : ℕ :=
  Set.ncard {x : ℚ | IsCampanaPoint x ∧ (height x : ℝ) ^ κ ≤ B}

/-! ### Finiteness and comparison of heights -/

lemma finite_height_le (B : ℝ) : {x : ℚ | (height x : ℝ) ≤ B}.Finite := by
  refine (((Finset.Icc (-(⌊B⌋₊ : ℤ)) ⌊B⌋₊) ×ˢ (Finset.Icc (0 : ℤ) ⌊B⌋₊)).image
    (fun p : ℤ × ℤ => (p.1 : ℚ) / p.2)).finite_toSet.subset ?_
  intro x hx
  simp only [Set.mem_ofPred_eq, height, Nat.cast_max] at hx
  have h1 : x.num.natAbs ≤ ⌊B⌋₊ := Nat.le_floor ((le_max_left _ _).trans hx)
  have h2 : x.den ≤ ⌊B⌋₊ := Nat.le_floor ((le_max_right _ _).trans hx)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
  exact ⟨(x.num, x.den), ⟨⟨by omega, by omega⟩, by omega, by omega⟩, Rat.num_div_den x⟩

lemma finite_pow (κ B : ℝ) (hκ : 0 < κ) :
    {x : ℚ | IsCampanaPoint x ∧ (height x : ℝ) ^ κ ≤ B}.Finite := by
  refine (finite_height_le (B ^ κ⁻¹)).subset ?_
  rintro x ⟨-, hx⟩
  have h0 : (0 : ℝ) ≤ height x := Nat.cast_nonneg _
  have := Real.rpow_le_rpow (Real.rpow_nonneg h0 κ) hx (inv_nonneg.2 hκ.le)
  rwa [Real.rpow_rpow_inv h0 hκ.ne'] at this

lemma count_le_countPow (κ B : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hB : 1 ≤ B) :
    campanaCount B ≤ campanaCountPow κ B := by
  apply Set.ncard_le_ncard _ (finite_pow κ B hκ)
  rintro x ⟨hc, hx⟩
  refine ⟨hc, ?_⟩
  calc (height x : ℝ) ^ κ ≤ B ^ κ := Real.rpow_le_rpow (Nat.cast_nonneg _) hx hκ.le
    _ ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB hκ1
    _ = B := Real.rpow_one B

/-! ### The Pythagorean family -/

lemma mult2_sq {k : ℤ} (hk : k ≠ 0) : Mult2 (k ^ 2) := by
  intro p hp
  have := Fact.mk hp
  rw [sq, padicValInt.mul hk hk]
  omega

/-- The rational point `(m² + n²)² / (m² - n²)²`; then `x - 1 = (2mn)² / (m² - n²)²`. -/
noncomputable def pt (m n : ℤ) : ℚ :=
  (((m ^ 2 + n ^ 2) ^ 2 : ℤ) : ℚ) / (((m ^ 2 - n ^ 2) ^ 2 : ℤ) : ℚ)

lemma sub_ne_zero_of_parity {m n : ℤ} (hm : m % 2 = 1) (hn : n % 2 = 0) : m ^ 2 - n ^ 2 ≠ 0 := by
  have ho : Odd (m ^ 2 - n ^ 2) :=
    ((Int.odd_iff.2 hm).pow).sub_even ((Int.even_iff.2 hn).pow_of_ne_zero two_ne_zero)
  intro h
  rw [h] at ho
  exact (Int.not_even_iff_odd.2 ho) (Int.even_iff.2 rfl)

lemma pt_num_den {m n : ℤ} (hco : Int.gcd m n = 1) (hm : m % 2 = 1) (hn : n % 2 = 0) :
    (pt m n).num = (m ^ 2 + n ^ 2) ^ 2 ∧ ((pt m n).den : ℤ) = (m ^ 2 - n ^ 2) ^ 2 := by
  have hpt := (PythagoreanTriple.coprime_classification (x := m ^ 2 - n ^ 2) (y := 2 * m * n)
    (z := m ^ 2 + n ^ 2)).2 ⟨m, n, Or.inl ⟨rfl, rfl⟩, Or.inl rfl, hco, Or.inr ⟨hm, hn⟩⟩
  have h1 : IsCoprime (m ^ 2 - n ^ 2) (2 * m * n) := Int.isCoprime_iff_gcd_eq_one.2 hpt.2
  have h2 : IsCoprime ((m ^ 2 - n ^ 2) ^ 2) ((m ^ 2 + n ^ 2) ^ 2) := by
    have := (h1.pow (m := 2) (n := 2)).add_mul_left_right 1
    rwa [show (2 * m * n) ^ 2 + (m ^ 2 - n ^ 2) ^ 2 * 1 = (m ^ 2 + n ^ 2) ^ 2 by ring] at this
  have h3 : IsCoprime ((m ^ 2 + n ^ 2) ^ 2) ((m ^ 2 - n ^ 2) ^ 2) :=
    ((IsCoprime.pow_iff two_pos two_pos).1 h2).symm.pow
  have hpos : 0 < (m ^ 2 - n ^ 2) ^ 2 := by
    have := sub_ne_zero_of_parity hm hn
    positivity
  have hcop : Nat.Coprime ((m ^ 2 + n ^ 2) ^ 2).natAbs ((m ^ 2 - n ^ 2) ^ 2).natAbs := by
    have := Int.isCoprime_iff_gcd_eq_one.1 h3
    rwa [Int.gcd_eq_natAbs] at this
  exact ⟨Rat.num_div_eq_of_coprime hpos hcop, Rat.den_div_eq_of_coprime hpos hcop⟩

lemma pt_campana {m n : ℤ} (hco : Int.gcd m n = 1) (hm : m % 2 = 1) (hn : n % 2 = 0)
    (hn0 : n ≠ 0) : IsCampanaPoint (pt m n) := by
  obtain ⟨hnum, hden⟩ := pt_num_den hco hm hn
  have hm0 : m ≠ 0 := by omega
  have hs : m ^ 2 + n ^ 2 ≠ 0 := by positivity
  have hd := sub_ne_zero_of_parity hm hn
  have hmn : 2 * m * n ≠ 0 := by positivity
  have hid : (m ^ 2 + n ^ 2) ^ 2 - (m ^ 2 - n ^ 2) ^ 2 = (2 * m * n) ^ 2 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, Rat.num_zero] at hnum
    exact hs (pow_eq_zero_iff two_ne_zero |>.1 hnum.symm)
  · intro h
    rw [h, Rat.num_one] at hnum
    rw [h, Rat.den_one] at hden
    have : (2 * m * n) ^ 2 = 0 := by rw [← hid, ← hnum, ← hden]; norm_num
    exact hmn (pow_eq_zero_iff two_ne_zero |>.1 this)
  · rw [hnum]; exact mult2_sq hs
  · rw [hden]; exact mult2_sq hd
  · rw [hnum, hden, hid]; exact mult2_sq hmn

lemma pt_height {m n : ℤ} (hco : Int.gcd m n = 1) (hm : m % 2 = 1) (hn : n % 2 = 0)
    (L : ℤ) (hL : m ^ 2 + n ^ 2 ≤ L) : ((height (pt m n) : ℤ) : ℝ) ≤ (L : ℝ) ^ 2 := by
  obtain ⟨hnum, hden⟩ := pt_num_den hco hm hn
  have hle : (height (pt m n) : ℤ) ≤ L ^ 2 := by
    simp only [height, Nat.cast_max, Int.natCast_natAbs, hnum, hden, max_le_iff]
    have h0 : 0 ≤ m ^ 2 + n ^ 2 := by positivity
    constructor
    · rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ h0 hL 2
    · nlinarith [sq_nonneg m, sq_nonneg n, sq_nonneg (m * n), pow_le_pow_left₀ h0 hL 2]
  exact_mod_cast hle

lemma sq_inj_of_pos {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  have := (sq_eq_sq_iff_abs_eq_abs a b).1 h
  rwa [abs_of_nonneg ha, abs_of_nonneg hb] at this

lemma pt_inj {m n m' n' : ℤ} (hm : 0 < m) (hn : 0 < n) (hm' : 0 < m') (hn' : 0 < n')
    (hpm : m % 2 = 1) (hpn : n % 2 = 0) (hpm' : m' % 2 = 1) (hpn' : n' % 2 = 0)
    (hco : Int.gcd m n = 1) (hco' : Int.gcd m' n' = 1) (h : pt m n = pt m' n') :
    m = m' ∧ n = n' := by
  obtain ⟨h1, h2⟩ := pt_num_den hco hpm hpn
  obtain ⟨h1', h2'⟩ := pt_num_den hco' hpm' hpn'
  have es : m ^ 2 + n ^ 2 = m' ^ 2 + n' ^ 2 :=
    sq_inj_of_pos (by positivity) (by positivity) (by rw [← h1, ← h1', h])
  have ed : (m ^ 2 - n ^ 2) ^ 2 = (m' ^ 2 - n' ^ 2) ^ 2 := by rw [← h2, ← h2', h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 ed with e | e
  · have e1 : m ^ 2 = m' ^ 2 := by linarith
    have e2 : n ^ 2 = n' ^ 2 := by linarith
    exact ⟨sq_inj_of_pos hm.le hm'.le e1, sq_inj_of_pos hn.le hn'.le e2⟩
  · have e1 : m ^ 2 = n' ^ 2 := by linarith
    have := sq_inj_of_pos hm.le hn'.le e1
    omega

/-! ### Counting coprime pairs `(2i + 1, 2j)` -/

lemma sum_inv_sq_odd (E : ℕ) :
    ∑ e ∈ range E, (1 : ℝ) / ((2 * e + 3 : ℝ) ^ 2) ≤ 1 / 4 - 1 / (4 * ((E : ℝ) + 1)) := by
  induction E with
  | zero => norm_num
  | succ E ih =>
    rw [sum_range_succ]
    have h : (1 : ℝ) / ((2 * E + 3) ^ 2) ≤ 1 / (4 * ((E : ℝ) + 1)) - 1 / (4 * ((E : ℝ) + 1 + 1)) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast
    linarith

/-- The pairs `(i, j)` with `i < K`, `1 ≤ j ≤ K` and `gcd(2i + 1, 2j) = 1`. -/
def good (K : ℕ) : Finset (ℕ × ℕ) :=
  ((range K) ×ˢ (Icc 1 K)).filter (fun ij => Nat.Coprime (2 * ij.1 + 1) (2 * ij.2))

lemma card_good (K : ℕ) : (K : ℝ) ^ 2 / 2 ≤ (good K).card := by
  set T := (range K) ×ˢ (Icc 1 K)
  set Bad := T.filter (fun ij : ℕ × ℕ => ¬ Nat.Coprime (2 * ij.1 + 1) (2 * ij.2))
  have hsplit : (good K).card + Bad.card = K * K := by
    have := card_filter_add_card_filter_not
      (s := T) (fun ij : ℕ × ℕ => Nat.Coprime (2 * ij.1 + 1) (2 * ij.2))
    simp only [good, Bad]
    rw [this]
    simp [T]
  let A : ℕ → Finset (ℕ × ℕ) := fun e =>
    ((range K).filter (fun i => (2 * e + 3) ∣ 2 * i + 1)) ×ˢ
      ((Icc 1 K).filter (fun j => (2 * e + 3) ∣ 2 * j))
  have hsub : Bad ⊆ (range K).biUnion A := by
    intro ij hij
    simp only [Bad, T, mem_filter, mem_product, mem_range, mem_Icc] at hij
    obtain ⟨⟨hi, hj1, hjK⟩, hnc⟩ := hij
    have hg1 : Nat.gcd (2 * ij.1 + 1) (2 * ij.2) ∣ 2 * ij.1 + 1 := Nat.gcd_dvd_left _ _
    have hg2 : Nat.gcd (2 * ij.1 + 1) (2 * ij.2) ∣ 2 * ij.2 := Nat.gcd_dvd_right _ _
    have hodd : Odd (Nat.gcd (2 * ij.1 + 1) (2 * ij.2)) := Odd.of_dvd_nat ⟨ij.1, by ring⟩ hg1
    have hgle : Nat.gcd (2 * ij.1 + 1) (2 * ij.2) ≤ 2 * ij.2 := Nat.le_of_dvd (by omega) hg2
    have hne : Nat.gcd (2 * ij.1 + 1) (2 * ij.2) ≠ 1 := hnc
    obtain ⟨t, ht⟩ := hodd
    have hd : 2 * (t - 1) + 3 = Nat.gcd (2 * ij.1 + 1) (2 * ij.2) := by omega
    simp only [A, mem_biUnion, mem_range, mem_product, mem_filter, mem_Icc]
    exact ⟨t - 1, by omega, ⟨hi, hd ▸ hg1⟩, ⟨hj1, hjK⟩, hd ▸ hg2⟩
  have hcard : ∀ e ∈ range K, ((A e).card : ℝ) ≤ 2 * (K : ℝ) ^ 2 / ((2 * e + 3 : ℝ) ^ 2) := by
    intro e _
    have h1 : ((range K).filter (fun i => (2 * e + 3) ∣ 2 * i + 1)).card ≤ (2 * K) / (2 * e + 3) := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div]
      apply card_le_card_of_injOn (fun i => 2 * i + 1)
      · intro i hi
        simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_Ioc] at hi ⊢
        exact ⟨⟨by omega, by omega⟩, hi.2⟩
      · intro a _ b _ h
        simp only at h
        omega
    have h2 : ((Icc 1 K).filter (fun j => (2 * e + 3) ∣ 2 * j)).card ≤ K / (2 * e + 3) := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div]
      apply card_le_card
      intro j hj
      simp only [mem_filter, mem_Icc, mem_Ioc] at hj ⊢
      refine ⟨⟨by omega, hj.1.2⟩, ?_⟩
      have hcop : Nat.Coprime (2 * e + 3) 2 := by
        rw [Nat.coprime_two_right]; exact ⟨e + 1, by ring⟩
      exact (Nat.Coprime.dvd_mul_left hcop).1 hj.2
    have hd : (0 : ℝ) < 2 * e + 3 := by positivity
    simp only [A, card_product]
    calc (((range K).filter (fun i => (2 * e + 3) ∣ 2 * i + 1)).card *
          ((Icc 1 K).filter (fun j => (2 * e + 3) ∣ 2 * j)).card : ℕ)
        ≤ (((2 * K) / (2 * e + 3) : ℕ) : ℝ) * ((K / (2 * e + 3) : ℕ) : ℝ) := by
          push_cast [← Nat.cast_mul]; exact_mod_cast Nat.mul_le_mul h1 h2
      _ ≤ ((2 * K : ℕ) / (2 * e + 3 : ℕ) : ℝ) * ((K : ℝ) / (2 * e + 3 : ℕ)) := by
          gcongr
          · exact Nat.cast_div_le
          · exact Nat.cast_div_le
      _ = 2 * (K : ℝ) ^ 2 / ((2 * e + 3 : ℝ) ^ 2) := by push_cast; field_simp
  have hBad : (Bad.card : ℝ) ≤ (K : ℝ) ^ 2 / 2 := by
    calc (Bad.card : ℝ) ≤ ((range K).biUnion A).card := by exact_mod_cast card_le_card hsub
      _ ≤ ∑ e ∈ range K, ((A e).card : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ e ∈ range K, 2 * (K : ℝ) ^ 2 / ((2 * e + 3 : ℝ) ^ 2) := sum_le_sum hcard
      _ = 2 * (K : ℝ) ^ 2 * ∑ e ∈ range K, 1 / ((2 * e + 3 : ℝ) ^ 2) := by
          rw [mul_sum]; congr 1; ext e; ring
      _ ≤ 2 * (K : ℝ) ^ 2 * (1 / 4) := by
          gcongr
          have : (0 : ℝ) ≤ 1 / (4 * ((K : ℝ) + 1)) := by positivity
          linarith [sum_inv_sq_odd K]
      _ = (K : ℝ) ^ 2 / 2 := by ring
  have : ((good K).card : ℝ) + Bad.card = K * K := by exact_mod_cast hsplit
  nlinarith

/-! ### The lower bound `N(64 K⁴) ≥ K² / 2` -/

/-- For every `K`, at least `K² / 2` Campana points have naive height `≤ 64 K⁴`; i.e.
`N(B) ≥ √B / 16` along `B = 64 K⁴`. -/
theorem campanaCount_lower (K : ℕ) : (K : ℝ) ^ 2 / 2 ≤ campanaCount (64 * (K : ℝ) ^ 4) := by
  let f : ℕ × ℕ → ℚ := fun ij => pt (2 * (ij.1 : ℤ) + 1) (2 * (ij.2 : ℤ))
  have hmem : ∀ ij ∈ good K, ij.1 < K ∧ 1 ≤ ij.2 ∧ ij.2 ≤ K ∧
      Int.gcd (2 * (ij.1 : ℤ) + 1) (2 * (ij.2 : ℤ)) = 1 := by
    intro ij hij
    simp only [good, mem_filter, mem_product, mem_range, mem_Icc] at hij
    refine ⟨hij.1.1, hij.1.2.1, hij.1.2.2, ?_⟩
    have := hij.2
    rw [show 2 * (ij.1 : ℤ) + 1 = ((2 * ij.1 + 1 : ℕ) : ℤ) by push_cast; ring,
      show 2 * (ij.2 : ℤ) = ((2 * ij.2 : ℕ) : ℤ) by push_cast; ring, Int.gcd_natCast_natCast]
    exact this
  have hinj : Set.InjOn f (good K) := by
    intro a ha b hb h
    obtain ⟨-, ha1, -, hac⟩ := hmem a ha
    obtain ⟨-, hb1, -, hbc⟩ := hmem b hb
    have := pt_inj (by positivity) (by omega) (by positivity) (by omega) (by omega) (by omega)
      (by omega) (by omega) hac hbc h
    exact Prod.ext (by omega) (by omega)
  have hsub : (((good K).image f : Finset ℚ) : Set ℚ) ⊆
      {x : ℚ | IsCampanaPoint x ∧ (height x : ℝ) ≤ 64 * (K : ℝ) ^ 4} := by
    intro x hx
    simp only [coe_image, Set.mem_image, mem_coe] at hx
    obtain ⟨ij, hij, rfl⟩ := hx
    obtain ⟨hi, hj1, hjK, hco⟩ := hmem ij hij
    refine ⟨pt_campana hco (by omega) (by omega) (by omega), ?_⟩
    have := pt_height hco (by omega) (by omega) (8 * (K : ℤ) ^ 2) (by
      have hi' : (ij.1 : ℤ) + 1 ≤ K := by exact_mod_cast hi
      have hj' : (ij.2 : ℤ) ≤ K := by exact_mod_cast hjK
      nlinarith)
    have e : (((height (f ij) : ℤ) : ℝ)) = (height (f ij) : ℝ) := by norm_cast
    rw [e] at this
    push_cast at this
    linarith
  have := Set.ncard_le_ncard hsub ((finite_height_le _).subset fun x hx => hx.2)
  rw [Set.ncard_coe_finset, card_image_of_injOn hinj] at this
  calc (K : ℝ) ^ 2 / 2 ≤ (good K).card := card_good K
    _ ≤ campanaCount (64 * (K : ℝ) ^ 4) := Nat.cast_le.2 this

/-! ### The asymptotic statements -/

lemma not_isBigO_of_lower {f : ℝ → ℝ} (hf : ∀ K : ℕ, 1 ≤ K → (K : ℝ) ^ 2 / 2 ≤ f (64 * (K : ℝ) ^ 4)) :
    ¬ f =O[atTop] (fun B => √B / √(log B)) := by
  intro h
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨B0, hB0⟩ := eventually_atTop.1 hc
  set K : ℕ := ⌈max (exp (256 * c ^ 2)) B0⌉₊ + 1 with hKdef
  have hK1 : max (exp (256 * c ^ 2)) B0 < K := by
    have := Nat.le_ceil (max (exp (256 * c ^ 2)) B0)
    rw [hKdef]; push_cast; linarith
  have hK : (1 : ℝ) ≤ K := by rw [hKdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈max (exp (256 * c ^ 2)) B0⌉₊]
  have hK4 : (K : ℝ) ≤ 64 * (K : ℝ) ^ 4 := by nlinarith [pow_le_pow_right₀ hK (show 1 ≤ 4 by norm_num)]
  have hB : 64 * (K : ℝ) ^ 4 ≥ B0 := by linarith [le_max_right (exp (256 * c ^ 2)) B0]
  have hbd := hB0 _ hB
  have hsqrt : √(64 * (K : ℝ) ^ 4) = 8 * (K : ℝ) ^ 2 := by
    rw [show (64 * (K : ℝ) ^ 4) = (8 * (K : ℝ) ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hlog : 256 * c ^ 2 < log (64 * (K : ℝ) ^ 4) := by
    have h1 : 256 * c ^ 2 < log K :=
      (Real.lt_log_iff_exp_lt (by linarith)).2 (lt_of_le_of_lt (le_max_left _ _) hK1)
    have h2 : log K ≤ log (64 * (K : ℝ) ^ 4) := Real.log_le_log (by linarith) hK4
    linarith
  set s := √(log (64 * (K : ℝ) ^ 4)) with hs_def
  have hs : 16 * |c| < s := by
    rw [show 16 * |c| = √((16 * |c|) ^ 2) by rw [Real.sqrt_sq (by positivity)], hs_def]
    apply Real.sqrt_lt_sqrt (by positivity)
    rw [mul_pow, sq_abs]
    linarith
  have hspos : 0 < s := lt_of_le_of_lt (by positivity) hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hsqrt,
    abs_of_pos (by positivity : 0 < 8 * (K : ℝ) ^ 2 / s)] at hbd
  have hKpos : 0 < (K : ℝ) ^ 2 := by positivity
  have hlow : (K : ℝ) ^ 2 / 2 ≤ c * (8 * (K : ℝ) ^ 2 / s) :=
    le_trans (hf K (by exact_mod_cast hK)) (le_trans (le_abs_self _) hbd)
  have hup : c * (8 * (K : ℝ) ^ 2 / s) < (K : ℝ) ^ 2 / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ hspos two_pos]
    nlinarith [le_abs_self c, mul_lt_mul_of_pos_right hs hKpos]
  linarith

/-- If `f` is not `O(g)`, then `f` is neither eventually equal to `c · g` nor asymptotic to `c · g`,
for any constant `c`. -/
lemma readings_of_not_isBigO {f g : ℝ → ℝ} (h : ¬ f =O[atTop] g) :
    (¬ ∃ c B0 : ℝ, ∀ B ≥ B0, f B = c * g B) ∧
      (∀ c : ℝ, ¬ f ~[atTop] (fun B => c * g B)) ∧ ¬ f =O[atTop] g := by
  have hg : ∀ c : ℝ, (fun B => c * g B) =O[atTop] g := fun c => isBigO_const_mul_self c g atTop
  refine ⟨?_, fun c hc => h (hc.isBigO.trans (hg c)), h⟩
  rintro ⟨c, B0, hB⟩
  exact h ((EventuallyEq.isBigO (eventually_atTop.2 ⟨B0, hB⟩)).trans (hg c))

/-- **Main theorem (naive height).** The Campana count `N(B)` of `(P¹, ½[0] + ½[1] + ½[∞])` is not of the
form `c √B / √(log B)`: it is not eventually equal to it (for any real `c`), not asymptotic to it (for any
real `c`), and not even `O(√B / √(log B))`. -/
theorem campana_count_disproof :
    (¬ ∃ c B0 : ℝ, ∀ B ≥ B0, (campanaCount B : ℝ) = c * (√B / √(log B))) ∧
      (∀ c : ℝ, ¬ (fun B => (campanaCount B : ℝ)) ~[atTop] (fun B => c * (√B / √(log B)))) ∧
      ¬ (fun B => (campanaCount B : ℝ)) =O[atTop] (fun B => √B / √(log B)) :=
  readings_of_not_isBigO (not_isBigO_of_lower fun K _ => campanaCount_lower K)

/-- **Main theorem (heights `H^κ`, `0 < κ ≤ 1`).** The same three statements for the count of Campana
points with `H(x)^κ ≤ B`; `κ = 1/2` is the orbifold anticanonical height (`-(K + Δ)` has degree `1/2`). -/
theorem campana_count_pow_disproof (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    (¬ ∃ c B0 : ℝ, ∀ B ≥ B0, (campanaCountPow κ B : ℝ) = c * (√B / √(log B))) ∧
      (∀ c : ℝ, ¬ (fun B => (campanaCountPow κ B : ℝ)) ~[atTop] (fun B => c * (√B / √(log B)))) ∧
      ¬ (fun B => (campanaCountPow κ B : ℝ)) =O[atTop] (fun B => √B / √(log B)) := by
  refine readings_of_not_isBigO (not_isBigO_of_lower fun K hK => ?_)
  refine (campanaCount_lower K).trans ?_
  have : (1 : ℝ) ≤ 64 * (K : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith [pow_le_pow_right₀ this (show 1 ≤ 4 by norm_num)]
  exact_mod_cast count_le_countPow κ _ hκ hκ1 this

end C1729
