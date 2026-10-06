import Mathlib

/-!
# Conjecture 00000002410: a non-Rajchman measure on a 1/2-dimensional homogeneous Cantor set

Statement: there exists a measure on a 1/2-dimensional homogeneous Cantor set whose Fourier
transform does not decay to zero; the construction uses x4-invariant (not x2) blocking.

Witness (classical): `cantor = {0.d₀d₁d₂… in base 4 : every dᵢ ∈ {0,3}}` (self-similar under
`x ↦ x/4`, `x ↦ x/4 + 3/4`, equal ratios), and `cantorMeasure`, the law of `∑ dᵢ 4^{-(i+1)}` for
i.i.d. fair digits `dᵢ ∈ {0,3}`. We prove `dimH cantor = 1/2`, `cantor ≃ₜ {0,1}^ℕ`,
`Re μ̂(4ⁿ) ≥ 1/8` (so `μ̂ ↛ 0`), and `μ` is invariant under `x ↦ 4x mod 1`, not under `x ↦ 2x mod 1`.
Fourier convention: `μ̂(ξ) = ∫ exp(-2πiξx) dμ(x)`.
-/

open MeasureTheory Filter Topology Set Real
open scoped ENNReal NNReal

namespace C2410

/-! ## The coding map and the Cantor set -/

/-- Digit map `{0,1} → {0,3} ⊆ Fin 4`. -/
def dig (e : Fin 2) : Fin 4 := if e = 0 then 0 else 3

/-- `code a = 0.d₀d₁d₂…` in base 4 with `dᵢ = dig (aᵢ) ∈ {0,3}` (Mathlib's `Real.ofDigits`). -/
noncomputable def code (a : ℕ → Fin 2) : ℝ := Real.ofDigits (fun i => dig (a i))

/-- The homogeneous Cantor set: reals `0.d₀d₁d₂…` (base 4) with all digits in `{0,3}`. -/
def cantor : Set ℝ := Real.ofDigits '' {d : ℕ → Fin 4 | ∀ i, d i = 0 ∨ d i = 3}

theorem cantor_eq_range : cantor = Set.range code := by
  ext x; constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨fun i => if d i = 0 then 0 else 1, ?_⟩
    unfold code; congr 1; funext i
    rcases hd i with h | h <;> simp [dig, h]
  · rintro ⟨a, rfl⟩
    refine ⟨_, fun i => ?_, rfl⟩
    simp only [dig]; split_ifs <;> simp

theorem code_split (a : ℕ → Fin 2) (n : ℕ) :
    code a = (∑ i ∈ Finset.range n, Real.ofDigitsTerm (fun i => dig (a i)) i)
      + ((4:ℝ) ^ n)⁻¹ * code (fun i => a (i + n)) := by
  simpa [code] using Real.ofDigits_eq_sum_add_ofDigits (fun i => dig (a i)) n

theorem code_nonneg (a : ℕ → Fin 2) : 0 ≤ code a := Real.ofDigits_nonneg _

theorem code_le_one (a : ℕ → Fin 2) : code a ≤ 1 := Real.ofDigits_le_one _

theorem code_head (a : ℕ → Fin 2) :
    code a = (if a 0 = 0 then 0 else 3 / 4) + 4⁻¹ * code (fun i => a (i + 1)) := by
  rw [code_split a 1]
  split_ifs with h <;> simp [Real.ofDigitsTerm, dig, h] <;> norm_num

theorem code_le_of_zero (a : ℕ → Fin 2) (h : a 0 = 0) : code a ≤ 1 / 4 := by
  rw [code_head, if_pos h]; have := code_le_one (fun i => a (i + 1)); linarith

theorem code_ge_of_one (a : ℕ → Fin 2) (h : a 0 ≠ 0) : 3 / 4 ≤ code a := by
  rw [code_head, if_neg h]; have := code_nonneg (fun i => a (i + 1)); linarith

theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

/-- The gap: no point of the Cantor set lies in `(1/4, 3/4)`. -/
theorem code_gap (a : ℕ → Fin 2) : code a ≤ 1 / 4 ∨ 3 / 4 ≤ code a :=
  (em (a 0 = 0)).imp (code_le_of_zero a) (code_ge_of_one a)

theorem code_sep0 (b b' : ℕ → Fin 2) (h : b 0 ≠ b' 0) : 1 / 2 ≤ |code b - code b'| := by
  rcases fin2_cases (b 0) with h0 | h0 <;> rcases fin2_cases (b' 0) with h1 | h1
  · exact absurd (h0.trans h1.symm) h
  · have := code_le_of_zero b h0; have := code_ge_of_one b' (by simp [h1])
    exact le_abs.2 (Or.inr (by linarith))
  · have := code_ge_of_one b (by simp [h0]); have := code_le_of_zero b' h1
    exact le_abs.2 (Or.inl (by linarith))
  · exact absurd (h0.trans h1.symm) h

/-- Two codings that first differ at index `n` give points at distance `≥ 4^{-n}/2`. -/
theorem code_sep (a a' : ℕ → Fin 2) (n : ℕ) (hlt : ∀ i < n, a i = a' i) (hn : a n ≠ a' n) :
    ((4:ℝ) ^ n)⁻¹ / 2 ≤ |code a - code a'| := by
  rw [code_split a n, code_split a' n]
  have hs : ∑ i ∈ Finset.range n, Real.ofDigitsTerm (fun i => dig (a i)) i =
      ∑ i ∈ Finset.range n, Real.ofDigitsTerm (fun i => dig (a' i)) i :=
    Finset.sum_congr rfl fun i hi => by
      simp [Real.ofDigitsTerm, hlt i (Finset.mem_range.mp hi)]
  rw [hs, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  have := code_sep0 (fun i => a (i + n)) (fun i => a' (i + n)) (by simpa using hn)
  have h4 : (0:ℝ) < ((4:ℝ) ^ n)⁻¹ := by positivity
  nlinarith

theorem exists_first_diff {a a' : ℕ → Fin 2} (h : a ≠ a') :
    ∃ n, (∀ i < n, a i = a' i) ∧ a n ≠ a' n := by
  classical
  have hex : ∃ n, a n ≠ a' n := by
    by_contra hc; exact h (funext fun n => not_not.1 fun hn => hc ⟨n, hn⟩)
  exact ⟨Nat.find hex, fun i hi => by simpa using Nat.find_min hex hi, Nat.find_spec hex⟩

theorem code_injective : Function.Injective code := fun a a' h => by_contra fun hne => by
  obtain ⟨n, hlt, hn⟩ := exists_first_diff hne
  have := code_sep a a' n hlt hn
  rw [h, sub_self, abs_zero] at this
  linarith [show (0:ℝ) < ((4:ℝ) ^ n)⁻¹ / 2 by positivity]

theorem code_continuous : Continuous code :=
  Real.continuous_ofDigits.comp (continuous_pi fun i =>
    (continuous_of_discreteTopology (f := dig)).comp (continuous_apply i))

/-! ## Topology: a homogeneous self-similar Cantor set -/

/-- `cantor` is homeomorphic to the Cantor space `{0,1}^ℕ`. -/
theorem cantor_homeomorph : Nonempty (cantor ≃ₜ (ℕ → Fin 2)) := by
  rw [cantor_eq_range]
  exact ⟨((code_continuous.isClosedEmbedding code_injective).isEmbedding.toHomeomorph).symm⟩

theorem isCompact_cantor : IsCompact cantor := by
  rw [cantor_eq_range]; exact isCompact_range code_continuous

/-- Self-similarity: `cantor = f₁(cantor) ∪ f₂(cantor)`, `f₁ x = x/4`, `f₂ x = x/4 + 3/4`. -/
theorem cantor_selfSimilar :
    cantor = (fun x => x / 4) '' cantor ∪ (fun x => x / 4 + 3 / 4) '' cantor := by
  rw [cantor_eq_range]; ext x; constructor
  · rintro ⟨a, rfl⟩
    rw [code_head a]
    by_cases h : a 0 = 0
    · left; exact ⟨code (fun i => a (i + 1)), ⟨_, rfl⟩, by rw [if_pos h]; ring⟩
    · right; exact ⟨code (fun i => a (i + 1)), ⟨_, rfl⟩, by rw [if_neg h]; ring⟩
  · rintro (⟨_, ⟨b, rfl⟩, rfl⟩ | ⟨_, ⟨b, rfl⟩, rfl⟩)
    · exact ⟨fun i => if i = 0 then 0 else b (i - 1), by rw [code_head]; simp; ring⟩
    · exact ⟨fun i => if i = 0 then 1 else b (i - 1), by rw [code_head]; simp; ring⟩

/-! ## Hausdorff dimension `1/2` -/

/-- Partial sum `∑_{i<n} dᵢ 4^{-(i+1)}`. -/
noncomputable def psum (b : ℕ → Fin 2) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, Real.ofDigitsTerm (fun j => dig (b j)) i

/-- Extend a finite word by zeros. -/
def ext (n : ℕ) (w : Fin n → Fin 2) : ℕ → Fin 2 := fun j => if h : j < n then w ⟨j, h⟩ else 0

/-- The level-`n` interval with prefix `w`, of length `4^{-n}`. -/
noncomputable def cell (n : ℕ) (w : Fin n → Fin 2) : Set ℝ :=
  Icc (psum (ext n w) n) (psum (ext n w) n + ((4:ℝ) ^ n)⁻¹)

theorem range_code_subset (n : ℕ) : Set.range code ⊆ ⋃ w, cell n w := by
  rintro _ ⟨a, rfl⟩
  refine mem_iUnion.2 ⟨fun i => a i, ?_⟩
  have hp : psum (ext n fun i => a i) n = psum a n :=
    Finset.sum_congr rfl fun i hi => by simp [Real.ofDigitsTerm, ext, Finset.mem_range.1 hi]
  have := code_split a n
  have h0 := code_nonneg (fun i => a (i + n)); have h1 := code_le_one (fun i => a (i + n))
  have h4 : (0:ℝ) < ((4:ℝ) ^ n)⁻¹ := by positivity
  rw [cell, hp]; unfold psum; constructor <;> nlinarith

theorem ediam_cell (n : ℕ) (w : Fin n → Fin 2) :
    Metric.ediam (cell n w) = ENNReal.ofReal ((4:ℝ) ^ n)⁻¹ := by
  rw [cell, Real.ediam_Icc, add_sub_cancel_left]

theorem four_pow (n : ℕ) : (4:ℝ) ^ n = ((2:ℝ) ^ n) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

theorem rpow_quarter (n : ℕ) : (((4:ℝ) ^ n)⁻¹) ^ ((2⁻¹ : ℝ≥0) : ℝ) = ((2:ℝ) ^ n)⁻¹ := by
  rw [four_pow, ← inv_pow, NNReal.coe_inv, NNReal.coe_ofNat, show ((2:ℝ))⁻¹ = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]

/-- `μH[1/2] cantor ≤ 1`, via the covers by the `2ⁿ` level-`n` intervals of length `4^{-n}`. -/
theorem hausdorff_le : μH[((2⁻¹ : ℝ≥0) : ℝ)] cantor ≤ 1 := by
  rw [cantor_eq_range]
  have hr : Tendsto (fun n : ℕ => ENNReal.ofReal ((4:ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)))
  refine (Measure.hausdorffMeasure_le_liminf_sum _ _ _ hr cell
    (Eventually.of_forall fun n w => (ediam_cell n w).le)
    (Eventually.of_forall range_code_subset)).trans (le_of_eq ?_)
  have : ∀ n : ℕ, ∑ w : Fin n → Fin 2, Metric.ediam (cell n w) ^ ((2⁻¹ : ℝ≥0) : ℝ) = 1 := by
    intro n
    simp_rw [ediam_cell]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (NNReal.coe_nonneg _), rpow_quarter]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
    push_cast
    exact ENNReal.mul_inv_cancel (by simp) (by simp)
  simp_rw [this]; exact liminf_const 1

/-- `toBinary (code a) = 0.a₀a₁a₂…` in base 2. -/
noncomputable def toBinary (x : ℝ) : ℝ := Real.ofDigits (Function.invFun code x)

theorem toBinary_code (a : ℕ → Fin 2) : toBinary (code a) = Real.ofDigits a := by
  rw [toBinary, Function.leftInverse_invFun code_injective a]

theorem binary_holder_aux (a a' : ℕ → Fin 2) :
    |Real.ofDigits a - Real.ofDigits a'| ≤ 2 * √|code a - code a'| := by
  by_cases h : a = a'
  · subst h; simp
  obtain ⟨n, hlt, hn⟩ := exists_first_diff h
  have h1 := Real.abs_ofDigits_sub_ofDigits_le hlt
  simp only [Nat.cast_ofNat] at h1
  have h2 := code_sep a a' n hlt hn
  have e : (((2:ℝ) ^ n)⁻¹ / 2) ^ 2 = ((4:ℝ) ^ n)⁻¹ / 4 := by
    rw [four_pow]; field_simp; ring
  have h3 : (((2:ℝ) ^ n)⁻¹ / 2) ^ 2 ≤ |code a - code a'| := by
    have : (0:ℝ) < ((4:ℝ) ^ n)⁻¹ := by positivity
    rw [e]; linarith
  have h4 := (Real.sqrt_sq (by positivity : (0:ℝ) ≤ ((2:ℝ) ^ n)⁻¹ / 2)).symm.le.trans
    (Real.sqrt_le_sqrt h3)
  linarith

/-- `toBinary` is `1/2`-Hölder on the Cantor set. -/
theorem toBinary_holder : HolderOnWith 2 2⁻¹ toBinary (Set.range code) := by
  rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
  rw [toBinary_code, toBinary_code, edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by positivity), NNReal.coe_inv,
    NNReal.coe_ofNat, show ((2:ℝ))⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    show ((2:ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (binary_holder_aux a a')

theorem half_le_dimH : (2⁻¹ : ℝ≥0∞) ≤ dimH cantor := by
  have hIcc : Icc (0:ℝ) 1 ⊆ toBinary '' Set.range code := by
    intro y hy
    obtain ⟨a, -, ha⟩ := Real.ofDigits_SurjOn (b := 2) (by norm_num) hy
    exact ⟨code a, ⟨a, rfl⟩, by rw [toBinary_code, ha]⟩
  have h1 : (1 : ℝ≥0∞) ≤ dimH (toBinary '' Set.range code) := by
    have := Real.dimH_of_nonempty_interior (s := Icc (0:ℝ) 1)
      (by rw [interior_Icc]; exact ⟨1 / 2, by norm_num, by norm_num⟩)
    rw [Module.finrank_self, Nat.cast_one] at this
    exact this.symm.le.trans (dimH_mono hIcc)
  have h3 := h1.trans (toBinary_holder.dimH_image_le (by norm_num))
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), one_mul] at h3
  rw [cantor_eq_range]; simpa using h3

/-- **Hausdorff dimension.** `dimH cantor = 1/2`. -/
theorem dimH_cantor : dimH cantor = 1 / 2 := by
  rw [one_div]
  refine le_antisymm ?_ half_le_dimH
  have := dimH_le_of_hausdorffMeasure_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hausdorff_le)
  simpa using this

/-! ## The Cantor measure -/

/-- The fair coin on `Fin 2 = {0,1}`. -/
noncomputable def coin : Measure (Fin 2) := (PMF.uniformOfFintype (Fin 2)).toMeasure

instance : IsProbabilityMeasure coin := by unfold coin; infer_instance

/-- The fair-coin product measure on `{0,1}^ℕ` (i.i.d. fair digits). -/
noncomputable def bern : Measure (ℕ → Fin 2) := Measure.infinitePi (fun _ => coin)

instance : IsProbabilityMeasure bern := by unfold bern; infer_instance

/-- The natural Cantor measure: the law of `∑ dᵢ 4^{-(i+1)}` with i.i.d. fair digits `dᵢ ∈ {0,3}`. -/
noncomputable def cantorMeasure : Measure ℝ := bern.map code

theorem code_measurable : Measurable code := code_continuous.measurable

instance : IsProbabilityMeasure cantorMeasure := by
  unfold cantorMeasure; exact Measure.isProbabilityMeasure_map code_measurable.aemeasurable

/-- `cantorMeasure` is carried by the Cantor set. -/
theorem cantorMeasure_cantor : cantorMeasure cantor = 1 := by
  rw [cantorMeasure, Measure.map_apply code_measurable isCompact_cantor.measurableSet,
    cantor_eq_range, Set.preimage_range, measure_univ]

theorem coin_singleton (e : Fin 2) : coin {e} = 2⁻¹ := by
  simp [coin, PMF.uniformOfFintype_apply]

theorem bern_cyl (s : Finset ℕ) (w : ℕ → Fin 2) :
    bern (Set.pi s (fun i => {w i})) = 2⁻¹ ^ s.card := by
  rw [bern, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton _)]
  simp [coin_singleton]

/-! ## Fourier transform: no decay along `4ⁿ` -/

/-- Fourier transform `μ̂(ξ) = ∫ exp(-2πiξx) dμ(x)`. -/
noncomputable def fourierTransform (μ : Measure ℝ) (ξ : ℝ) : ℂ :=
  ∫ x, Complex.exp (↑(-2 * π * ξ * x) * Complex.I) ∂μ

/-- `4ⁿ · code a = N + code (shiftⁿ a)` with `N ∈ ℕ`. -/
theorem four_pow_mul_code (a : ℕ → Fin 2) (n : ℕ) :
    ∃ N : ℕ, (4:ℝ) ^ n * code a = N + code (fun i => a (i + n)) := by
  refine ⟨∑ i ∈ Finset.range n, (dig (a i) : ℕ) * 4 ^ (n - (i + 1)), ?_⟩
  rw [code_split a n, mul_add, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul,
    Finset.mul_sum]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i + 1 ≤ n := Finset.mem_range.1 hi
  rw [Real.ofDigitsTerm, show (4:ℝ) ^ n = 4 ^ (n - (i + 1)) * 4 ^ (i + 1) by
    rw [← pow_add, Nat.sub_add_cancel hi']]
  push_cast
  field_simp

theorem cos_shift (a : ℕ → Fin 2) (n : ℕ) :
    Real.cos (-2 * π * (4:ℝ) ^ n * code a) = Real.cos (2 * π * code (fun i => a (i + n))) := by
  obtain ⟨N, hN⟩ := four_pow_mul_code a n
  rw [show -2 * π * (4:ℝ) ^ n * code a = -(2 * π * code (fun i => a (i + n)) + N * (2 * π)) by
    rw [mul_assoc (-2 * π), hN]; ring, Real.cos_neg, Real.cos_add_nat_mul_two_pi]

theorem cos_code_nonneg (b : ℕ → Fin 2) : 0 ≤ Real.cos (2 * π * code b) := by
  have h0 := code_nonneg b; have h1 := code_le_one b; have hp := Real.pi_pos
  rcases code_gap b with h | h
  · exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  · rw [← Real.cos_sub_two_pi]; exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩

theorem cos_code_ge (b : ℕ → Fin 2) (h0 : b 0 = 0) (h1 : b 1 = 0) :
    1 / 2 ≤ Real.cos (2 * π * code b) := by
  have hc : code b ≤ 1 / 16 := by
    rw [code_head, if_pos h0]
    have := code_le_of_zero (fun i => b (i + 1)) (by simpa using h1); linarith
  have hp := Real.pi_pos; have := code_nonneg b
  rw [← Real.cos_pi_div_three]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by nlinarith)

/-- **Key estimate.** `Re μ̂(4ⁿ) ≥ 1/8` for every `n : ℕ`. -/
theorem re_fourier_ge (n : ℕ) : 1 / 8 ≤ (fourierTransform cantorMeasure ((4:ℝ) ^ n)).re := by
  set E : Set (ℕ → Fin 2) := Set.pi (({n, n + 1} : Finset ℕ) : Set ℕ) (fun _ => {0}) with hE
  have hEm : MeasurableSet E :=
    MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)
  have hEv : bern.real E = 1 / 4 := by
    rw [measureReal_def, hE, bern_cyl _ (fun _ => 0), Finset.card_pair (by omega)]
    simp [ENNReal.toReal_pow]; norm_num
  have hc : Continuous fun a => Complex.exp (↑(-2 * π * (4:ℝ) ^ n * code a) * Complex.I) := by
    have := code_continuous; fun_prop
  have hint : Integrable (fun a => Complex.exp (↑(-2 * π * (4:ℝ) ^ n * code a) * Complex.I)) bern :=
    (integrable_const (1:ℝ)).mono' hc.aestronglyMeasurable
      (ae_of_all _ fun a => by rw [Complex.norm_exp_ofReal_mul_I])
  have hcos : Integrable (fun a => Real.cos (-2 * π * (4:ℝ) ^ n * code a)) bern :=
    (integrable_const (1:ℝ)).mono' (by have := code_continuous; fun_prop)
      (ae_of_all _ fun a => by simpa using Real.abs_cos_le_one _)
  unfold fourierTransform cantorMeasure
  rw [integral_map code_measurable.aemeasurable (by fun_prop : Continuous fun x : ℝ =>
    Complex.exp (↑(-2 * π * (4:ℝ) ^ n * x) * Complex.I)).aestronglyMeasurable]
  have hre := integral_re hint
  simp only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] at hre
  rw [← hre]
  calc (1 / 8 : ℝ) = ∫ a, E.indicator (fun _ => (1 / 2 : ℝ)) a ∂bern := by
        rw [integral_indicator_const _ hEm, hEv]; norm_num
    _ ≤ _ := integral_mono ((integrable_const _).indicator hEm) hcos fun a => by
        by_cases ha : a ∈ E
        · rw [Set.indicator_of_mem ha, cos_shift]
          simp only [hE, Finset.coe_insert, Finset.coe_singleton, Set.mem_pi, Set.mem_insert_iff,
            Set.mem_singleton_iff, forall_eq_or_imp, forall_eq] at ha
          exact cos_code_ge _ (by simpa using ha.1) (by simpa [add_comm] using ha.2)
        · rw [Set.indicator_of_notMem ha, cos_shift]; exact cos_code_nonneg _

/-- `μ̂(ξ) ↛ 0` as `ξ → +∞`. -/
theorem not_tendsto_atTop : ¬ Tendsto (fourierTransform cantorMeasure) atTop (𝓝 0) := by
  intro h
  have h4 : Tendsto (fun n : ℕ => (4:ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have := ge_of_tendsto' ((Complex.continuous_re.tendsto 0).comp (h.comp h4))
    fun n => re_fourier_ge n
  norm_num at this

/-- Not Rajchman: `μ̂(ξ) ↛ 0` as `|ξ| → ∞`. -/
theorem not_rajchman : ¬ Tendsto (fourierTransform cantorMeasure) (cocompact ℝ) (𝓝 0) :=
  fun h => not_tendsto_atTop (h.mono_left atTop_le_cocompact)

/-- Integer frequencies: `μ̂(m) ↛ 0` as `m → ∞` in `ℤ`. -/
theorem not_tendsto_int :
    ¬ Tendsto (fun m : ℤ => fourierTransform cantorMeasure m) atTop (𝓝 0) := by
  intro h
  have h4 : Tendsto (fun n : ℕ => (4:ℤ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have := ge_of_tendsto' ((Complex.continuous_re.tendsto 0).comp (h.comp h4))
    fun n => by simpa using re_fourier_ge n
  norm_num at this

/-! ## ×4-invariance, and failure of ×2-invariance -/

/-- `T₄ x = 4x mod 1`. -/
noncomputable def T4 (x : ℝ) : ℝ := Int.fract (4 * x)

/-- `T₂ x = 2x mod 1`. -/
noncomputable def T2 (x : ℝ) : ℝ := Int.fract (2 * x)

/-- The left shift on `{0,1}^ℕ`. -/
def shift (a : ℕ → Fin 2) : ℕ → Fin 2 := fun i => a (i + 1)

theorem measurable_shift : Measurable shift :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- The shift preserves the fair-coin product measure. -/
theorem bern_shift : bern.map shift = bern := by
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply measurable_shift (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have : shift ⁻¹' Set.pi s t =
      Set.pi (s.map (addRightEmbedding 1) : Set ℕ) (fun j => t (j - 1)) := by
    ext a; simp [shift, Set.mem_pi]
  rw [this, bern, Measure.infinitePi_pi _ (fun i _ => ht _), Finset.prod_map]
  simp

theorem bern_singleton (b : ℕ → Fin 2) : bern {b} = 0 := by
  refine le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (ENNReal.inv_lt_one.2 (by norm_num) : (2⁻¹ : ℝ≥0∞) < 1)) fun n => ?_) (by positivity)
  rw [← Finset.card_range n, ← bern_cyl _ b]
  exact measure_mono fun x hx => by simp_all

theorem code_ones : code (fun _ => 1) = 1 := by
  have h : (fun _ : ℕ => dig 1) = fun _ => Fin.last 3 := by funext; decide
  show Real.ofDigits (fun _ => dig 1) = 1
  rw [h]; exact Real.ofDigits_const_last_eq_one 3

theorem four_mul_code (a : ℕ → Fin 2) : ∃ k : ℕ, 4 * code a = k + code (shift a) := by
  obtain ⟨N, hN⟩ := four_pow_mul_code a 1
  exact ⟨N, by rw [pow_one] at hN; exact hN⟩

theorem T4_code (a : ℕ → Fin 2) (h : code (shift a) < 1) : T4 (code a) = code (shift a) := by
  obtain ⟨k, hk⟩ := four_mul_code a
  rw [T4, hk, Int.fract_natCast_add, Int.fract_eq_self.2 ⟨code_nonneg _, h⟩]

/-- **×4-invariance.** `cantorMeasure` is invariant under `T₄ : x ↦ 4x mod 1`. -/
theorem cantorMeasure_T4 : cantorMeasure.map T4 = cantorMeasure := by
  have hT4 : Measurable T4 := by unfold T4; exact measurable_fract.comp (measurable_id.const_mul _)
  have hae : T4 ∘ code =ᵐ[bern] code ∘ shift := by
    have h0 : bern (shift ⁻¹' {fun _ => 1}) = 0 := by
      rw [← Measure.map_apply measurable_shift (measurableSet_singleton _), bern_shift,
        bern_singleton]
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun a ha => ?_) h0
    by_contra hne
    refine ha (T4_code a (lt_of_le_of_ne (code_le_one _) fun h1 => hne ?_))
    exact code_injective (h1.trans code_ones.symm)
  unfold cantorMeasure
  rw [Measure.map_map hT4 code_measurable, Measure.map_congr hae,
    ← Measure.map_map code_measurable measurable_shift, bern_shift]

/-- **Not ×2-invariant.** `cantorMeasure` gives `(1/4, 3/4)` mass `0`, its `T₂`-image does not. -/
theorem cantorMeasure_T2_ne : cantorMeasure.map T2 ≠ cantorMeasure := by
  have hT2 : Measurable T2 := by unfold T2; exact measurable_fract.comp (measurable_id.const_mul _)
  have hU : cantorMeasure (Ioo (1 / 4) (3 / 4)) = 0 := by
    rw [cantorMeasure, Measure.map_apply code_measurable measurableSet_Ioo]
    convert measure_empty (μ := bern)
    exact Set.eq_empty_of_forall_notMem fun a ha => by
      rcases code_gap a with h | h
      · exact absurd ha.1 (not_lt.2 h)
      · exact absurd ha.2 (not_lt.2 h)
  intro h
  have hpos : (0 : ℝ≥0∞) < (cantorMeasure.map T2) (Ioo (1 / 4) (3 / 4)) := by
    rw [Measure.map_apply hT2 measurableSet_Ioo, cantorMeasure,
      Measure.map_apply code_measurable (hT2 measurableSet_Ioo)]
    refine lt_of_lt_of_le (ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp)) _ :
      (0 : ℝ≥0∞) < 2⁻¹ ^ ({0, 1} : Finset ℕ).card) ?_
    rw [← bern_cyl _ (fun i => if i = 0 then 1 else 0)]
    refine measure_mono fun a ha => ?_
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_pi, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq] at ha
    simp only [if_pos, one_ne_zero, if_false] at ha
    have h1 : code a = 3 / 4 + 4⁻¹ * code (fun i => a (i + 1)) := by
      rw [code_head a, if_neg (by simp [ha.1])]
    have h2 := code_le_of_zero (fun i => a (i + 1)) (by simpa using ha.2)
    have h3 := code_nonneg (fun i => a (i + 1))
    show T2 (code a) ∈ Ioo (1 / 4) (3 / 4)
    have hf : T2 (code a) = 2 * code a - 1 := by
      rw [T2, Int.fract_eq_iff]; exact ⟨by linarith, by linarith, 1, by push_cast; ring⟩
    rw [hf]; constructor <;> linarith
  rw [h, hU] at hpos; exact lt_irrefl _ hpos

/-! ## Main theorem -/

/-- **Conjecture 00000002410 (true; classical example).** There is a probability measure `μ`
carried by a homogeneous Cantor set `K` (homeomorphic to `{0,1}^ℕ`, compact, `K = K/4 ∪ (K/4 + 3/4)`,
`dimH K = 1/2`) such that `Re μ̂(4ⁿ) ≥ 1/8` for all `n`, hence `μ̂(ξ) ↛ 0` as `|ξ| → ∞` and
`μ̂(m) ↛ 0` as `m → ∞` in `ℤ`; moreover `μ` is invariant under `x ↦ 4x mod 1` but not under
`x ↦ 2x mod 1`. -/
theorem main :
    ∃ (K : Set ℝ) (μ : Measure ℝ), IsProbabilityMeasure μ ∧ μ K = 1 ∧
      Nonempty (K ≃ₜ (ℕ → Fin 2)) ∧ IsCompact K ∧
      K = (fun x => x / 4) '' K ∪ (fun x => x / 4 + 3 / 4) '' K ∧ dimH K = 1 / 2 ∧
      (∀ n : ℕ, 1 / 8 ≤ (fourierTransform μ ((4:ℝ) ^ n)).re) ∧
      ¬ Tendsto (fourierTransform μ) (cocompact ℝ) (𝓝 0) ∧
      ¬ Tendsto (fun m : ℤ => fourierTransform μ m) atTop (𝓝 0) ∧
      μ.map T4 = μ ∧ μ.map T2 ≠ μ :=
  ⟨cantor, cantorMeasure, inferInstance, cantorMeasure_cantor, cantor_homeomorph,
    isCompact_cantor, cantor_selfSimilar, dimH_cantor, re_fourier_ge, not_rajchman,
    not_tendsto_int, cantorMeasure_T4, cantorMeasure_T2_ne⟩

end C2410
