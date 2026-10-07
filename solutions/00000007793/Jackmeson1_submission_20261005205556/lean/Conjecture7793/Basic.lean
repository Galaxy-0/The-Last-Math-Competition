import Mathlib

/-!
# Conjecture 00000007793 (two-point distance variance ratio) is false

Let `X, Y` be independent and uniformly distributed on the unit ball of `ℝⁿ` (`n` is the
dimension).  The conjecture asserts `Var|X - Y| / Var|X| = 2 - 2/√3 + O(1/n)`.

We prove, for every `n ≥ 1`,
`Var|X - Y| / Var|X| ≥ (n + 1)^2 / (4 (n + 2))`,
so the ratio tends to `+∞`; in particular it is not `L + O(1/n)` for any constant `L`.

Ingredients: `E|X|^k = n/(n+k)` (polar coordinates, `integral_fun_norm_addHaar`), hence
`Var|X| = n/((n+1)^2 (n+2))`; the symmetry `Y ↦ -Y` together with
`|X+Y|^2 - |X-Y|^2 = 4⟨X,Y⟩` gives `Var|X-Y| ≥ E⟨X,Y⟩^2 / 4`; and
`E⟨X,Y⟩^2 = ∑ᵢⱼ (E XᵢXⱼ)^2 ≥ (E|X|^2)^2 / n = n/(n+2)^2`.
-/

open MeasureTheory ProbabilityTheory Metric Filter Set Asymptotics
open scoped RealInnerProductSpace Topology

namespace C7793

/-- `ℝⁿ` with its Euclidean structure. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The uniform probability measure on the open unit ball of `ℝⁿ`: Lebesgue measure restricted
to the ball and normalised, i.e. `volume[|ball 0 1] = (volume (ball 0 1))⁻¹ • volume.restrict (ball 0 1)`. -/
noncomputable def ballUnif (n : ℕ) : Measure (E n) :=
  ProbabilityTheory.cond volume (ball (0 : E n) 1)

/-- `Var |X - Y| / Var |X|` for `X, Y` independent, both uniform on the unit ball of `ℝⁿ`.
Independence is modelled by the product measure, with `X = p.1` and `Y = p.2`. -/
noncomputable def ratio (n : ℕ) : ℝ :=
  variance (fun p : E n × E n => ‖p.1 - p.2‖) ((ballUnif n).prod (ballUnif n)) /
    variance (fun x : E n => ‖x‖) (ballUnif n)

instance (n : ℕ) : IsProbabilityMeasure (ballUnif n) :=
  cond_isProbabilityMeasure_of_finite (measure_ball_pos volume 0 one_pos).ne'
    measure_ball_lt_top.ne

lemma ae_ball (n : ℕ) : ∀ᵐ x ∂ballUnif n, x ∈ closedBall (0 : E n) 1 := by
  filter_upwards [ae_cond_mem (μ := (volume : Measure (E n))) (measurableSet_ball (x := 0) (ε := 1))]
    with x hx
  exact ball_subset_closedBall hx

lemma ae_ball2 (n : ℕ) : ∀ᵐ p ∂(ballUnif n).prod (ballUnif n),
    p ∈ closedBall (0 : E n) 1 ×ˢ closedBall (0 : E n) 1 :=
  (Measure.quasiMeasurePreserving_fst.ae (ae_ball n)).and
    (Measure.quasiMeasurePreserving_snd.ae (ae_ball n))

/-- A continuous function is integrable for a finite measure carried by a compact set. -/
lemma integrable_of_continuous {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [SecondCountableTopology α] {ν : Measure α} [IsFiniteMeasure ν]
    {K : Set α} (hK : IsCompact K) (hν : ∀ᵐ x ∂ν, x ∈ K) {g : α → ℝ} (hg : Continuous g) :
    Integrable g ν := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  exact Integrable.of_bound hg.aestronglyMeasurable C (by filter_upwards [hν] with x hx using hC x hx)

lemma int1 {n : ℕ} {g : E n → ℝ} (hg : Continuous g) : Integrable g (ballUnif n) :=
  integrable_of_continuous (isCompact_closedBall _ _) (ae_ball n) hg

lemma int2 {n : ℕ} {g : E n × E n → ℝ} (hg : Continuous g) :
    Integrable g ((ballUnif n).prod (ballUnif n)) :=
  integrable_of_continuous ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
    (ae_ball2 n) hg

/-! ### Radial moments -/

lemma radial (n k : ℕ) (hn : 1 ≤ n) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) • (Iio (1 : ℝ)).indicator (fun r => r ^ k) y = 1 / (n + k) := by
  have h : (fun y : ℝ => y ^ (n - 1) • (Iio (1 : ℝ)).indicator (fun r => r ^ k) y) =
      (Iio (1 : ℝ)).indicator (fun y => y ^ (n - 1 + k)) := by
    funext y; by_cases hy : y < 1 <;> simp [indicator, hy, pow_add]
  rw [h, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Iio_inter_Ioi, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_pow]
  have e : n - 1 + k + 1 = n + k := by omega
  rw [e]
  have h0 : (0 : ℝ) ^ (n + k) = 0 := zero_pow (by omega)
  simp only [one_pow, h0, sub_zero]
  rw [Nat.cast_add, Nat.cast_sub hn, Nat.cast_one]
  congr 1
  ring

/-- `E|X|^k = n / (n + k)` for `X` uniform on the unit ball of `ℝⁿ`. -/
lemma moment (n k : ℕ) (hn : 1 ≤ n) : ∫ x, ‖x‖ ^ k ∂ballUnif n = n / (n + k) := by
  have hB0 : volume (ball (0 : E n) 1) ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
  have hBt : volume (ball (0 : E n) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hBr : volume.real (ball (0 : E n) 1) ≠ 0 := by
    rw [measureReal_def]; exact ENNReal.toReal_ne_zero.mpr ⟨hB0, hBt⟩
  have h1 : ∫ x, ‖x‖ ^ k ∂ballUnif n = (volume.real (ball (0 : E n) 1))⁻¹ *
      ∫ x : E n, (Iio (1 : ℝ)).indicator (fun r => r ^ k) ‖x‖ := by
    rw [ballUnif, ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator measurableSet_ball]
    rw [measureReal_def, ENNReal.toReal_inv, smul_eq_mul]
    congr 2
    funext x
    by_cases hx : ‖x‖ < 1 <;> simp [indicator, hx]
  have : Nontrivial (E n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  rw [h1, integral_fun_norm_addHaar (volume : Measure (E n)) ((Iio (1 : ℝ)).indicator fun r => r ^ k),
    finrank_euclideanSpace_fin, radial n k hn]
  have : (n : ℝ) + k ≠ 0 := by positivity
  simp only [nsmul_eq_mul, smul_eq_mul]
  field_simp

/-- `Var|X| = n / ((n+1)^2 (n+2))`. -/
lemma var_norm (n : ℕ) (hn : 1 ≤ n) :
    variance (fun x : E n => ‖x‖) (ballUnif n) = n / ((n + 1) ^ 2 * (n + 2)) := by
  have hm : MemLp (fun x : E n => ‖x‖) 2 (ballUnif n) :=
    MemLp.of_bound continuous_norm.aestronglyMeasurable 1
      (by filter_upwards [ae_ball n] with x hx; simpa using hx)
  rw [variance_eq_sub hm]
  have e1 := moment n 1 hn
  have e2 := moment n 2 hn
  simp only [pow_one] at e1
  show ∫ x, ‖x‖ ^ 2 ∂ballUnif n - (∫ x, ‖x‖ ∂ballUnif n) ^ 2 = _
  rw [e1, e2]
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-! ### The symmetry `Y ↦ -Y` -/

lemma neg_pres (n : ℕ) : MeasurePreserving (fun y : E n => -y) (ballUnif n) (ballUnif n) := by
  have h := (LinearIsometryEquiv.neg ℝ (E := E n)).measurePreserving
  have hpre : (fun y : E n => -y) ⁻¹' ball (0 : E n) 1 = ball 0 1 := by
    ext y; simp
  have h2 := (h.restrict_preimage (s := ball (0 : E n) 1) measurableSet_ball)
  simp only [LinearIsometryEquiv.coe_neg] at h2
  rw [hpre] at h2
  exact h2.smul_measure _

/-- Pointwise: on the unit ball, `⟨x,y⟩^2 ≤ 2((|x-y| - c)^2 + (|x+y| - c)^2)`. -/
lemma pointwise {n : ℕ} (x y : E n) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (c : ℝ) :
    ⟪x, y⟫ ^ 2 ≤ 2 * ((‖x - y‖ - c) ^ 2 + (‖x + y‖ - c) ^ 2) := by
  have ha : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := norm_sub_sq_real x y
  have hb : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := norm_add_sq_real x y
  have h1 : ‖x - y‖ ≤ 2 := (norm_sub_le x y).trans (by linarith)
  have h2 : ‖x + y‖ ≤ 2 := (norm_add_le x y).trans (by linarith)
  have ha0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hb0 : 0 ≤ ‖x + y‖ := norm_nonneg _
  set a := ‖x - y‖
  set b := ‖x + y‖
  set t := ⟪x, y⟫
  have h16 : 16 * t ^ 2 = (b - a) ^ 2 * (b + a) ^ 2 := by
    have : 4 * t = (b - a) * (b + a) := by nlinarith
    nlinarith
  have hab : (b + a) ^ 2 ≤ 16 := by nlinarith
  have hs : t ^ 2 ≤ (b - a) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hab (sq_nonneg (b - a))]
  nlinarith [sq_nonneg (a + b - 2 * c)]

/-- `E⟨X,Y⟩^2 ≤ 4 Var|X - Y|`. -/
lemma inner_sq_le_var (n : ℕ) :
    ∫ p : E n × E n, ⟪p.1, p.2⟫ ^ 2 ∂(ballUnif n).prod (ballUnif n) ≤
      4 * variance (fun p : E n × E n => ‖p.1 - p.2‖) ((ballUnif n).prod (ballUnif n)) := by
  set ν := (ballUnif n).prod (ballUnif n)
  set c := ∫ p, ‖p.1 - p.2‖ ∂ν
  have hT : MeasurePreserving (Prod.map id (fun y : E n => -y)) ν ν :=
    (MeasurePreserving.id (ballUnif n)).prod (neg_pres n)
  have hV : variance (fun p : E n × E n => ‖p.1 - p.2‖) ν = ∫ p, (‖p.1 - p.2‖ - c) ^ 2 ∂ν :=
    variance_eq_integral (by fun_prop)
  have hV' : ∫ p, (‖p.1 + p.2‖ - c) ^ 2 ∂ν = ∫ p, (‖p.1 - p.2‖ - c) ^ 2 ∂ν := by
    conv_rhs => rw [← hT.map_eq]
    rw [integral_map hT.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    simp [sub_neg_eq_add]
  have hpt : ∀ᵐ p ∂ν, ⟪p.1, p.2⟫ ^ 2 ≤ 2 * ((‖p.1 - p.2‖ - c) ^ 2 + (‖p.1 + p.2‖ - c) ^ 2) := by
    filter_upwards [ae_ball2 n] with p hp
    obtain ⟨h1, h2⟩ := hp
    rw [mem_closedBall_zero_iff] at h1 h2
    exact pointwise p.1 p.2 h1 h2 c
  calc ∫ p, ⟪p.1, p.2⟫ ^ 2 ∂ν
      ≤ ∫ p, 2 * ((‖p.1 - p.2‖ - c) ^ 2 + (‖p.1 + p.2‖ - c) ^ 2) ∂ν :=
        integral_mono_ae (int2 (by fun_prop)) (int2 (by fun_prop)) hpt
    _ = 4 * variance (fun p : E n × E n => ‖p.1 - p.2‖) ν := by
        rw [integral_const_mul, integral_add (int2 (by fun_prop)) (int2 (by fun_prop)), hV', hV]
        ring

/-- `E⟨X,Y⟩^2 = ∑ᵢⱼ (E XᵢXⱼ)^2 ≥ (E|X|^2)^2 / n`. -/
lemma inner_sq_ge (n : ℕ) (hn : 1 ≤ n) :
    (∫ x, ‖x‖ ^ 2 ∂ballUnif n) ^ 2 / n ≤
      ∫ p : E n × E n, ⟪p.1, p.2⟫ ^ 2 ∂(ballUnif n).prod (ballUnif n) := by
  set m : Fin n → Fin n → ℝ := fun i j => ∫ x, x i * x j ∂ballUnif n
  have hexp : ∫ p : E n × E n, ⟪p.1, p.2⟫ ^ 2 ∂(ballUnif n).prod (ballUnif n) =
      ∑ i, ∑ j, m i j ^ 2 := by
    have hp : ∀ p : E n × E n,
        ⟪p.1, p.2⟫ ^ 2 = ∑ i, ∑ j, (p.1 i * p.1 j) * (p.2 i * p.2 j) := by
      intro p
      rw [PiLp.inner_apply, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    simp_rw [hp]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      int2 (g := fun p : E n × E n => p.1 i * p.1 j * (p.2 i * p.2 j)) (by fun_prop)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ =>
      int2 (g := fun p : E n × E n => p.1 i * p.1 j * (p.2 i * p.2 j)) (by fun_prop)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_prod_mul (fun x : E n => x i * x j) (fun y : E n => y i * y j)]
    ring
  have htr : ∫ x, ‖x‖ ^ 2 ∂ballUnif n = ∑ i, m i i := by
    rw [← integral_finsetSum _ fun i _ => int1 (g := fun x : E n => x i * x i) (by fun_prop)]
    congr 1
    funext x
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [sq]
  rw [hexp, htr]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc (∑ i, m i i) ^ 2 / n ≤ ∑ i, m i i ^ 2 := by
        rw [div_le_iff₀ hn']
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun i => m i i)
        simpa [mul_comm] using this
    _ ≤ ∑ i, ∑ j, m i j ^ 2 := Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (f := fun j => m i j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- `Var|X - Y| ≥ n / (4 (n+2)^2)`. -/
lemma var_dist_ge (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / (4 * (n + 2) ^ 2) ≤
      variance (fun p : E n × E n => ‖p.1 - p.2‖) ((ballUnif n).prod (ballUnif n)) := by
  have h1 := inner_sq_ge n hn
  have h2 := inner_sq_le_var n
  rw [moment n 2 hn] at h1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ((n : ℝ) / (n + (2 : ℕ))) ^ 2 / n = n / (n + 2) ^ 2 := by
    push_cast; field_simp
  rw [e] at h1
  have e4 : (n : ℝ) / (4 * (n + 2) ^ 2) = (n / (n + 2) ^ 2) / 4 := by field_simp
  rw [e4]
  linarith

/-! ### Main results -/

/-- Lower bound: `Var|X - Y| / Var|X| ≥ (n + 1)^2 / (4 (n + 2))` for every dimension `n ≥ 1`. -/
theorem ratio_ge (n : ℕ) (hn : 1 ≤ n) : ((n : ℝ) + 1) ^ 2 / (4 * (n + 2)) ≤ ratio n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold ratio
  rw [var_norm n hn, le_div_iff₀ (by positivity)]
  calc ((n : ℝ) + 1) ^ 2 / (4 * (n + 2)) * (n / ((n + 1) ^ 2 * (n + 2)))
      = n / (4 * (n + 2) ^ 2) := by field_simp
    _ ≤ _ := var_dist_ge n hn

/-- The variance ratio tends to `+∞` with the dimension. -/
theorem ratio_tendsto_atTop : Tendsto ratio atTop atTop := by
  have hlin : Tendsto (fun n : ℕ => (n : ℝ) / 8) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hlin
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine le_trans ?_ (ratio_ge n hn)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

/-- **Conjecture 00000007793 is false.** For `X, Y` independent and uniform on the unit ball of
`ℝⁿ`, the ratio `Var|X - Y| / Var|X|` is not `2 - 2/√3 + O(1/n)` as `n → ∞`. -/
theorem not_conjecture :
    ¬ (fun n : ℕ => ratio n - (2 - 2 / Real.sqrt 3)) =O[atTop] (fun n : ℕ => (1 : ℝ) / n) := by
  intro h
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h1 := h.trans_tendsto h0
  have h2 : Tendsto ratio atTop (𝓝 (2 - 2 / Real.sqrt 3)) := by
    have := h1.add_const (2 - 2 / Real.sqrt 3)
    simpa using this
  exact not_tendsto_nhds_of_tendsto_atTop ratio_tendsto_atTop _ h2

/-- The ratio has no finite limit; in particular it does not converge to `2 - 2/√3`. -/
theorem no_finite_limit (L : ℝ) : ¬ Tendsto ratio atTop (𝓝 L) :=
  not_tendsto_nhds_of_tendsto_atTop ratio_tendsto_atTop L

/-! ### Random-variable formulation, any radius

The ratio is scale invariant, so the normalisation of the ball (unit ball, or the isotropic
position of radius `√(n+2)`) does not matter.  We state the refutation for arbitrary
independent random variables with uniform laws on balls of arbitrary radii `r n > 0`. -/

/-- The uniform probability measure on the open ball of radius `r` in `ℝⁿ`. -/
noncomputable def ballUnifR (n : ℕ) (r : ℝ) : Measure (E n) :=
  ProbabilityTheory.cond volume (ball (0 : E n) r)

lemma map_smul_ballUnif (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (ballUnif n).map (fun x => r • x) = ballUnifR n r := by
  ext s hs
  rw [Measure.map_apply (measurable_const_smul r) hs]
  simp only [ballUnif, ballUnifR, cond_apply measurableSet_ball]
  have hpre : (fun x : E n => r • x) ⁻¹' (ball 0 r ∩ s) = ball 0 1 ∩ (fun x => r • x) ⁻¹' s := by
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith [norm_nonneg x], h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith [norm_nonneg x], h2⟩
  rw [← hpre, Measure.addHaar_preimage_smul volume hr.ne',
    Measure.addHaar_ball_of_pos volume 0 hr]
  have hB0 : volume (ball (0 : E n) 1) ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
  have hBt : volume (ball (0 : E n) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hrn : (0 : ℝ) < r ^ Module.finrank ℝ (E n) := pow_pos hr _
  rw [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hrn).ne') (Or.inl ENNReal.ofReal_ne_top),
    abs_of_pos (inv_pos.mpr hrn), ENNReal.ofReal_inv_of_pos hrn]
  ring

/-- For `X, Y` independent, uniform on the ball of radius `r > 0` in `ℝⁿ`, the ratio
`Var|X - Y| / Var|X|` equals `ratio n`. -/
lemma ratio_eq_of_indep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {r : ℝ} (hr : 0 < r) {X Y : Ω → E n} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P) (hlX : P.map X = ballUnifR n r) (hlY : P.map Y = ballUnifR n r) :
    variance (fun ω => ‖X ω - Y ω‖) P / variance (fun ω => ‖X ω‖) P = ratio n := by
  have hs : Measurable (fun x : E n => r⁻¹ • x) := measurable_const_smul _
  have hinv : (fun x : E n => r⁻¹ • x) ∘ (fun x : E n => r • x) = id := by
    funext x; simp [smul_smul, inv_mul_cancel₀ hr.ne']
  have hlaw : ∀ Z : Ω → E n, Measurable Z → P.map Z = ballUnifR n r →
      P.map ((fun x : E n => r⁻¹ • x) ∘ Z) = ballUnif n := by
    intro Z hZ hl
    rw [← Measure.map_map hs hZ, hl, ← map_smul_ballUnif n hr,
      Measure.map_map hs (measurable_const_smul r), hinv, Measure.map_id]
  have hind := hXY.comp hs hs
  have hj : P.map (fun ω => (((fun x : E n => r⁻¹ • x) ∘ X) ω, ((fun x : E n => r⁻¹ • x) ∘ Y) ω))
      = (ballUnif n).prod (ballUnif n) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (hs.comp hX).aemeasurable
      (hs.comp hY).aemeasurable).mp hind, hlaw X hX hlX, hlaw Y hY hlY]
  have e1 : variance (fun ω => ‖X ω - Y ω‖) P = r ^ 2 *
      variance (fun p : E n × E n => ‖p.1 - p.2‖) ((ballUnif n).prod (ballUnif n)) := by
    rw [← hj, variance_map (by fun_prop) ((hs.comp hX).prodMk (hs.comp hY)).aemeasurable,
      ← variance_const_mul]
    congr 1
    funext ω
    simp only [Function.comp_apply, ← smul_sub, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hr]
    field_simp
  have e2 : variance (fun ω => ‖X ω‖) P = r ^ 2 * variance (fun x : E n => ‖x‖) (ballUnif n) := by
    rw [← hlaw X hX hlX, variance_map (by fun_prop) (hs.comp hX).aemeasurable,
      ← variance_const_mul]
    congr 1
    funext ω
    simp only [Function.comp_apply, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
    field_simp
  rw [e1, e2, mul_div_mul_left _ _ (pow_ne_zero 2 hr.ne')]
  rfl

/-- **Conjecture 00000007793 is false (random-variable form).** Let, for each dimension `n`,
`X n, Y n` be independent random variables, both uniform on the ball of radius `r n > 0` in `ℝⁿ`
(`r n = 1` for the unit ball, `r n = √(n+2)` for isotropic position). Then
`Var|X n - Y n| / Var|X n|` is not `2 - 2/√3 + O(1/n)` as `n → ∞`. -/
theorem not_conjecture_rv {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)] (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (X Y : ∀ n, Ω n → E n) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hind : ∀ n, IndepFun (X n) (Y n) (P n))
    (hlX : ∀ n, (P n).map (X n) = ballUnifR n (r n))
    (hlY : ∀ n, (P n).map (Y n) = ballUnifR n (r n)) :
    ¬ (fun n => variance (fun ω => ‖X n ω - Y n ω‖) (P n) / variance (fun ω => ‖X n ω‖) (P n)
        - (2 - 2 / Real.sqrt 3)) =O[atTop] (fun n : ℕ => (1 : ℝ) / n) := by
  have h : (fun n => variance (fun ω => ‖X n ω - Y n ω‖) (P n) / variance (fun ω => ‖X n ω‖) (P n)
      - (2 - 2 / Real.sqrt 3)) = fun n => ratio n - (2 - 2 / Real.sqrt 3) := by
    funext n
    rw [ratio_eq_of_indep (hr n) (hX n) (hY n) (hind n) (hlX n) (hlY n)]
  rw [h]
  exact not_conjecture

end C7793
