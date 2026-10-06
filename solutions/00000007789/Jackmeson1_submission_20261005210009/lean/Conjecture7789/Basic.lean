import Mathlib

/-!
# Conjecture 00000007789: the worst-case log-concave CLT distance is not `O(n^{-1/2})`

The conjecture's Definition (both languages) sets
`d_n = sup { d_K(<X, theta>, N(0,1)) : X isotropic log-concave in R^n, theta in S^{n-1} }`,
the worst Kolmogorov distance over `X` *and* directions `theta`, and claims `d_n = O(n^{-1/2})`
(together with further clauses about the extremal measure).

We refute the first clause, which refutes the conjunction.
Witness: `X` uniform on the cube `[-sqrt 3, sqrt 3]^n`, `theta = e_0`. Then `<X, theta>` is
uniform on `[-sqrt 3, sqrt 3]`, whose cdf equals `1` at `t = sqrt 3`, while `Phi (sqrt 3) < 1`.
So `d_n >= 1 - Phi (sqrt 3) > 0` for every `n >= 1`.

Conventions.
* `R^n` is `Fin n -> R` with Lebesgue measure `volume` (the product of the 1-D Lebesgue measures);
  directions are vectors with `sum_i theta_i ^ 2 = 1` (the Euclidean unit sphere);
  `<x, theta> = sum_i theta_i * x_i`.
* A measure is log-concave if it has a log-concave Lebesgue density `f`
  (`f >= 0` measurable and `f (t x + (1 - t) y) >= f x ^ t * f y ^ (1 - t)` for `0 < t < 1`).
* Isotropic: probability measure with finite second moments, mean `0`, covariance `I`.
* Kolmogorov distance to `N(0,1)`: `sup_t |F_nu t - Phi t|`, with Mathlib's `cdf` and
  `gaussianReal 0 1`.
-/

open MeasureTheory ProbabilityTheory Filter Asymptotics Set

namespace Conjecture7789

/-- A function `f : R^n -> R` is log-concave: nonnegative, measurable and
`f (t x + (1 - t) y) >= f x ^ t * f y ^ (1 - t)` for all `x, y` and `0 < t < 1`. -/
def IsLogConcaveFun {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧
    ∀ x y : Fin n → ℝ, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)

/-- A measure on `R^n` is log-concave if it has a log-concave density with respect to
Lebesgue measure. -/
def IsLogConcave {n : ℕ} (μ : Measure (Fin n → ℝ)) : Prop :=
  ∃ f : (Fin n → ℝ) → ℝ, IsLogConcaveFun f ∧ μ = volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- An isotropic probability measure on `R^n`: finite second moments, mean zero and identity
covariance. -/
def IsIsotropic {n : ℕ} (μ : Measure (Fin n → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ i, Integrable (fun x => x i ^ 2) μ) ∧
    (∀ i, ∫ x, x i ∂μ = 0) ∧ ∀ i j, ∫ x, x i * x j ∂μ = if i = j then 1 else 0

/-- The projection `x ↦ <x, theta>`. -/
def proj {n : ℕ} (θ : Fin n → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, θ i * x i

/-- Kolmogorov distance from a law `ν` on `R` to the standard normal law `N(0,1)`. -/
noncomputable def kolmogorovToStdNormal (ν : Measure ℝ) : ℝ :=
  ⨆ t : ℝ, |cdf ν t - cdf (gaussianReal 0 1) t|

/-- The conjecture's `d_n`: the worst Kolmogorov distance to `N(0,1)` of a one-dimensional
projection `<X, theta>`, over isotropic log-concave `X` in `R^n` and unit directions `theta`. -/
noncomputable def worstDist (n : ℕ) : ℝ :=
  sSup {r | ∃ μ : Measure (Fin n → ℝ), ∃ θ : Fin n → ℝ,
    IsIsotropic μ ∧ IsLogConcave μ ∧ ∑ i, θ i ^ 2 = 1 ∧
      r = kolmogorovToStdNormal (μ.map (proj θ))}

lemma abs_cdf_sub_le_one (ν : Measure ℝ) (t : ℝ) :
    |cdf ν t - cdf (gaussianReal 0 1) t| ≤ 1 := by
  have h1 := cdf_nonneg ν t; have h2 := cdf_le_one ν t
  have h3 := cdf_nonneg (gaussianReal 0 1) t; have h4 := cdf_le_one (gaussianReal 0 1) t
  rw [abs_le]; constructor <;> linarith

lemma kolmogorov_le_one (ν : Measure ℝ) : kolmogorovToStdNormal ν ≤ 1 :=
  ciSup_le (abs_cdf_sub_le_one ν)

lemma le_kolmogorov (ν : Measure ℝ) (t : ℝ) :
    |cdf ν t - cdf (gaussianReal 0 1) t| ≤ kolmogorovToStdNormal ν :=
  le_ciSup (f := fun t => |cdf ν t - cdf (gaussianReal 0 1) t|) ⟨1, by
    rintro _ ⟨s, rfl⟩; exact abs_cdf_sub_le_one ν s⟩ t

/-! ## The uniform law on `[-sqrt 3, sqrt 3]` -/

/-- The interval `[-sqrt 3, sqrt 3]`. -/
def I : Set ℝ := Icc (-Real.sqrt 3) (Real.sqrt 3)

/-- The uniform density height `1 / (2 sqrt 3)`. -/
noncomputable def c : ℝ := 1 / (2 * Real.sqrt 3)

lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

lemma c_pos : 0 < c := by unfold c; have := sqrt3_pos; positivity

/-- The uniform law on `[-sqrt 3, sqrt 3]`. -/
noncomputable def U : Measure ℝ := ENNReal.ofReal c • volume.restrict I

lemma volume_I : volume I = ENNReal.ofReal (2 * Real.sqrt 3) := by
  rw [I, Real.volume_Icc]; ring_nf

instance : IsProbabilityMeasure U := by
  constructor
  rw [U, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, volume_I,
    smul_eq_mul, ← ENNReal.ofReal_mul c_pos.le]
  have : c * (2 * Real.sqrt 3) = 1 := by unfold c; have := sqrt3_pos; field_simp
  rw [this, ENNReal.ofReal_one]

lemma integral_U (g : ℝ → ℝ) : ∫ y, g y ∂U = c * ∫ y in (-Real.sqrt 3)..(Real.sqrt 3), g y := by
  rw [U, integral_smul_measure, ENNReal.toReal_ofReal c_pos.le, smul_eq_mul, I,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [sqrt3_pos])]

lemma mean_U : ∫ y, y ∂U = 0 := by
  rw [integral_U, integral_id]; ring

lemma second_moment_U : ∫ y, y * y ∂U = 1 := by
  rw [integral_U]
  simp_rw [← sq]
  rw [integral_pow]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have : Real.sqrt 3 ^ (2 + 1) = 3 * Real.sqrt 3 := by rw [pow_succ, h3]
  unfold c
  rw [neg_pow, this]
  have := sqrt3_pos
  field_simp
  norm_num

lemma integrable_sq_U : Integrable (fun y : ℝ => y ^ 2) U := by
  rw [U]
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  exact (continuous_pow 2).integrableOn_Icc

lemma cdf_U_sqrt3 : cdf U (Real.sqrt 3) = 1 := by
  rw [cdf_eq_real, measureReal_def, U, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iic]
  have : Iic (Real.sqrt 3) ∩ I = I := inter_eq_right.2 (fun y hy => hy.2)
  rw [this, volume_I, smul_eq_mul, ← ENNReal.ofReal_mul c_pos.le]
  have : c * (2 * Real.sqrt 3) = 1 := by unfold c; have := sqrt3_pos; field_simp
  rw [this, ENNReal.ofReal_one, ENNReal.toReal_one]

/-! ## The uniform law on the cube -/

/-- The cube `[-sqrt 3, sqrt 3]^n`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ => I

/-- The density of the uniform law on the cube: `c^n` on the cube, `0` outside. -/
noncomputable def cubeDensity (n : ℕ) : (Fin n → ℝ) → ℝ := (cube n).indicator fun _ => c ^ n

/-- The uniform law on the cube, as a product of `n` copies of `U`. -/
noncomputable def cubeLaw (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => U

lemma measurableSet_cube (n : ℕ) : MeasurableSet (cube n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma cubeDensity_logConcave (n : ℕ) : IsLogConcaveFun (cubeDensity n) := by
  have hc : 0 < c ^ n := pow_pos c_pos n
  have hconv : Convex ℝ (cube n) := convex_pi fun _ _ => convex_Icc _ _
  refine ⟨measurable_const.indicator (measurableSet_cube n), fun x => ?_, ?_⟩
  · unfold cubeDensity; by_cases hx : x ∈ cube n <;> simp [hx, hc.le]
  intro x y t ht0 ht1
  unfold cubeDensity
  by_cases hx : x ∈ cube n
  · by_cases hy : y ∈ cube n
    · have hm : t • x + (1 - t) • y ∈ cube n :=
        hconv hx hy ht0.le (by linarith) (by ring)
      rw [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hm,
        ← Real.rpow_add hc]
      simp
    · rw [indicator_of_notMem hy, Real.zero_rpow (by linarith), mul_zero]
      exact indicator_nonneg (fun _ _ => hc.le) _
  · rw [indicator_of_notMem hx, Real.zero_rpow ht0.ne', zero_mul]
    exact indicator_nonneg (fun _ _ => hc.le) _

/-- The product law equals Lebesgue measure with density `cubeDensity n`. -/
lemma cubeLaw_eq_withDensity (n : ℕ) :
    cubeLaw n = volume.withDensity (fun x => ENNReal.ofReal (cubeDensity n x)) := by
  have hfun : (fun x => ENNReal.ofReal (cubeDensity n x)) =
      (cube n).indicator fun _ => ENNReal.ofReal (c ^ n) := by
    funext x; unfold cubeDensity
    by_cases hx : x ∈ cube n <;> simp [hx]
  rw [hfun, withDensity_indicator (measurableSet_cube n), withDensity_const]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs), cube,
    ← Set.pi_inter_distrib, volume_pi_pi, smul_eq_mul, ENNReal.ofReal_pow c_pos.le]
  have hU : ∏ i, U (s i) = ∏ i : Fin n, (ENNReal.ofReal c * volume (s i ∩ I)) :=
    Finset.prod_congr rfl fun i _ => by
      rw [U, Measure.smul_apply, Measure.restrict_apply (hs i), smul_eq_mul]
  rw [hU, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma cubeLaw_logConcave (n : ℕ) : IsLogConcave (cubeLaw n) :=
  ⟨cubeDensity n, cubeDensity_logConcave n, cubeLaw_eq_withDensity n⟩

lemma cubeLaw_isotropic (n : ℕ) : IsIsotropic (cubeLaw n) := by
  refine ⟨by unfold cubeLaw; infer_instance, fun i => ?_, fun i => ?_, fun i j => ?_⟩
  · exact integrable_comp_eval (μ := fun _ => U) integrable_sq_U
  · rw [cubeLaw, integral_eval]; exact mean_U
  · by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, cubeLaw,
        integral_comp_eval (μ := fun _ => U) (f := fun y => y * y) (by fun_prop)]
      exact second_moment_U
    · rw [if_neg hij, cubeLaw]
      have hind : iIndepFun (fun k (ω : Fin n → ℝ) => ω k) (Measure.pi fun _ => U) :=
        iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
      rw [(hind.indepFun hij).integral_fun_mul_eq_mul_integral
          (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable,
        integral_eval, mean_U, zero_mul]

/-! ## The lower bound -/

/-- `Phi (sqrt 3) < 1`. -/
lemma cdf_gauss_sqrt3_lt_one : cdf (gaussianReal 0 1) (Real.sqrt 3) < 1 := by
  have hpos : gaussianReal 0 1 (Ioi (Real.sqrt 3)) ≠ 0 := by
    intro h
    have := gaussianReal_absolutelyContinuous' 0 (one_ne_zero) h
    rw [Real.volume_Ioi] at this
    exact ENNReal.top_ne_zero this
  rw [cdf_eq_real, ← compl_Ioi, measureReal_compl measurableSet_Ioi, probReal_univ]
  have : 0 < (gaussianReal 0 1).real (Ioi (Real.sqrt 3)) :=
    ENNReal.toReal_pos hpos (measure_ne_top _ _)
  linarith

/-- The gap `delta = 1 - Phi (sqrt 3) > 0`. -/
noncomputable def delta : ℝ := 1 - cdf (gaussianReal 0 1) (Real.sqrt 3)

lemma delta_pos : 0 < delta := by unfold delta; linarith [cdf_gauss_sqrt3_lt_one]

/-- The coordinate projection of the cube law is the uniform law `U`. -/
lemma map_proj_cubeLaw {n : ℕ} (i : Fin n) :
    (cubeLaw n).map (proj (Pi.single i 1)) = U := by
  have : proj (Pi.single i (1 : ℝ)) = fun x : Fin n → ℝ => x i := by
    funext x; simp [proj, Pi.single_apply]
  rw [this, cubeLaw]
  exact (measurePreserving_eval (fun _ : Fin n => U) i).map_eq

/-- The worst-case distance is bounded below by `delta > 0` in every dimension `n >= 1`. -/
theorem delta_le_worstDist (n : ℕ) (hn : 1 ≤ n) : delta ≤ worstDist n := by
  let i : Fin n := ⟨0, hn⟩
  have hmem : kolmogorovToStdNormal U ∈ {r | ∃ μ : Measure (Fin n → ℝ), ∃ θ : Fin n → ℝ,
      IsIsotropic μ ∧ IsLogConcave μ ∧ ∑ i, θ i ^ 2 = 1 ∧
        r = kolmogorovToStdNormal (μ.map (proj θ))} :=
    ⟨cubeLaw n, Pi.single i 1, cubeLaw_isotropic n, cubeLaw_logConcave n,
      by simp [Pi.single_apply], by rw [map_proj_cubeLaw]⟩
  have hbdd : BddAbove {r | ∃ μ : Measure (Fin n → ℝ), ∃ θ : Fin n → ℝ,
      IsIsotropic μ ∧ IsLogConcave μ ∧ ∑ i, θ i ^ 2 = 1 ∧
        r = kolmogorovToStdNormal (μ.map (proj θ))} := by
    refine ⟨1, ?_⟩
    rintro r ⟨μ, θ, -, -, -, rfl⟩
    exact kolmogorov_le_one _
  refine le_trans ?_ (le_csSup hbdd hmem)
  have h := le_kolmogorov U (Real.sqrt 3)
  rw [cdf_U_sqrt3, abs_of_nonneg (by linarith [cdf_gauss_sqrt3_lt_one])] at h
  exact h

/-- **Main theorem.** The worst-case distance `d_n` is not `O(n^{-1/2})`. -/
theorem worstDist_not_isBigO :
    ¬ (worstDist =O[atTop] fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  intro h
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h0 : Tendsto worstDist atTop (nhds 0) := h.trans_tendsto ht
  have hlt : ∀ᶠ n in atTop, worstDist n < delta := h0.eventually (gt_mem_nhds delta_pos)
  obtain ⟨n, hn1, hn2⟩ := (hlt.and (eventually_ge_atTop 1)).exists
  exact absurd (delta_le_worstDist n hn2) (not_le.2 hn1)

/-- The conjecture is the conjunction of `d_n = O(n^{-1/2})` with further clauses `P`
(about the extremal measure and directions); the conjunction fails whatever `P` is. -/
theorem conjecture_false (P : Prop) :
    ¬ ((worstDist =O[atTop] fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) ∧ P) :=
  fun h => worstDist_not_isBigO h.1

end Conjecture7789
