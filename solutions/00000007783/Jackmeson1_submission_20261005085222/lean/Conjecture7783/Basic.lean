import Mathlib

/-!
# Conjecture 00000007783: the thin-shell constant is not of order `n^(-1/4)`

Work in `ℝ^n = EuclideanSpace ℝ (Fin n)` with Lebesgue measure `volume`.  For a set `K`, the
uniform probability law on `K` is `volume[|K] = (volume K)⁻¹ • volume.restrict K`.
A convex body is a compact convex set with nonempty interior.  It is *isotropic* (the
conjecture's "isotropic uniform sample") if `X ~ volume[|K]` has `E X = 0` and
`E[X_i X_j] = δ_ij`.  The thin-shell quantity of `K` is the standard deviation
`sqrt (Var ‖X‖)` of the Euclidean norm, with Mathlib's `variance`.

The conjecture asserts `σ_n = Θ(n^(-1/4))` for `σ_n = sup_K sd_K`, and that every isotropic
body has `sd_K` between the ball value and `c n^(-1/4)`.  We show that the cube
`[-√3, √3]^n` is an isotropic convex body with `sd ≥ 1/√15` in every dimension `n ≥ 1`, so no
bound `sd_K ≤ C n^(-1/4)` holds for all isotropic bodies in all large dimensions.
The same holds in the volume-one convention (cube `[-1/2,1/2]^n`, `sd ≥ 1/√180`).
-/

open MeasureTheory ProbabilityTheory Set Finset Filter Topology

namespace C7783

variable {n : ℕ}

/-- The cube `[-a,a]^n` in `ℝ^n = EuclideanSpace ℝ (Fin n)`. -/
def cube (n : ℕ) (a : ℝ) : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, x i ∈ Icc (-a) a}

/-- A convex body: compact, convex, with nonempty interior. -/
def IsConvexBody (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- Isotropic convex body: the uniform random vector `X ~ volume[|K]` has mean `0` and
identity covariance. -/
def IsIsotropicConvexBody (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsConvexBody K ∧ (∀ i, ∫ x, x i ∂(volume[|K]) = 0) ∧
    ∀ i j, ∫ x, x i * x j ∂(volume[|K]) = if i = j then 1 else 0

/-- Isotropic convex body in the volume-one convention: volume `1`, barycenter `0` and
covariance `L_K^2 • I` for some `L_K > 0`. -/
def IsIsotropicConvexBodyVolOne (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsConvexBody K ∧ volume K = 1 ∧ (∀ i, ∫ x, x i ∂(volume[|K]) = 0) ∧
    ∃ L : ℝ, 0 < L ∧ ∀ i j, ∫ x, x i * x j ∂(volume[|K]) = if i = j then L ^ 2 else 0

/-- The thin-shell quantity of `K`: standard deviation of `‖X‖` for `X` uniform on `K`. -/
noncomputable def thinShell (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  Real.sqrt (variance (fun x => ‖x‖) (volume[|K]))

/-- The thin-shell constant `σ_n`: the supremum (in `[0, ∞]`) over isotropic convex bodies. -/
noncomputable def sigma (n : ℕ) : ENNReal :=
  ⨆ (K : Set (EuclideanSpace ℝ (Fin n))) (_ : IsIsotropicConvexBody K), ENNReal.ofReal (thinShell K)

/-! ### The cube: geometry and change of variables -/

lemma cube_eq (a : ℝ) :
    cube n a = (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ⁻¹'
      Set.pi univ (fun _ => Icc (-a) a) := by
  ext x; exact ⟨fun h i _ => h i, fun h i => h i (Set.mem_univ i)⟩

lemma isClosed_cube (a : ℝ) : IsClosed (cube n a) := by
  rw [cube_eq]
  exact (isClosed_set_pi fun _ _ => isClosed_Icc).preimage (PiLp.continuous_ofLp 2 _)

lemma measurableSet_cube (a : ℝ) : MeasurableSet (cube n a) := (isClosed_cube a).measurableSet

lemma norm_sq_le_of_mem_cube {a : ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ cube n a) :
    ‖x‖ ^ 2 ≤ n * a ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin n, a ^ 2 :=
        Finset.sum_le_sum fun i _ => sq_le_sq' (hx i).1 (hx i).2
    _ = n * a ^ 2 := by simp

lemma isConvexBody_cube {a : ℝ} (ha : 0 < a) : IsConvexBody (cube n a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy s t hs ht hst i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    obtain ⟨h1, h2⟩ := hx i
    obtain ⟨h3, h4⟩ := hy i
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h3 ht]
    · nlinarith [mul_le_mul_of_nonneg_left h2 hs, mul_le_mul_of_nonneg_left h4 ht]
  · refine Metric.isCompact_of_isClosed_isBounded (isClosed_cube a) ?_
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n)))
      (r := Real.sqrt (n * a ^ 2))).subset fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Real.le_sqrt_of_sq_le (norm_sq_le_of_mem_cube hx)
  · refine ⟨0, mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (Metric.ball_mem_nhds 0 ha) ?_)⟩
    intro x hx i
    have h1 := PiLp.norm_apply_le x i
    rw [Metric.mem_ball, dist_zero_right] at hx
    rw [Real.norm_eq_abs] at h1
    exact ⟨by linarith [neg_abs_le (x i)], by linarith [le_abs_self (x i)]⟩

/-- Change of variables: integrals over the cube are integrals against a product measure. -/
lemma setIntegral_cube (a : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ x in cube n a, f x =
      ∫ y, f (WithLp.toLp 2 y) ∂(Measure.pi fun _ : Fin n => volume.restrict (Icc (-a) a)) := by
  rw [cube_eq, ← Measure.restrict_pi_pi, ← volume_pi]
  have := (PiLp.volume_preserving_ofLp (Fin n)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding
    (fun y => f (WithLp.toLp 2 y)) (Set.pi univ fun _ => Icc (-a) a)
  simpa using this

lemma volume_cube {a : ℝ} (_ha : 0 ≤ a) :
    volume (cube n a) = ENNReal.ofReal (2 * a) ^ n := by
  rw [cube_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet, volume_pi_pi]
  simp [Real.volume_Icc, two_mul]

/-- Normalized one-dimensional moments `c_m = (2a)⁻¹ ∫_{-a}^{a} t^m dt`. -/
noncomputable def c (a : ℝ) (m : ℕ) : ℝ := (∫ t in Icc (-a) a, t ^ m) / (2 * a)

lemma integral_pow_Icc {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    ∫ t in Icc (-a) a, t ^ m = (a ^ (m + 1) - (-a) ^ (m + 1)) / (m + 1) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), integral_pow]

lemma c_zero {a : ℝ} (ha : 0 < a) : c a 0 = 1 := by
  rw [c, integral_pow_Icc ha.le]; field_simp; ring
lemma c_one {a : ℝ} (ha : 0 < a) : c a 1 = 0 := by
  rw [c, integral_pow_Icc ha.le]; ring
lemma c_two {a : ℝ} (ha : 0 < a) : c a 2 = a ^ 2 / 3 := by
  rw [c, integral_pow_Icc ha.le]; field_simp; ring
lemma c_four {a : ℝ} (ha : 0 < a) : c a 4 = a ^ 4 / 5 := by
  rw [c, integral_pow_Icc ha.le]; field_simp; ring

/-- The uniform law on the cube. -/
noncomputable abbrev μ (n : ℕ) (a : ℝ) : Measure (EuclideanSpace ℝ (Fin n)) := volume[|cube n a]

/-- Moments of monomials under the uniform law on the cube (Fubini). -/
lemma integral_monomial {a : ℝ} (ha : 0 < a) (p : Fin n → ℕ) :
    ∫ x, ∏ i, x i ^ p i ∂(μ n a) = ∏ i, c a (p i) := by
  rw [μ, ProbabilityTheory.cond, integral_smul_measure, setIntegral_cube,
    integral_fintype_prod_eq_prod (fun i t => t ^ p i), volume_cube ha.le]
  simp only [c, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 2 * a),
    smul_eq_mul]
  have : (2 * a) ^ n ≠ 0 := pow_ne_zero _ (by positivity)
  field_simp

lemma isProb (n : ℕ) {a : ℝ} (ha : 0 < a) : IsProbabilityMeasure (μ n a) := by
  refine cond_isProbabilityMeasure_of_finite ?_ ?_ <;> rw [volume_cube ha.le]
  · exact pow_ne_zero _ (by simpa using ha)
  · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

lemma integrable_cont {a : ℝ} (ha : 0 < a) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Continuous f) : Integrable f (μ n a) := by
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 ?_)
  · exact hf.continuousOn.integrableOn_compact (isConvexBody_cube ha).2.1
  · rw [volume_cube ha.le]; exact pow_ne_zero _ (by simpa using ha)

lemma cont_coord (i : Fin n) : Continuous fun x : EuclideanSpace ℝ (Fin n) => x i :=
  PiLp.continuous_apply 2 _ i

/-! ### Products of coordinates as monomials -/

lemma prod_single (x : Fin n → ℝ) (i : Fin n) (u : ℕ) :
    ∏ k, x k ^ (if k = i then u else 0) = x i ^ u :=
  (Fintype.prod_eq_single i fun k hk => by simp [hk]).trans (by simp)

lemma prod_double (x : Fin n → ℝ) (i j : Fin n) (u v : ℕ) :
    ∏ k, x k ^ ((if k = i then u else 0) + (if k = j then v else 0)) = x i ^ u * x j ^ v := by
  simp_rw [pow_add, Finset.prod_mul_distrib, prod_single]

lemma c_single {a : ℝ} (ha : 0 < a) (i : Fin n) (u : ℕ) :
    ∏ k, c a (if k = i then u else 0) = c a u :=
  (Fintype.prod_eq_single i fun k hk => by simp [hk, c_zero ha]).trans (by simp)

lemma c_double {a : ℝ} (ha : 0 < a) {i j : Fin n} (hij : i ≠ j) (u v : ℕ) :
    ∏ k, c a ((if k = i then u else 0) + (if k = j then v else 0)) = c a u * c a v := by
  rw [Fintype.prod_eq_mul i j hij fun k hk => by simp [hk.1, hk.2, c_zero ha]]
  simp [hij, hij.symm]

lemma mean_coord {a : ℝ} (ha : 0 < a) (i : Fin n) : ∫ x, x i ∂(μ n a) = 0 := by
  have := integral_monomial ha (fun k => if k = i then 1 else 0)
  simp only [prod_single, pow_one, c_single ha, c_one ha] at this
  exact this

lemma cov_coord {a : ℝ} (ha : 0 < a) (i j : Fin n) :
    ∫ x, x i * x j ∂(μ n a) = if i = j then a ^ 2 / 3 else 0 := by
  by_cases hij : i = j
  · subst hij
    have := integral_monomial ha (fun k => if k = i then 2 else 0)
    simp only [prod_single, c_single ha, c_two ha] at this
    simpa [sq] using this
  · have := integral_monomial ha (fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0))
    simp only [prod_double, pow_one, c_double ha hij, c_one ha, zero_mul] at this
    simpa [hij] using this

lemma fourth_coord {a : ℝ} (ha : 0 < a) (i j : Fin n) :
    ∫ x, x i ^ 2 * x j ^ 2 ∂(μ n a) =
      a ^ 4 / 9 + if i = j then a ^ 4 / 5 - a ^ 4 / 9 else 0 := by
  by_cases hij : i = j
  · subst hij
    have := integral_monomial ha (fun k => if k = i then 4 else 0)
    simp only [prod_single, c_single ha, c_four ha] at this
    rw [show (fun x : EuclideanSpace ℝ (Fin n) => x i ^ 2 * x i ^ 2) = fun x => x i ^ 4 by
      funext x; ring, this]
    simp
  · have := integral_monomial ha (fun k => (if k = i then 2 else 0) + (if k = j then 2 else 0))
    simp only [prod_double, c_double ha hij, c_two ha] at this
    rw [this]; simp [hij]; ring

/-! ### Second and fourth moments of `‖X‖` on the cube -/

lemma moment_two {a : ℝ} (ha : 0 < a) : ∫ x, ‖x‖ ^ 2 ∂(μ n a) = n * (a ^ 2 / 3) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ fun i _ =>
    integrable_cont ha (f := fun x => x i ^ 2) ((cont_coord i).pow 2)]
  simp_rw [sq, cov_coord ha]; simp; left; ring

lemma moment_four {a : ℝ} (ha : 0 < a) :
    ∫ x, ‖x‖ ^ 4 ∂(μ n a) = n ^ 2 * (a ^ 4 / 9) + n * (a ^ 4 / 5 - a ^ 4 / 9) := by
  have h4 : (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 4) =
      fun x => ∑ i, ∑ j, x i ^ 2 * x j ^ 2 := by
    funext x
    rw [show ‖x‖ ^ 4 = ‖x‖ ^ 2 * ‖x‖ ^ 2 by ring, EuclideanSpace.real_norm_sq_eq,
      Finset.sum_mul_sum]
  have hint : ∀ i j : Fin n, Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i ^ 2 * x j ^ 2)
      (μ n a) := fun i j => integrable_cont ha
        (((cont_coord i).pow 2).mul ((cont_coord j).pow 2))
  rw [h4, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp_rw [integral_finsetSum _ fun j _ => hint _ j, fourth_coord ha, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp; ring

/-! ### Variance lower bound -/

/-- On the cube `[-a,a]^n` (`n ≥ 1`), `Var ‖X‖ ≥ a^2 / 45`. -/
theorem variance_norm_cube {a : ℝ} (ha : 0 < a) (hn : 1 ≤ n) :
    a ^ 2 / 45 ≤ variance (fun x => ‖x‖) (μ n a) := by
  have := isProb n ha
  set m := ∫ x, ‖x‖ ∂(μ n a) with hm
  set b := Real.sqrt (n * a ^ 2)
  have hb2 : b ^ 2 = n * a ^ 2 := Real.sq_sqrt (by positivity)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hae : ∀ᵐ x ∂(μ n a), ‖x‖ ≤ b := (ae_cond_mem (measurableSet_cube a)).mono
    fun x hx => Real.le_sqrt_of_sq_le (norm_sq_le_of_mem_cube hx)
  have hm0 : 0 ≤ m := integral_nonneg fun _ => norm_nonneg _
  have hmb : m ≤ b := by
    have := integral_mono_ae (integrable_cont ha continuous_norm) (integrable_const b) hae
    simpa using this
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ := continuous_norm
  rw [variance_eq_integral hcont.aemeasurable]
  -- pointwise: (r^2 - m^2)^2 ≤ 4 b^2 (r - m)^2
  have hpt : ∀ᵐ x ∂(μ n a), (‖x‖ ^ 2 - m ^ 2) ^ 2 ≤ 4 * b ^ 2 * (‖x‖ - m) ^ 2 :=
    hae.mono fun x hx => by
      have h0 := norm_nonneg x
      have : (‖x‖ + m) ^ 2 ≤ (2 * b) ^ 2 := by nlinarith
      calc (‖x‖ ^ 2 - m ^ 2) ^ 2 = (‖x‖ - m) ^ 2 * (‖x‖ + m) ^ 2 := by ring
        _ ≤ (‖x‖ - m) ^ 2 * (2 * b) ^ 2 := mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = 4 * b ^ 2 * (‖x‖ - m) ^ 2 := by ring
  have hI : ∫ x, (‖x‖ ^ 2 - m ^ 2) ^ 2 ∂(μ n a) ≤ 4 * b ^ 2 * ∫ x, (‖x‖ - m) ^ 2 ∂(μ n a) := by
    rw [← integral_const_mul]
    exact integral_mono_ae (integrable_cont ha ((hcont.pow 2).sub continuous_const |>.pow 2))
      (integrable_cont ha (continuous_const.mul ((hcont.sub continuous_const).pow 2))) hpt
  -- expand the left side
  have hexp : ∫ x, (‖x‖ ^ 2 - m ^ 2) ^ 2 ∂(μ n a) =
      ∫ x, ‖x‖ ^ 4 ∂(μ n a) - 2 * m ^ 2 * ∫ x, ‖x‖ ^ 2 ∂(μ n a) + m ^ 4 := by
    have e : (fun x : EuclideanSpace ℝ (Fin n) => (‖x‖ ^ 2 - m ^ 2) ^ 2) =
        fun x => (‖x‖ ^ 4 - 2 * m ^ 2 * ‖x‖ ^ 2) + m ^ 4 := by funext x; ring
    have i1 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 4) (μ n a) :=
      integrable_cont ha (f := fun x => ‖x‖ ^ 4) (hcont.pow 4)
    have i2 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => 2 * m ^ 2 * ‖x‖ ^ 2) (μ n a) :=
      integrable_cont ha (f := fun x => 2 * m ^ 2 * ‖x‖ ^ 2) (continuous_const.mul (hcont.pow 2))
    have i3 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 4 - 2 * m ^ 2 * ‖x‖ ^ 2)
      (μ n a) := i1.sub i2
    rw [e, integral_add i3 (integrable_const _), integral_sub i1 i2, integral_const_mul]
    simp
  rw [hexp, moment_four ha, moment_two ha, hb2] at hI
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have key : 4 * (n * a ^ 2) * (a ^ 2 / 45) ≤ 4 * (n * a ^ 2) * ∫ x, (‖x‖ - m) ^ 2 ∂(μ n a) := by
    nlinarith [sq_nonneg (n * (a ^ 2 / 3) - m ^ 2)]
  exact le_of_mul_le_mul_left key (by positivity)

/-! ### The cube is isotropic (both conventions) -/

lemma isIsotropic_cube (n : ℕ) : IsIsotropicConvexBody (cube n (Real.sqrt 3)) := by
  have ha : 0 < Real.sqrt 3 := by positivity
  refine ⟨isConvexBody_cube ha, mean_coord ha, fun i j => ?_⟩
  rw [cov_coord ha]; simp

lemma isIsotropicVolOne_cube (n : ℕ) : IsIsotropicConvexBodyVolOne (cube n (1 / 2)) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  refine ⟨isConvexBody_cube ha, by rw [volume_cube ha.le]; norm_num, mean_coord ha,
    Real.sqrt (1 / 12), by positivity, fun i j => ?_⟩
  rw [cov_coord ha, Real.sq_sqrt (by norm_num)]; norm_num

/-! ### Main theorems -/

lemma eventually_small (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ (-(1 / 4 : ℝ)) < ε := by
  have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    tendsto_natCast_atTop_atTop).const_mul C
  rw [mul_zero] at h
  exact h.eventually (gt_mem_nhds hε)

/-- **Main theorem.** There are no constants `C, N` such that every isotropic convex body
`K ⊆ ℝ^n`, `n ≥ N`, has thin-shell quantity `sd(‖X‖) ≤ C n^(-1/4)`.  Hence
`σ_n = Θ(n^(-1/4))` is false, and so is "every isotropic body has `sd ≤ c n^(-1/4)`". -/
theorem not_thinShell_le_rpow :
    ¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ K : Set (EuclideanSpace ℝ (Fin n)),
      IsIsotropicConvexBody K → thinShell K ≤ C * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  rintro ⟨C, N, hC⟩
  obtain ⟨n, hn⟩ := ((eventually_small C (1 / Real.sqrt 15) (by positivity)).and
    (eventually_ge_atTop (max N 1))).exists
  have h1 := hC n (le_of_max_le_left hn.2) _ (isIsotropic_cube n)
  have h2 : 1 / Real.sqrt 15 ≤ thinShell (cube n (Real.sqrt 3)) := by
    rw [thinShell, show (1 : ℝ) / Real.sqrt 15 = Real.sqrt (Real.sqrt 3 ^ 2 / 45) by
      rw [Real.sq_sqrt (by norm_num), show (3 : ℝ) / 45 = 1 / 15 by norm_num, Real.sqrt_div' _
        (by norm_num : (0 : ℝ) ≤ 15), Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (variance_norm_cube (by positivity) (le_of_max_le_right hn.2))
  linarith [hn.1]

/-- The same statement for `σ_n` itself, defined as a supremum in `[0, ∞]`. -/
theorem not_sigma_le_rpow :
    ¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, sigma n ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by
  rintro ⟨C, N, hC⟩
  refine not_thinShell_le_rpow ⟨max C 0, N, fun n hn K hK => ?_⟩
  have hpos : 0 ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h := ((le_iSup₂ (f := fun (K : Set (EuclideanSpace ℝ (Fin n)))
    (_ : IsIsotropicConvexBody K) => ENNReal.ofReal (thinShell K)) K hK).trans (hC n hn)).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left C 0) hpos))
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_max_right C 0) hpos)).1 h

/-- Volume-one convention: the same failure. -/
theorem not_thinShell_le_rpow_volOne :
    ¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ K : Set (EuclideanSpace ℝ (Fin n)),
      IsIsotropicConvexBodyVolOne K → thinShell K ≤ C * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  rintro ⟨C, N, hC⟩
  obtain ⟨n, hn⟩ := ((eventually_small C (1 / Real.sqrt 180) (by positivity)).and
    (eventually_ge_atTop (max N 1))).exists
  have h1 := hC n (le_of_max_le_left hn.2) _ (isIsotropicVolOne_cube n)
  have h2 : 1 / Real.sqrt 180 ≤ thinShell (cube n (1 / 2)) := by
    rw [thinShell, show (1 : ℝ) / Real.sqrt 180 = Real.sqrt ((1 / 2 : ℝ) ^ 2 / 45) by
      rw [show ((1 / 2 : ℝ) ^ 2 / 45) = 1 / 180 by norm_num, Real.sqrt_div' _
        (by norm_num : (0 : ℝ) ≤ 180), Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (variance_norm_cube (by positivity) (le_of_max_le_right hn.2))
  linarith [hn.1]

end C7783
