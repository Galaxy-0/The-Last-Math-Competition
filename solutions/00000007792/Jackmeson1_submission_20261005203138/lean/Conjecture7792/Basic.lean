import Mathlib

/-!
# Conjecture 00000007792: the M-ellipsoid constant is at least 4

The conjecture's first clause says the optimal constant `C` in the M-ellipsoid condition
`vol(K + E) vol(K° + E°) ≤ C^n vol(K) vol(K°)` satisfies `C ≤ (π/4) e ≈ 2.135`.
We show that for the Euclidean unit ball `B` in every dimension `n` and every (possibly
non-centred, non-degenerate) ellipsoid `E`,
`vol(B + E) vol(B° + E°) ≥ 4^n vol(B) vol(B°)`, so every admissible constant is `≥ 4`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise InnerProductSpace

noncomputable section

namespace Conjecture7792

/-- The ambient space `ℝⁿ` with the Euclidean inner product and Lebesgue measure `volume`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The polar body `K° = {y | ∀ x ∈ K, ⟪x, y⟫ ≤ 1}` (polarity with respect to the origin). -/
def polar (K : Set (Rn n)) : Set (Rn n) := {y | ∀ x ∈ K, ⟪x, y⟫_ℝ ≤ 1}

/-- A (non-degenerate) ellipsoid: the image of the closed unit ball under an invertible affine
map `x ↦ c + A x`. The centre `c` is arbitrary. -/
def IsEllipsoid (E : Set (Rn n)) : Prop :=
  ∃ (c : Rn n) (A : Rn n ≃ₗ[ℝ] Rn n), E = (fun x => c + A x) '' closedBall 0 1

/-- A convex body: a compact convex set with nonempty interior. -/
def IsConvexBody (K : Set (Rn n)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- `E` is an M-ellipsoid of `K` with constant `C`:
`vol(K + E) vol(K° + E°) ≤ C^n vol(K) vol(K°)` (Minkowski sums, Lebesgue measure). -/
def MEllipsoidCondition (C : ℝ) (K E : Set (Rn n)) : Prop :=
  IsEllipsoid E ∧
    volume (K + E) * volume (polar K + polar E) ≤
      ENNReal.ofReal (C ^ n) * volume K * volume (polar K)

/-- `C` is an admissible M-ellipsoid constant in dimension `n`: every convex body with the
origin in its interior has an ellipsoid satisfying the M-ellipsoid condition with constant `C`. -/
def AdmissibleConstant (n : ℕ) (C : ℝ) : Prop :=
  ∀ K : Set (Rn n), IsConvexBody K → (0 : Rn n) ∈ interior K → ∃ E, MEllipsoidCondition C K E

/-- The unit ball is its own polar. -/
theorem polar_closedBall : polar (closedBall (0 : Rn n) 1) = closedBall 0 1 := by
  ext y
  simp only [polar, Set.mem_ofPred_eq, mem_closedBall_zero_iff]
  constructor
  · intro h
    by_cases hy : y = 0
    · simp [hy]
    · have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have h1 := h (‖y‖⁻¹ • y) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne'])
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at h1
      have h2 : ‖y‖⁻¹ * ‖y‖ ^ 2 = ‖y‖ := by field_simp
      linarith
  · intro hy x hx
    calc ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
      _ ≤ 1 := by nlinarith [norm_nonneg x, norm_nonneg y]

/-- The unit ball is a convex body with the origin in its interior. -/
theorem closedBall_isConvexBody :
    IsConvexBody (closedBall (0 : Rn n) 1) ∧ (0 : Rn n) ∈ interior (closedBall 0 1) := by
  have h0 : (0 : Rn n) ∈ interior (closedBall 0 1) :=
    ball_subset_interior_closedBall (mem_ball_self one_pos)
  exact ⟨⟨convex_closedBall 0 1, isCompact_closedBall 0 1, ⟨0, h0⟩⟩, h0⟩

lemma volume_image_add_left (a : Rn n) (S : Set (Rn n)) :
    volume ((fun w => a + w) '' S) = volume S := by
  rw [Set.image_add_left]; exact measure_preimage_add _ _ _

/-- Elementary inequality behind the non-centred case: with `k = (1 + ‖d‖)⁻¹`,
`⟪d, x - k d⟫ + ‖x - k d‖ ≤ 1` whenever `‖x‖ ≤ 1`. -/
lemma key_ineq (d x : Rn n) (hx : ‖x‖ ≤ 1) :
    ⟪d, x - (1 + ‖d‖)⁻¹ • d⟫_ℝ + ‖x - (1 + ‖d‖)⁻¹ • d‖ ≤ 1 := by
  set r := ‖d‖ with hr
  set k := (1 + r)⁻¹ with hk
  set p := ⟪d, x⟫_ℝ with hp
  have hr0 : 0 ≤ r := norm_nonneg d
  have hk0 : 0 < k := by positivity
  have hkr : k * (1 + r) = 1 := inv_mul_cancel₀ (by positivity)
  have hpr : p ≤ r := by
    calc p ≤ ‖d‖ * ‖x‖ := real_inner_le_norm d x
      _ ≤ r := by nlinarith [norm_nonneg x]
  have h1 : ⟪d, x - k • d⟫_ℝ = p - k * r ^ 2 := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have h2 : ‖x - k • d‖ ^ 2 = ‖x‖ ^ 2 - 2 * k * p + k ^ 2 * r ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hk0.le,
      real_inner_comm]
    ring
  have hR0 : 1 - r + k * r ^ 2 = k := by linear_combination (r - 1) * hkr
  have hR : 0 ≤ 1 - p + k * r ^ 2 := by nlinarith
  have h3 : ‖x - k • d‖ ≤ 1 - p + k * r ^ 2 := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero, h2]
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have e : (1 - p + k * r ^ 2) ^ 2 - (‖x‖ ^ 2 - 2 * k * p + k ^ 2 * r ^ 2) =
        (r - p) ^ 2 + 1 - ‖x‖ ^ 2 := by
      linear_combination (2 * p * (1 - r) + r ^ 2 * (k * (r - 1) + 1)) * hkr
    nlinarith [sq_nonneg (r - p)]
  linarith

lemma four_le_mul_inv {s : ℝ} (hs : 0 < s) : 4 ≤ (1 + s) * (1 + s⁻¹) := by
  have e : (1 + s) * (1 + s⁻¹) - 4 = (s - 1) ^ 2 / s := by field_simp; ring
  have : 0 ≤ (s - 1) ^ 2 / s := by positivity
  linarith

/-- **Main estimate.** For the unit ball `B` of `ℝⁿ` (any `n`) and every ellipsoid `E`
(arbitrary centre), `4^n vol(B) vol(B°) ≤ vol(B + E) vol(B° + E°)`. -/
theorem ball_volume_product_ge (E : Set (Rn n)) (hE : IsEllipsoid E) :
    ENNReal.ofReal (4 ^ n) * volume (closedBall (0 : Rn n) 1) *
        volume (polar (closedBall (0 : Rn n) 1)) ≤
      volume (closedBall (0 : Rn n) 1 + E) * volume (polar (closedBall (0 : Rn n) 1) + polar E) := by
  obtain ⟨c, A, rfl⟩ := hE
  rw [polar_closedBall]
  set B : Set (Rn n) := closedBall 0 1 with hB
  set A' : Rn n →ₗ[ℝ] Rn n := A.toLinearMap with hA'
  have hT : (LinearMap.adjoint A' * A').IsSymmetric := LinearMap.isSymmetric_adjoint_mul_self A'
  have hn : Module.finrank ℝ (Rn n) = n := finrank_euclideanSpace_fin
  set v := hT.eigenvectorBasis hn with hv
  set lam := hT.eigenvalues hn with hlam
  have hvon : ∀ i j, ⟪v i, v j⟫_ℝ = if i = j then 1 else 0 := orthonormal_iff_ite.mp v.orthonormal
  have hAAv : ∀ j, LinearMap.adjoint A' (A' (v j)) = lam j • v j := by
    intro j
    have := hT.apply_eigenvectorBasis hn j
    rw [Module.End.mul_apply] at this
    exact this
  have hAv : ∀ i j, ⟪A' (v i), A' (v j)⟫_ℝ = lam j * ⟪v i, v j⟫_ℝ := by
    intro i j
    rw [← LinearMap.adjoint_inner_right, hAAv, real_inner_smul_right]
  have hlam_pos : ∀ j, 0 < lam j := by
    intro j
    have h := hAv j j
    rw [hvon, if_pos rfl, mul_one, real_inner_self_eq_norm_sq] at h
    have hne : A' (v j) ≠ 0 := by
      intro h0
      exact v.orthonormal.ne_zero j (A.injective (by simpa [hA'] using h0))
    rw [← h]; positivity
  set s : Fin n → ℝ := fun j => Real.sqrt (lam j) with hs
  have hs_pos : ∀ j, 0 < s j := fun j => Real.sqrt_pos.mpr (hlam_pos j)
  have hs_sq : ∀ j, s j * s j = lam j := fun j => Real.mul_self_sqrt (hlam_pos j).le
  set u : Fin n → Rn n := fun j => (s j)⁻¹ • A' (v j) with hu
  have hu_on : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [hu, real_inner_smul_left, real_inner_smul_right, hAv, hvon]
    split_ifs with h
    · subst h
      have := (hs_pos i).ne'
      rw [← hs_sq]; field_simp
    · simp
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range u) :=
    (hu_on.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge
  set ub := OrthonormalBasis.mk hu_on hsp with hub_def
  have hub : ∀ i, ub i = u i := fun i => by simp [hub_def]
  have hAvu : ∀ i, A' (v i) = s i • ub i := by
    intro i; rw [hub, hu]; simp only; rw [smul_inv_smul₀ (hs_pos i).ne']
  set Rl : Rn n ≃ₗᵢ[ℝ] Rn n := ub.repr.trans v.repr.symm with hRl_def
  have hRl : ∀ i, Rl (ub i) = v i := by intro i; simp [hRl_def]
  -- diagonal maps in the orthonormal basis `ub`
  let D : (Fin n → ℝ) → (Rn n →ₗ[ℝ] Rn n) := fun a =>
    Matrix.toLin ub.toBasis ub.toBasis (Matrix.diagonal a)
  have hD : ∀ a i, D a (ub i) = a i • ub i := by
    intro a i
    have := Matrix.toLin_self ub.toBasis ub.toBasis (Matrix.diagonal a) i
    simp only [OrthonormalBasis.coe_toBasis, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  have hDdet : ∀ a, LinearMap.det (D a) = ∏ i, a i := by
    intro a; simp [D, LinearMap.det_toLin, Matrix.det_diagonal]
  have hDadd : ∀ a x, D (1 + a) x = x + D a x := by
    intro a x
    have : D (1 + a) = LinearMap.id + D a := ub.toBasis.ext fun i => by
      simp only [OrthonormalBasis.coe_toBasis, LinearMap.add_apply, LinearMap.id_apply, hD,
        Pi.add_apply, Pi.one_apply, add_smul, one_smul]
    rw [this]; rfl
  have hAR : ∀ x, A' (Rl x) = D s x := by
    have : A' ∘ₗ Rl.toLinearEquiv.toLinearMap = D s := ub.toBasis.ext fun i => by
      simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv, hRl, hAvu, hD]
    intro x; exact LinearMap.congr_fun this x
  have hAdj : ∀ x, LinearMap.adjoint A' (D s⁻¹ x) = Rl x := by
    have : LinearMap.adjoint A' ∘ₗ D s⁻¹ = Rl.toLinearEquiv.toLinearMap :=
      ub.toBasis.ext fun i => by
        simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toLinearEquiv, hRl, hD, Pi.inv_apply, map_smul]
        rw [hub, hu]; simp only [map_smul, hAAv, smul_smul]
        rw [← hs_sq]; field_simp [(hs_pos i).ne']; simp
    intro x; exact LinearMap.congr_fun this x
  -- volume of a diagonal image of the ball
  have hvolD : ∀ a : Fin n → ℝ, (∀ i, 0 < a i) →
      volume (D a '' B) = ENNReal.ofReal (∏ i, a i) * volume B := by
    intro a ha
    rw [MeasureTheory.Measure.addHaar_image_linearMap, hDdet,
      abs_of_pos (Finset.prod_pos fun i _ => ha i)]
  -- first factor: `c + (I + D s) B ⊆ B + E`
  have h1 : (fun w => c + w) '' (D (1 + s) '' B) ⊆ B + (fun x => c + A x) '' B := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, c + A (Rl x), ⟨Rl x, ?_, rfl⟩, ?_⟩
    · simpa [hB] using hx
    · rw [hDadd, ← hAR]; simp only [hA', LinearEquiv.coe_coe]; abel
  have hvol1 : ENNReal.ofReal (∏ i, (1 + s i)) * volume B ≤
      volume (B + (fun x => c + A x) '' B) := by
    calc ENNReal.ofReal (∏ i, (1 + s i)) * volume B = volume (D (1 + s) '' B) :=
          (hvolD (1 + s) fun i => by simp only [Pi.add_apply, Pi.one_apply]; linarith [hs_pos i]).symm
      _ = volume ((fun w => c + w) '' (D (1 + s) '' B)) := (volume_image_add_left _ _).symm
      _ ≤ _ := measure_mono h1
  -- second factor: the polar of `E` contains `D s⁻¹ (B - k d)`
  set d := LinearMap.adjoint (D s⁻¹) c with hd
  set k := (1 + ‖d‖)⁻¹ with hk
  have hpol : ∀ x ∈ B, D s⁻¹ (x - k • d) ∈ polar ((fun x => c + A x) '' B) := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := hy
    rw [inner_add_left]
    have e1 : ⟪c, D s⁻¹ (x - k • d)⟫_ℝ = ⟪d, x - k • d⟫_ℝ :=
      (LinearMap.adjoint_inner_left _ _ _).symm
    have e2 : ⟪A x', D s⁻¹ (x - k • d)⟫_ℝ = ⟪x', Rl (x - k • d)⟫_ℝ := by
      rw [← hAdj, LinearMap.adjoint_inner_right]; rfl
    have e3 : ⟪x', Rl (x - k • d)⟫_ℝ ≤ ‖x - k • d‖ := by
      have hx'1 : ‖x'‖ ≤ 1 := by simpa [hB] using hx'
      calc ⟪x', Rl (x - k • d)⟫_ℝ ≤ ‖x'‖ * ‖Rl (x - k • d)‖ := real_inner_le_norm _ _
        _ ≤ 1 * ‖x - k • d‖ := by
          rw [LinearIsometryEquiv.norm_map]; gcongr
        _ = ‖x - k • d‖ := one_mul _
    have := key_ineq d x (by simpa [hB] using hx)
    rw [e1, e2]; linarith
  have h2 : (fun w => -(k • D s⁻¹ d) + w) '' (D (1 + s⁻¹) '' B) ⊆
      B + polar ((fun x => c + A x) '' B) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, D s⁻¹ (x - k • d), hpol x hx, ?_⟩
    beta_reduce
    rw [hDadd, map_sub, map_smul]
    abel
  have hvol2 : ENNReal.ofReal (∏ i, (1 + (s i)⁻¹)) * volume B ≤
      volume (B + polar ((fun x => c + A x) '' B)) := by
    calc ENNReal.ofReal (∏ i, (1 + (s i)⁻¹)) * volume B = volume (D (1 + s⁻¹) '' B) :=
          (hvolD (1 + s⁻¹) fun i => by
            simp only [Pi.add_apply, Pi.one_apply, Pi.inv_apply]
            have := inv_pos.mpr (hs_pos i); linarith).symm
      _ = volume ((fun w => -(k • D s⁻¹ d) + w) '' (D (1 + s⁻¹) '' B)) :=
          (volume_image_add_left _ _).symm
      _ ≤ _ := measure_mono h2
  -- combine
  have h4 : (4 : ℝ) ^ n ≤ (∏ i, (1 + s i)) * ∏ i, (1 + (s i)⁻¹) := by
    rw [← Finset.prod_mul_distrib]
    calc (4 : ℝ) ^ n = ∏ _i : Fin n, (4 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num)
          (fun i _ => four_le_mul_inv (hs_pos i))
  have hp1 : 0 ≤ ∏ i, (1 + s i) := Finset.prod_nonneg fun i _ => by linarith [hs_pos i]
  calc ENNReal.ofReal (4 ^ n) * volume B * volume B
      ≤ ENNReal.ofReal ((∏ i, (1 + s i)) * ∏ i, (1 + (s i)⁻¹)) * volume B * volume B := by
        gcongr
    _ = (ENNReal.ofReal (∏ i, (1 + s i)) * volume B) *
          (ENNReal.ofReal (∏ i, (1 + (s i)⁻¹)) * volume B) := by
        rw [ENNReal.ofReal_mul hp1]; ring
    _ ≤ _ := by gcongr

/-- For the unit ball, any constant `C` for which some ellipsoid satisfies the M-ellipsoid
condition has `4^n ≤ C^n`. -/
theorem ball_condition_pow_ge (C : ℝ) (E : Set (Rn n))
    (h : MEllipsoidCondition C (closedBall (0 : Rn n) 1) E) : (4 : ℝ) ^ n ≤ C ^ n := by
  have hle := (ball_volume_product_ge E h.1).trans h.2
  rw [polar_closedBall] at hle
  set b := volume (closedBall (0 : Rn n) 1) with hb
  have hb0 : b ≠ 0 := (measure_closedBall_pos volume 0 one_pos).ne'
  have hbt : b ≠ ⊤ := measure_closedBall_lt_top.ne
  rw [mul_assoc, mul_assoc] at hle
  have h4 := (ENNReal.mul_le_mul_iff_left (mul_ne_zero hb0 hb0) (ENNReal.mul_ne_top hbt hbt)).mp hle
  rcases ENNReal.ofReal_le_ofReal_iff'.mp h4 with h | h
  · exact h
  · have : (0 : ℝ) < 4 ^ n := by positivity
    linarith

/-- In every dimension `n ≥ 1`, every admissible M-ellipsoid constant satisfies `|C| ≥ 4`. -/
theorem admissible_abs_ge_four (hn : 1 ≤ n) (C : ℝ) (h : AdmissibleConstant n C) : 4 ≤ |C| := by
  obtain ⟨E, hE⟩ := h _ closedBall_isConvexBody.1 closedBall_isConvexBody.2
  have h4 : (4 : ℝ) ^ n ≤ |C| ^ n :=
    (ball_condition_pow_ge C E hE).trans (by rw [← abs_pow]; exact le_abs_self _)
  exact (pow_le_pow_iff_left₀ (by norm_num) (abs_nonneg C) (by omega)).mp h4

/-- In every odd dimension, every admissible constant satisfies `C ≥ 4`. -/
theorem admissible_ge_four_of_odd (hn : Odd n) (C : ℝ) (h : AdmissibleConstant n C) : 4 ≤ C := by
  obtain ⟨E, hE⟩ := h _ closedBall_isConvexBody.1 closedBall_isConvexBody.2
  exact (hn.strictMono_pow (R := ℝ)).le_iff_le.mp (ball_condition_pow_ge C E hE)

/-- A constant that is admissible uniformly in all dimensions is at least `4`
(so the optimal uniform constant, if any, is `≥ 4`). -/
theorem uniform_admissible_ge_four (C : ℝ) (h : ∀ n : ℕ, 1 ≤ n → AdmissibleConstant n C) :
    4 ≤ C :=
  admissible_ge_four_of_odd odd_one C (h 1 le_rfl)

lemma pi_mul_e_div_four_lt_four : Real.pi / 4 * Real.exp 1 < 4 := by
  have h1 := Real.pi_lt_four
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.pi_pos
  have h4 := Real.exp_pos 1
  nlinarith

/-- **Conjecture 00000007792, first clause, is false**: there is no constant `C ≤ (π/4) e`
that is an admissible M-ellipsoid constant in every dimension `n ≥ 1`. -/
theorem conjecture_7792_false :
    ¬ ∃ C : ℝ, C ≤ Real.pi / 4 * Real.exp 1 ∧ ∀ n : ℕ, 1 ≤ n → AdmissibleConstant n C := by
  rintro ⟨C, hC, h⟩
  have := uniform_admissible_ge_four C h
  linarith [pi_mul_e_div_four_lt_four]

/-- Asymptotic reading: no `C ≤ (π/4) e` is admissible in all sufficiently large dimensions. -/
theorem conjecture_7792_false_eventually :
    ¬ ∃ C : ℝ, C ≤ Real.pi / 4 * Real.exp 1 ∧ ∀ᶠ n in atTop, AdmissibleConstant n C := by
  rintro ⟨C, hC, h⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have := admissible_ge_four_of_odd (odd_two_mul_add_one N) C (hN _ (by omega))
  linarith [pi_mul_e_div_four_lt_four]

/-- Dimension-dependent reading: if `C n ≥ 0` is admissible in dimension `n` for all large `n`
and `C n → L`, then `L ≥ 4`; in particular `L ≤ (π/4) e` is impossible. -/
theorem conjecture_7792_false_limit :
    ¬ ∃ (Cs : ℕ → ℝ) (L : ℝ), (∀ n, 0 ≤ Cs n) ∧ (∀ᶠ n in atTop, AdmissibleConstant n (Cs n)) ∧
      Tendsto Cs atTop (𝓝 L) ∧ L ≤ Real.pi / 4 * Real.exp 1 := by
  rintro ⟨Cs, L, h0, h, hlim, hL⟩
  have h4 : ∀ᶠ n in atTop, 4 ≤ Cs n := by
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
    have := admissible_abs_ge_four hn1 (Cs n) hn
    rwa [abs_of_nonneg (h0 n)] at this
  have := ge_of_tendsto hlim h4
  linarith [pi_mul_e_div_four_lt_four]

end Conjecture7792
