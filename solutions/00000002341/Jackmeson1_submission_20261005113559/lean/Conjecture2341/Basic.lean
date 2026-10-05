import Mathlib

/-!
# Conjecture 00000002341 (pseudospectral area identity) is false

Conjecture (verbatim): "Definition: The pseudospectrum is {z : ‖(A−zI)^{-1}‖ > ε^{-1}}.
Conjecture: The pseudospectral area of a random matrix is πε²·(1 + ‖A*A − AA*‖_{HS}/2)
(an explicit identity in the Hilbert–Schmidt deviation from normality); the area growth is
exactly ε²."

Conventions.
* `‖·‖` on matrices is the operator 2-norm (Mathlib's scoped `Matrix.Norms.L2Operator`).
* For `z` an eigenvalue, `A - zI` has no inverse and `‖(A - zI)⁻¹‖ = ∞` by convention, so the
  pseudospectrum contains the spectrum (`pseudospectrum` below).
* Area is Lebesgue measure (`volume`) on `ℂ ≅ ℝ²`.
* `‖M‖_HS = sqrt (∑ i j, |M i j|²)` (`hsNorm`).

Results.
* `no_exact_eps_sq_law` (any complex Banach algebra with `‖1‖ = 1`): if `a` has two distinct
  spectral values, there is no constant `K` with `area (Λ_ε a) = K ε²` for all `ε > 0`.
* `areaIdentity_iff_scalar`: for an `n × n` complex matrix (`n ≥ 1`, operator 2-norm), the
  identity holds for all `ε > 0` if and only if `A = c • 1` is a scalar matrix.
* `conjecture_2341_false`: not every `2 × 2` complex matrix satisfies the identity
  (witness `diag(1, -1)`); `diag_counterexample` treats this matrix directly.
-/

open MeasureTheory Metric Real
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace C2341

set_option linter.unusedSectionVars false

section Banach

variable {𝒜 : Type*} [NormedRing 𝒜] [NormedAlgebra ℂ 𝒜] [CompleteSpace 𝒜] [NormOneClass 𝒜]

/-- Pseudospectrum of `a` in a unital Banach algebra: the spectrum together with the points
where the resolvent norm exceeds `ε⁻¹`. -/
def pseudo (a : 𝒜) (ε : ℝ) : Set ℂ :=
  {z | z ∈ spectrum ℂ a ∨ ε⁻¹ < ‖Ring.inverse (a - algebraMap ℂ 𝒜 z)‖}

lemma isUnit_sub_of_notMem {a : 𝒜} {z : ℂ} (h : z ∉ spectrum ℂ a) :
    IsUnit (a - algebraMap ℂ 𝒜 z) := by
  have := (spectrum.notMem_iff.mp h).neg
  rwa [neg_sub] at this

/-- The `ε`-ball around a spectral value lies in the pseudospectrum. -/
lemma ball_subset_pseudo {a : 𝒜} {lam : ℂ} (hl : lam ∈ spectrum ℂ a) {ε : ℝ} (hε : 0 < ε) :
    ball lam ε ⊆ pseudo a ε := by
  intro z hz
  by_cases hzs : z ∈ spectrum ℂ a
  · exact Or.inl hzs
  right
  have hne : lam - z ≠ 0 := sub_ne_zero.mpr (fun h => hzs (h ▸ hl))
  obtain ⟨u, hu⟩ := isUnit_sub_of_notMem hzs
  have h1 : ((Units.mk0 _ hne : ℂˣ) : ℂ) ∈ spectrum ℂ (u : 𝒜) := by
    rw [hu, ← spectrum.sub_singleton_eq]
    exact Set.sub_mem_sub hl rfl
  have h2 := spectrum.norm_le_norm_of_mem ((spectrum.inv_mem_iff).mp h1)
  rw [← hu, Ring.inverse_unit]
  have hd : ‖lam - z‖ < ε := by rwa [mem_ball, dist_comm, dist_eq_norm] at hz
  have hpos : 0 < ‖lam - z‖ := norm_pos_iff.mpr hne
  calc ε⁻¹ < ‖lam - z‖⁻¹ := (inv_lt_inv₀ hε hpos).mpr hd
    _ = ‖(((Units.mk0 _ hne)⁻¹ : ℂˣ) : ℂ)‖ := by simp
    _ ≤ _ := h2

/-- Resolvent bound `‖(a - z)⁻¹‖ (|z| - ‖a‖) ≤ 1` for `|z| > ‖a‖`. -/
lemma norm_inverse_mul_le {a : 𝒜} {z : ℂ} (hz : ‖a‖ < ‖z‖) :
    ‖Ring.inverse (a - algebraMap ℂ 𝒜 z)‖ * (‖z‖ - ‖a‖) ≤ 1 := by
  set R := Ring.inverse (a - algebraMap ℂ 𝒜 z)
  have hzs : z ∉ spectrum ℂ a := fun h => (spectrum.norm_le_norm_of_mem h).not_gt hz
  have hR : R * (a - algebraMap ℂ 𝒜 z) = 1 := Ring.inverse_mul_cancel _ (isUnit_sub_of_notMem hzs)
  rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at hR
  have hzR : z • R = R * a - 1 := by rw [← hR]; abel
  have h1 : ‖z‖ * ‖R‖ ≤ ‖R‖ * ‖a‖ + 1 := by
    rw [← norm_smul, hzR]
    calc ‖R * a - 1‖ ≤ ‖R * a‖ + ‖(1 : 𝒜)‖ := norm_sub_le _ _
      _ ≤ ‖R‖ * ‖a‖ + 1 := by rw [norm_one]; gcongr; exact norm_mul_le _ _
  nlinarith

/-- The pseudospectrum lies in the disc of radius `‖a‖ + ε`. -/
lemma pseudo_subset_ball (a : 𝒜) {ε : ℝ} (hε : 0 < ε) : pseudo a ε ⊆ ball 0 (‖a‖ + ε) := by
  intro z hz
  rw [mem_ball, dist_zero_right]
  by_contra h
  rw [not_lt] at h
  have hz' : ‖a‖ < ‖z‖ := by linarith
  rcases hz with hs | hn
  · exact (spectrum.norm_le_norm_of_mem hs).not_gt hz'
  · have key := norm_inverse_mul_le hz'
    have h1 : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
    have h2 := mul_lt_mul_of_pos_right hn hε
    nlinarith [norm_nonneg (Ring.inverse (a - algebraMap ℂ 𝒜 z))]

lemma vol_ball (c : ℂ) {r : ℝ} (hr : 0 ≤ r) : volume (ball c r) = ENNReal.ofReal (π * r ^ 2) := by
  rw [Complex.volume_ball, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), mul_comm]

lemma vol_pseudo_le (a : 𝒜) {ε : ℝ} (hε : 0 < ε) :
    volume (pseudo a ε) ≤ ENNReal.ofReal (π * (‖a‖ + ε) ^ 2) := by
  rw [← vol_ball 0 (by positivity)]
  exact measure_mono (pseudo_subset_ball a hε)

lemma vol_pseudo_ge_two {a : 𝒜} {lam mu : ℂ} (hl : lam ∈ spectrum ℂ a) (hm : mu ∈ spectrum ℂ a)
    {ε : ℝ} (hε : 0 < ε) (h : 2 * ε ≤ ‖lam - mu‖) :
    ENNReal.ofReal (2 * (π * ε ^ 2)) ≤ volume (pseudo a ε) := by
  have hd : Disjoint (ball lam ε) (ball mu ε) :=
    ball_disjoint_ball (by rw [dist_eq_norm]; linarith)
  calc ENNReal.ofReal (2 * (π * ε ^ 2)) = volume (ball lam ε ∪ ball mu ε) := by
        rw [measure_union hd measurableSet_ball, vol_ball _ hε.le, vol_ball _ hε.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity), two_mul]
    _ ≤ _ := measure_mono (Set.union_subset (ball_subset_pseudo hl hε) (ball_subset_pseudo hm hε))

/-- **No exact `ε²` law.** If `a` has two distinct spectral values, then the area of its
`ε`-pseudospectrum is not of the form `K ε²` (for any real constant `K`, all `ε > 0`). -/
theorem no_exact_eps_sq_law {a : 𝒜} {lam mu : ℂ} (hl : lam ∈ spectrum ℂ a)
    (hm : mu ∈ spectrum ℂ a) (hne : lam ≠ mu) :
    ¬ ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → volume (pseudo a ε) = ENNReal.ofReal (K * ε ^ 2) := by
  rintro ⟨K, hK⟩
  have hd : 0 < ‖lam - mu‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set e0 := ‖lam - mu‖ / 2 with he0
  have he0p : 0 < e0 := by positivity
  have h1 := vol_pseudo_ge_two hl hm he0p (by rw [he0]; linarith)
  rw [hK e0 he0p] at h1
  have hp : 0 < 2 * (π * e0 ^ 2) := by positivity
  have h1' : 2 * (π * e0 ^ 2) ≤ K * e0 ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff'.mp h1).resolve_right (not_le.mpr hp)
  have hK2 : 2 * π ≤ K := by nlinarith [pow_pos he0p 2]
  set R := ‖a‖
  have hR : 0 ≤ R := norm_nonneg a
  have he1 : (0 : ℝ) < 3 * R + 1 := by positivity
  have h2 := vol_pseudo_le a he1
  rw [hK _ he1, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right hK2 (sq_nonneg (3 * R + 1))]

end Banach

section Matrices

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The `ε`-pseudospectrum of a square complex matrix as defined in the conjecture,
`{z | ‖(A - z I)⁻¹‖ > ε⁻¹}`, operator 2-norm, with the standard convention
`‖(A - z I)⁻¹‖ = ∞` when `A - z I` is not invertible. -/
def pseudospectrum (A : Matrix m m ℂ) (ε : ℝ) : Set ℂ :=
  {z | ¬ IsUnit (A - z • (1 : Matrix m m ℂ)) ∨ ε⁻¹ < ‖(A - z • (1 : Matrix m m ℂ))⁻¹‖}

/-- Hilbert–Schmidt (Frobenius) norm. -/
def hsNorm (M : Matrix m m ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2)

/-- The conjectured identity for a fixed matrix `A`, for every `ε > 0`. -/
def AreaIdentity (A : Matrix m m ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → volume (pseudospectrum A ε) =
    ENNReal.ofReal (π * ε ^ 2 * (1 + hsNorm (Aᴴ * A - A * Aᴴ) / 2))

lemma pseudospectrum_eq (A : Matrix m m ℂ) (ε : ℝ) : pseudospectrum A ε = pseudo A ε := by
  ext z
  simp only [pseudospectrum, pseudo, Set.mem_ofPred_eq, spectrum.mem_iff,
    Algebra.algebraMap_eq_smul_one, Matrix.nonsing_inv_eq_ringInverse]
  rw [← IsUnit.neg_iff, neg_sub]

lemma eq_zero_of_hsNorm_eq_zero {M : Matrix m m ℂ} (h : hsNorm M = 0) : M = 0 := by
  have hs : ∑ i, ∑ j, ‖M i j‖ ^ 2 = 0 := by
    rw [hsNorm, Real.sqrt_eq_zero (by positivity)] at h; exact h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp hs i
    (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h1 j
    (Finset.mem_univ _)
  simpa using h2

/-- The pseudospectrum of a scalar matrix `c • 1` is the open disc of radius `ε` about `c`. -/
lemma pseudo_scalar [Nonempty m] (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    pseudo (algebraMap ℂ (Matrix m m ℂ) c) ε = ball c ε := by
  apply Set.Subset.antisymm
  · intro z hz
    by_contra hb
    rw [mem_ball, dist_eq_norm, not_lt] at hb
    have hzc : z ≠ c := by rintro rfl; simp at hb; linarith
    rcases hz with hs | hn
    · rw [spectrum.scalar_eq, Set.mem_singleton_iff] at hs; exact hzc hs
    · set R := Ring.inverse (algebraMap ℂ (Matrix m m ℂ) c - algebraMap ℂ (Matrix m m ℂ) z)
      have hu : IsUnit (algebraMap ℂ (Matrix m m ℂ) c - algebraMap ℂ (Matrix m m ℂ) z) :=
        isUnit_sub_of_notMem (by rw [spectrum.scalar_eq]; exact hzc)
      have hR : R * algebraMap ℂ (Matrix m m ℂ) (c - z) = 1 := by
        rw [map_sub]; exact Ring.inverse_mul_cancel _ hu
      rw [Algebra.algebraMap_eq_smul_one (c - z), mul_smul_comm, mul_one] at hR
      have hn1 : ‖c - z‖ * ‖R‖ = 1 := by rw [← norm_smul, hR, norm_one]
      have h1 : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
      have hcz : ε ≤ ‖c - z‖ := by rw [norm_sub_rev]; exact hb
      nlinarith [norm_nonneg R, mul_lt_mul_of_pos_right hn hε]
  · exact ball_subset_pseudo (by rw [spectrum.scalar_eq]; rfl) hε

/-- **Characterization.** For an `n × n` complex matrix with `n ≥ 1` (operator 2-norm), the
conjectured identity holds for every `ε > 0` if and only if `A` is a scalar matrix. -/
theorem areaIdentity_iff_scalar [Nonempty m] (A : Matrix m m ℂ) :
    AreaIdentity A ↔ ∃ c : ℂ, A = c • (1 : Matrix m m ℂ) := by
  constructor
  · intro hI
    simp only [AreaIdentity, pseudospectrum_eq] at hI
    set c := hsNorm (Aᴴ * A - A * Aᴴ) with hcdef
    have hc0 : 0 ≤ c := Real.sqrt_nonneg _
    -- Step 1: the Hilbert–Schmidt term vanishes (compare with the disc of radius `‖A‖ + ε`).
    have hc : c = 0 := by
      by_contra hne
      have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hne)
      set R := ‖A‖
      have hR : 0 ≤ R := norm_nonneg A
      set ε := 2 * (2 * R + R ^ 2) / c + 1 with hεdef
      have hε1 : 1 ≤ ε := by
        have : 0 ≤ 2 * (2 * R + R ^ 2) / c := by positivity
        rw [hεdef]; linarith
      have hε : 0 < ε := by linarith
      have hce : c * ε = 2 * (2 * R + R ^ 2) + c := by
        rw [hεdef]; field_simp
      have h := vol_pseudo_le A hε
      rw [hI ε hε, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
      have h' : ε ^ 2 * (1 + c / 2) ≤ (R + ε) ^ 2 := by
        have := Real.pi_pos
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hε1 (sq_nonneg R)]
    have hcomm : Aᴴ * A = A * Aᴴ := sub_eq_zero.mp (eq_zero_of_hsNorm_eq_zero hc)
    -- Step 2: the spectrum is a single point.
    obtain ⟨lam, hl⟩ := spectrum.nonempty A
    have hsing : ∀ mu ∈ spectrum ℂ A, mu = lam := by
      intro mu hm
      by_contra hne
      have hd : 0 < ‖lam - mu‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
      have he : 0 < ‖lam - mu‖ / 2 := by positivity
      have h1 := vol_pseudo_ge_two hl hm he (by linarith)
      rw [hI _ he, hc, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
      nlinarith [Real.pi_pos, pow_pos he 2]
    -- Step 3: a normal matrix with one-point spectrum is scalar.
    set N := A - algebraMap ℂ (Matrix m m ℂ) lam with hN
    have hnorm : IsStarNormal N := by
      refine ⟨?_⟩
      rw [hN, star_sub, ← algebraMap_star_comm]
      have hA : Commute (star A) A := hcomm
      exact (hA.sub_right (Algebra.commute_algebraMap_right _ _)).sub_left
        ((Algebra.commute_algebraMap_left _ _).sub_right (Algebra.commutes _ _))
    have hsr : spectralRadius ℂ N = 0 := by
      apply le_antisymm _ bot_le
      refine iSup₂_le fun k hk => ?_
      rw [hN, ← spectrum.sub_singleton_eq] at hk
      obtain ⟨mu, hm, r, hr, rfl⟩ := hk
      rw [Set.mem_singleton_iff] at hr
      rw [hsing mu hm, hr]; simp
    rw [IsStarNormal.spectralRadius_eq_nnnorm, ENNReal.coe_eq_zero, nnnorm_eq_zero, hN,
      sub_eq_zero] at hsr
    exact ⟨lam, by rw [hsr, Algebra.algebraMap_eq_smul_one]⟩
  · rintro ⟨c, rfl⟩ ε hε
    have hzero : (c • (1 : Matrix m m ℂ))ᴴ * (c • 1) - (c • 1) * (c • 1)ᴴ = 0 := by
      simp [Matrix.conjTranspose_smul]
      rw [smul_smul, smul_smul, mul_comm, sub_self]
    rw [hzero, pseudospectrum_eq, ← Algebra.algebraMap_eq_smul_one, pseudo_scalar c hε,
      vol_ball _ hε.le]
    simp [hsNorm]

/-- The conjecture fails: the identity does not hold for all `2 × 2` complex matrices. -/
theorem conjecture_2341_false :
    ¬ ∀ A : Matrix (Fin 2) (Fin 2) ℂ, AreaIdentity A := by
  intro h
  obtain ⟨c, hc⟩ := (areaIdentity_iff_scalar _).mp (h (Matrix.diagonal ![1, -1]))
  have h0 := congrFun (congrFun hc 0) 0
  have h1 := congrFun (congrFun hc 1) 1
  simp at h0 h1
  rw [← h0] at h1
  norm_num at h1

/-- For `A = diag(1, -1)`: the area of the pseudospectrum is not `K ε²` for any constant `K`
(so "the area growth is exactly ε²" fails in the reading `area = K ε²` for all `ε > 0`), and the
conjectured identity fails. -/
theorem diag_counterexample :
    (¬ ∃ K : ℝ, ∀ ε : ℝ, 0 < ε →
        volume (pseudospectrum (Matrix.diagonal ![(1 : ℂ), -1]) ε) = ENNReal.ofReal (K * ε ^ 2)) ∧
      ¬ AreaIdentity (Matrix.diagonal ![(1 : ℂ), -1]) := by
  have h1 : (1 : ℂ) ∈ spectrum ℂ (Matrix.diagonal ![(1 : ℂ), -1]) := by
    rw [spectrum_diagonal]; exact ⟨0, rfl⟩
  have h2 : (-1 : ℂ) ∈ spectrum ℂ (Matrix.diagonal ![(1 : ℂ), -1]) := by
    rw [spectrum_diagonal]; exact ⟨1, rfl⟩
  have key := no_exact_eps_sq_law h1 h2 (by norm_num)
  simp only [← pseudospectrum_eq] at key
  refine ⟨key, fun hI => key ⟨π * (1 + hsNorm ((Matrix.diagonal ![(1 : ℂ), -1])ᴴ *
    Matrix.diagonal ![(1 : ℂ), -1] - Matrix.diagonal ![(1 : ℂ), -1] *
    (Matrix.diagonal ![(1 : ℂ), -1])ᴴ) / 2), fun ε hε => by rw [hI ε hε]; ring_nf⟩⟩

end Matrices

end C2341
