import Mathlib

/-!
# Conjecture 00000002348 (disproved)

"The expected condition number of the norm matrix of random interpolation on smooth varieties
is `m^{-1/2}` (`m` the sample count)."

Every condition number is `>= 1`, so its expectation under any probability law is `>= 1`,
while `m^{-1/2} < 1` for every `m >= 2` and `C * m^{-1/2} -> 0`.

We formalize two standard condition numbers, both valued in `[0, +infinity]` with the usual
convention `kappa = +infinity` for a singular (rank-deficient) matrix:

* `condNum A = ‖A‖ * ‖A⁻¹‖` for a square matrix, with `‖.‖` any submultiplicative norm
  (stated for an arbitrary nontrivial normed ring, then instantiated with the spectral norm
  `Matrix.instL2OpNormedRing`, i.e. the operator norm on `EuclideanSpace ℝ (Fin n)`);
* `svCond A = (max_{‖x‖=1} ‖A x‖) / (min_{‖x‖=1} ‖A x‖)` = `sigma_max / sigma_min` for a
  possibly rectangular real matrix acting on Euclidean spaces.

The random norm matrix is an arbitrary function `A : Ω → Matrix ...` on an arbitrary
probability space, with sizes allowed to depend on `m`; no measurability is needed because the
expectation is the lower Lebesgue integral `∫⁻`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace C2348

/-! ## Condition number in a normed ring (any submultiplicative norm) -/

/-- `kappa(A) = ‖A‖ * ‖A⁻¹‖` for invertible `A`, and `+infinity` for singular `A`. -/
noncomputable def condNum {R : Type*} [NormedRing R] (A : R) : ℝ≥0∞ := by
  classical
  exact if IsUnit A then ((‖A‖₊ * ‖Ring.inverse A‖₊ : ℝ≥0) : ℝ≥0∞) else ⊤

/-- `kappa(A) >= 1` for every element of a nontrivial normed ring. -/
theorem one_le_condNum {R : Type*} [NormedRing R] [Nontrivial R] (A : R) : 1 ≤ condNum A := by
  classical
  unfold condNum
  split_ifs with h
  · have h1 : (1 : ℝ) ≤ ‖A‖ * ‖Ring.inverse A‖ := by
      calc (1 : ℝ) ≤ ‖(1 : R)‖ := one_le_norm_one R
        _ = ‖A * Ring.inverse A‖ := by rw [Ring.mul_inverse_cancel A h]
        _ ≤ ‖A‖ * ‖Ring.inverse A‖ := norm_mul_le _ _
    have h2 : (1 : ℝ≥0) ≤ ‖A‖₊ * ‖Ring.inverse A‖₊ := by
      rw [← NNReal.coe_le_coe]; simpa using h1
    exact_mod_cast h2
  · exact le_top

/-! ## Singular-value condition number of a (possibly rectangular) real matrix -/

/-- Largest stretch `sigma_max(A) = sup_{‖x‖=1} ‖A x‖`. -/
noncomputable def stretchMax {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) : ℝ≥0∞ :=
  ⨆ x : {x : EuclideanSpace ℝ (Fin q) // ‖x‖ = 1}, (‖Matrix.toEuclideanLin A x.1‖₊ : ℝ≥0∞)

/-- Smallest stretch `sigma_min(A) = inf_{‖x‖=1} ‖A x‖` (zero iff `A` is rank deficient). -/
noncomputable def stretchMin {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) : ℝ≥0∞ :=
  ⨅ x : {x : EuclideanSpace ℝ (Fin q) // ‖x‖ = 1}, (‖Matrix.toEuclideanLin A x.1‖₊ : ℝ≥0∞)

/-- `kappa_2(A) = sigma_max / sigma_min`, and `+infinity` when `sigma_min = 0`. -/
noncomputable def svCond {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) : ℝ≥0∞ := by
  classical
  exact if stretchMin A = 0 then ⊤ else stretchMax A / stretchMin A

/-- `sigma_max / sigma_min >= 1` for every real `p × q` matrix with `q >= 1`. -/
theorem one_le_svCond {p q : ℕ} (hq : 1 ≤ q) (A : Matrix (Fin p) (Fin q) ℝ) :
    1 ≤ svCond A := by
  classical
  unfold svCond
  split_ifs with h0
  · exact le_top
  · let i : Fin q := ⟨0, hq⟩
    let x0 : {x : EuclideanSpace ℝ (Fin q) // ‖x‖ = 1} :=
      ⟨EuclideanSpace.single i 1, by simp⟩
    have hmin : stretchMin A ≤ (‖Matrix.toEuclideanLin A x0.1‖₊ : ℝ≥0∞) := iInf_le _ x0
    have hmax : (‖Matrix.toEuclideanLin A x0.1‖₊ : ℝ≥0∞) ≤ stretchMax A := le_iSup
      (fun x : {x : EuclideanSpace ℝ (Fin q) // ‖x‖ = 1} =>
        (‖Matrix.toEuclideanLin A x.1‖₊ : ℝ≥0∞)) x0
    have htop : stretchMin A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hmin
    calc (1 : ℝ≥0∞) = stretchMin A / stretchMin A := (ENNReal.div_self h0 htop).symm
      _ ≤ stretchMax A / stretchMin A := ENNReal.div_le_div_right (hmin.trans hmax) _

/-! ## Expectations and the claimed value `m^{-1/2}` -/

/-- Any `[0, +infinity]`-valued random variable that is `>= 1` pointwise has expectation `>= 1`
under a probability measure (no measurability needed for the lower integral). -/
theorem one_le_expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (κ : Ω → ℝ≥0∞) (hκ : ∀ ω, 1 ≤ κ ω) : 1 ≤ ∫⁻ ω, κ ω ∂P := by
  calc (1 : ℝ≥0∞) = ∫⁻ _ω, (1 : ℝ≥0∞) ∂P := by simp
    _ ≤ ∫⁻ ω, κ ω ∂P := lintegral_mono hκ

/-- `m^{-1/2} < 1` for every sample count `m >= 2`. -/
theorem rpow_neg_half_lt_one {m : ℕ} (hm : 2 ≤ m) : (m : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  · norm_num

/-- Exact reading, abstract form: an expectation `>= 1` is never `m^{-1/2}` for `m >= 2`. -/
theorem ne_rpow_neg_half {E : ℝ≥0∞} (hE : 1 ≤ E) {m : ℕ} (hm : 2 ≤ m) :
    E ≠ ENNReal.ofReal ((m : ℝ) ^ (-(1 / 2 : ℝ))) := by
  intro h
  have hlt : ENNReal.ofReal ((m : ℝ) ^ (-(1 / 2 : ℝ))) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (rpow_neg_half_lt_one hm)
  exact absurd (h ▸ hE) (not_le.2 hlt)

/-- Order reading, abstract form: a sequence with all terms `>= 1` is not eventually bounded
by `C * m^{-1/2}` for any real constant `C` (so it is not `O(m^{-1/2})`, not `Θ(m^{-1/2})`,
and not asymptotic to `c * m^{-1/2}`). -/
theorem not_le_C_rpow_neg_half (E : ℕ → ℝ≥0∞) (hE : ∀ m, 1 ≤ E m) :
    ¬ ∃ C : ℝ, ∃ M : ℕ, ∀ m ≥ M, E m ≤ ENNReal.ofReal (C * (m : ℝ) ^ (-(1 / 2 : ℝ))) := by
  rintro ⟨C, M, hM⟩
  set m : ℕ := max M (⌈C ^ 2⌉₊ + 1) with hmdef
  have hmM : M ≤ m := le_max_left _ _
  have hmC : C ^ 2 < (m : ℝ) := by
    have h1 : C ^ 2 ≤ (⌈C ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈C ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast le_max_right _ _
    push_cast at h2
    linarith
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (sq_nonneg C) hmC
  have hsq : (m : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt m)⁻¹ := by
    rw [Real.rpow_neg hm0.le, Real.sqrt_eq_rpow]
  have hs0 : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have hlt : C * (m : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
    rw [hsq, ← div_eq_mul_inv, div_lt_one hs0]
    rcases le_or_gt C 0 with hC | hC
    · linarith
    · exact (Real.lt_sqrt hC.le).2 hmC
  have hE1 := (hE m).trans (hM m hmM)
  have : ENNReal.ofReal (C * (m : ℝ) ^ (-(1 / 2 : ℝ))) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hlt
  exact absurd hE1 (not_le.2 this)

/-! ## The conjecture, for random norm matrices -/

section Matrices

open scoped Matrix.Norms.L2Operator

/-- Unfolding: for an invertible real matrix (`det A ≠ 0`), `condNum A` is the product of the
operator norms on `EuclideanSpace ℝ (Fin n)` of `A` and of the matrix inverse `A⁻¹`
(i.e. `sigma_max(A) / sigma_min(A)`); for a singular matrix it is `+infinity`. -/
theorem condNum_matrix_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.det ≠ 0 → condNum A = ((‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖₊ *
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹‖₊ : ℝ≥0) : ℝ≥0∞)) ∧
    (A.det = 0 → condNum A = ⊤) := by
  classical
  constructor
  · intro h
    have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h)
    simp only [condNum, if_pos hu, ← Matrix.nonsing_inv_eq_ringInverse]
    rfl
  · intro h
    have hu : ¬ IsUnit A := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]; exact fun h' => h' h
    simp only [condNum, if_neg hu]

/-- Spectral-norm condition number `‖A‖₂ ‖A⁻¹‖₂ >= 1` for every real `n × n` matrix, `n >= 1`. -/
theorem one_le_condNum_matrix {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) :
    1 ≤ condNum A := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact one_le_condNum A

/-- **Exact reading refuted (square, spectral norm).** For every sample count `m >= 2`, every
matrix size `n >= 1`, every probability space and every random `n × n` norm matrix `A`,
`E[‖A‖₂ ‖A⁻¹‖₂] >= 1 > m^{-1/2}`; in particular it is not `m^{-1/2}`. -/
theorem conjecture_2348_false_exact {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 1 ≤ n) (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    {m : ℕ} (hm : 2 ≤ m) :
    1 ≤ ∫⁻ ω, condNum (A ω) ∂P ∧
      ∫⁻ ω, condNum (A ω) ∂P ≠ ENNReal.ofReal ((m : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have h := one_le_expectation P _ (fun ω => one_le_condNum_matrix hn (A ω))
  exact ⟨h, ne_rpow_neg_half h hm⟩

/-- **Exact reading refuted (rectangular, `sigma_max / sigma_min`).** -/
theorem conjecture_2348_false_exact_sv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p q : ℕ} (hq : 1 ≤ q) (A : Ω → Matrix (Fin p) (Fin q) ℝ)
    {m : ℕ} (hm : 2 ≤ m) :
    1 ≤ ∫⁻ ω, svCond (A ω) ∂P ∧
      ∫⁻ ω, svCond (A ω) ∂P ≠ ENNReal.ofReal ((m : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have h := one_le_expectation P _ (fun ω => one_le_svCond hq (A ω))
  exact ⟨h, ne_rpow_neg_half h hm⟩

/-- **Order reading refuted (square, spectral norm).** For any family indexed by the sample
count `m` (matrix size `N m >= 1` and probability space `Ω m` both allowed to depend on `m`),
the expected condition numbers are not eventually `<= C * m^{-1/2}` for any constant `C`. -/
theorem conjecture_2348_false_order (N : ℕ → ℕ) (hN : ∀ m, 1 ≤ N m) (Ω : ℕ → Type*)
    [∀ m, MeasurableSpace (Ω m)] (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    (A : ∀ m, Ω m → Matrix (Fin (N m)) (Fin (N m)) ℝ) :
    ¬ ∃ C : ℝ, ∃ M : ℕ, ∀ m ≥ M,
      ∫⁻ ω, condNum (A m ω) ∂(P m) ≤ ENNReal.ofReal (C * (m : ℝ) ^ (-(1 / 2 : ℝ))) :=
  not_le_C_rpow_neg_half _ fun m =>
    one_le_expectation (P m) _ fun ω => one_le_condNum_matrix (hN m) (A m ω)

/-- **Order reading refuted (rectangular, `sigma_max / sigma_min`).** -/
theorem conjecture_2348_false_order_sv (p q : ℕ → ℕ) (hq : ∀ m, 1 ≤ q m) (Ω : ℕ → Type*)
    [∀ m, MeasurableSpace (Ω m)] (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    (A : ∀ m, Ω m → Matrix (Fin (p m)) (Fin (q m)) ℝ) :
    ¬ ∃ C : ℝ, ∃ M : ℕ, ∀ m ≥ M,
      ∫⁻ ω, svCond (A m ω) ∂(P m) ≤ ENNReal.ofReal (C * (m : ℝ) ^ (-(1 / 2 : ℝ))) :=
  not_le_C_rpow_neg_half _ fun m =>
    one_le_expectation (P m) _ fun ω => one_le_svCond (hq m) (A m ω)

end Matrices

/-- Real-valued (Bochner) expectation, for random matrices that are almost surely invertible
with integrable condition number: `E[‖A‖ ‖A⁻¹‖] >= 1`, in any nontrivial normed ring. -/
theorem one_le_integral_condNum {Ω R : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] [NormedRing R] [Nontrivial R] (A : Ω → R)
    (hA : ∀ᵐ ω ∂P, IsUnit (A ω))
    (hint : Integrable (fun ω => ‖A ω‖ * ‖Ring.inverse (A ω)‖) P) :
    1 ≤ ∫ ω, ‖A ω‖ * ‖Ring.inverse (A ω)‖ ∂P := by
  have hpt : ∀ᵐ ω ∂P, (1 : ℝ) ≤ ‖A ω‖ * ‖Ring.inverse (A ω)‖ := by
    filter_upwards [hA] with ω h
    calc (1 : ℝ) ≤ ‖(1 : R)‖ := one_le_norm_one R
      _ = ‖A ω * Ring.inverse (A ω)‖ := by rw [Ring.mul_inverse_cancel _ h]
      _ ≤ ‖A ω‖ * ‖Ring.inverse (A ω)‖ := norm_mul_le _ _
  calc (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂P := by simp
    _ ≤ ∫ ω, ‖A ω‖ * ‖Ring.inverse (A ω)‖ ∂P :=
      integral_mono_ae (integrable_const 1) hint hpt

end C2348
