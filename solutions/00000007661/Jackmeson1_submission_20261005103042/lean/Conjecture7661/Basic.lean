import Mathlib

/-!
# Conjecture 00000007661 is false

Fix `q : ℂ` with `0 < ‖q‖ < 1`.  A power series `F(z) = ∑ aₙ zⁿ` is *of q-hypergeometric type*
if there are rational functions `R(z), S(z)` with `F(qz) = R(z) F(z) + S(z)`; the coefficient
ratios `aₙ₊₁ / aₙ` are the *Q-geometric ratios*.

Conjecture: `F ∈ ℤ[[z]]` is of q-hypergeometric type with radius of convergence `1` if and only if
its Q-geometric ratios converge to `1` at rate `O(qⁿ)`, and this rate cannot be improved to
`o(qⁿ)` unless `F` is a polynomial.

For every such `q`:
* `F2 = 1/(1-z)² = ∑ (n+1) zⁿ` is of q-hypergeometric type (`R = (1-z)²/(1-qz)²`, `S = 0`) with
  radius `1`, but `aₙ₊₁/aₙ - 1 = 1/(n+1)` is not `O(qⁿ)`: the "only if" direction fails.
* `F1 = 1/(1-z) = ∑ zⁿ` is of q-hypergeometric type with radius `1`, its ratios are exactly `1`,
  so `aₙ₊₁/aₙ - 1 = 0 = o(qⁿ)`, yet `F1` is not a polynomial: the "unless" clause fails.

Conventions: the series `F` is evaluated as `∑' n, aₙ zⁿ` on the open unit disk; a rational
function is a quotient `A/B` of complex polynomials with `B ≠ 0`, and the functional equation is
required at every point of the open unit disk where the denominators do not vanish.  In both
examples every coefficient is nonzero, so no division by zero occurs in the ratios.
-/

open Filter Topology Asymptotics PowerSeries

namespace C7661

/-- The sum function `z ↦ ∑ aₙ zⁿ` of an integer power series. -/
noncomputable def toFun (F : PowerSeries ℤ) (z : ℂ) : ℂ := ∑' n, ((coeff n F : ℤ) : ℂ) * z ^ n

/-- The radius of convergence of `F` (as a complex power series). -/
noncomputable def radius (F : PowerSeries ℤ) : ENNReal :=
  (FormalMultilinearSeries.ofScalars ℂ (fun n => ((coeff n F : ℤ) : ℂ))).radius

/-- `F` is of q-hypergeometric type: there are rational functions `R = A/B`, `S = C/D` with
`F(qz) = R(z) F(z) + S(z)` on the open unit disk (wherever `B(z), D(z) ≠ 0`). -/
def QHypergeometricType (q : ℂ) (F : PowerSeries ℤ) : Prop :=
  ∃ A B C D : Polynomial ℂ, B ≠ 0 ∧ D ≠ 0 ∧
    ∀ z : ℂ, ‖z‖ < 1 → B.eval z ≠ 0 → D.eval z ≠ 0 →
      toFun F (q * z) = A.eval z / B.eval z * toFun F z + C.eval z / D.eval z

/-- The Q-geometric ratio sequence `aₙ₊₁ / aₙ`. -/
noncomputable def ratio (F : PowerSeries ℤ) (n : ℕ) : ℝ :=
  ((coeff (n + 1) F : ℤ) : ℝ) / ((coeff n F : ℤ) : ℝ)

/-- The ratios converge to `1` at rate `O(qⁿ)`. -/
def RateBigO (q : ℂ) (F : PowerSeries ℤ) : Prop :=
  Tendsto (ratio F) atTop (𝓝 1) ∧ (fun n => ratio F n - 1) =O[atTop] (fun n => q ^ n)

/-- The ratios converge to `1` at rate `o(qⁿ)`. -/
def RateLittleO (q : ℂ) (F : PowerSeries ℤ) : Prop :=
  (fun n => ratio F n - 1) =o[atTop] (fun n => q ^ n)

/-- `F` is a polynomial. -/
def IsPoly (F : PowerSeries ℤ) : Prop := ∃ p : Polynomial ℤ, (p : PowerSeries ℤ) = F

/-- `F1 = ∑ zⁿ = 1/(1-z)`. -/
noncomputable def F1 : PowerSeries ℤ := PowerSeries.mk fun _ => 1

/-- `F2 = ∑ (n+1) zⁿ = 1/(1-z)²`. -/
noncomputable def F2 : PowerSeries ℤ := PowerSeries.mk fun n => (n : ℤ) + 1

lemma toFun_F1 {z : ℂ} (hz : ‖z‖ < 1) : toFun F1 z = (1 - z)⁻¹ := by
  simpa [toFun, F1] using tsum_geometric_of_norm_lt_one hz

lemma toFun_F2 {z : ℂ} (hz : ‖z‖ < 1) : toFun F2 z = ((1 - z) ^ 2)⁻¹ := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hz).add (hasSum_geometric_of_norm_lt_one hz)
  have hz1 : (1 : ℂ) - z ≠ 0 := by
    intro h0; have : z = 1 := by linear_combination -h0
    rw [this, norm_one] at hz; exact lt_irrefl _ hz
  have : toFun F2 z = z / (1 - z) ^ 2 + (1 - z)⁻¹ := by
    rw [toFun, ← h.tsum_eq]; congr 1; funext n; simp [F2]; ring
  rw [this]; field_simp; ring

lemma norm_mul_lt {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) : ‖q * z‖ < 1 := by
  rw [norm_mul]
  calc ‖q‖ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
    _ < 1 := by simpa using hz

lemma one_sub_ne {z : ℂ} (hz : ‖z‖ < 1) : (1 : ℂ) - z ≠ 0 := by
  intro h0; have : z = 1 := by linear_combination -h0
  rw [this, norm_one] at hz; exact lt_irrefl _ hz

theorem qHyp_F1 {q : ℂ} (hq : ‖q‖ < 1) : QHypergeometricType q F1 := by
  refine ⟨1 - Polynomial.X, 1 - Polynomial.C q * Polynomial.X, 0, 1, ?_, one_ne_zero, ?_⟩
  · intro h; have := congrArg (Polynomial.eval 0) h; simp at this
  · intro z hz hB _
    rw [toFun_F1 hz, toFun_F1 (norm_mul_lt hq hz)]
    have h1 := one_sub_ne hz
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_zero] at hB ⊢
    field_simp
    ring

theorem qHyp_F2 {q : ℂ} (hq : ‖q‖ < 1) : QHypergeometricType q F2 := by
  refine ⟨(1 - Polynomial.X) ^ 2, (1 - Polynomial.C q * Polynomial.X) ^ 2, 0, 1, ?_, one_ne_zero,
    ?_⟩
  · intro h; have := congrArg (Polynomial.eval 0) h; simp at this
  · intro z hz hB _
    rw [toFun_F2 hz, toFun_F2 (norm_mul_lt hq hz)]
    have h1 := one_sub_ne hz
    have h2 := one_sub_ne (norm_mul_lt hq hz)
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_zero, Polynomial.eval_pow] at hB ⊢
    field_simp
    ring

theorem radius_F1 : radius F1 = 1 := by
  have h : Tendsto (fun n => ‖((coeff (n + 1) F1 : ℤ) : ℂ)‖ / ‖((coeff n F1 : ℤ) : ℂ)‖) atTop
      (𝓝 ((1 : NNReal) : ℝ)) := by
    simp [F1]
  have := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto ℂ
    (fun n => ((coeff n F1 : ℤ) : ℂ)) one_ne_zero h
  simpa [radius] using this

theorem radius_F2 : radius F2 = 1 := by
  have h : Tendsto (fun n => ‖((coeff (n + 1) F2 : ℤ) : ℂ)‖ / ‖((coeff n F2 : ℤ) : ℂ)‖) atTop
      (𝓝 ((1 : NNReal) : ℝ)) := by
    have e : (fun n : ℕ => ‖((coeff (n + 1) F2 : ℤ) : ℂ)‖ / ‖((coeff n F2 : ℤ) : ℂ)‖) =
        fun n : ℕ => 1 + 1 / ((n : ℝ) + 1) := by
      funext n
      have h1 : ((coeff (n + 1) F2 : ℤ) : ℂ) = (((n + 2 : ℕ) : ℝ) : ℂ) := by
        simp [F2]; ring
      have h0 : ((coeff n F2 : ℤ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) := by
        simp [F2]
      rw [h1, h0, Complex.norm_real, Complex.norm_real, Real.norm_natCast, Real.norm_natCast]
      push_cast; field_simp; ring
    rw [e]
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
  have := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto ℂ
    (fun n => ((coeff n F2 : ℤ) : ℂ)) one_ne_zero h
  simpa [radius] using this

lemma ratio_F1 (n : ℕ) : ratio F1 n = 1 := by simp [ratio, F1]

lemma ratio_F2 (n : ℕ) : ratio F2 n - 1 = 1 / ((n : ℝ) + 1) := by
  simp only [ratio, F2, coeff_mk]; push_cast
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp; ring

theorem not_rateBigO_F2 {q : ℂ} (hq : ‖q‖ < 1) : ¬ RateBigO q F2 := by
  rintro ⟨-, h⟩
  obtain ⟨c, hc⟩ := h.bound
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg q
  have ht : Tendsto (fun n : ℕ => c * ((n : ℝ) * ‖q‖ ^ n + ‖q‖ ^ n)) atTop (𝓝 0) := by
    simpa using ((tendsto_self_mul_const_pow_of_lt_one hr0 hq).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hq)).const_mul c
  obtain ⟨n, hn1, hn2⟩ := (hc.and (ht.eventually (gt_mem_nhds one_pos))).exists
  rw [ratio_F2, norm_pow] at hn1
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ hpos] at hn1
  nlinarith

theorem rateLittleO_F1 (q : ℂ) : RateLittleO q F1 := by
  have : (fun n => ratio F1 n - 1) = fun _ => (0 : ℝ) := by funext n; simp [ratio_F1]
  rw [RateLittleO, this]
  exact isLittleO_zero _ _

theorem rateBigO_F1 (q : ℂ) : RateBigO q F1 := by
  refine ⟨?_, (rateLittleO_F1 q).isBigO⟩
  rw [show ratio F1 = fun _ => 1 from funext ratio_F1]; exact tendsto_const_nhds

theorem not_isPoly_F1 : ¬ IsPoly F1 := by
  rintro ⟨p, hp⟩
  have := congrArg (coeff (p.natDegree + 1)) hp
  rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)] at this
  simp [F1] at this

/-- **Conjecture 00000007661 is false**, for every `q` with `0 < ‖q‖ < 1`.
(1) The "only if" direction fails: `F2 = 1/(1-z)²` is of q-hypergeometric type with radius `1`,
but its Q-geometric ratios do not converge to `1` at rate `O(qⁿ)`.
(2) The "unless" clause fails: `F1 = 1/(1-z)` is of q-hypergeometric type with radius `1`, its
ratios converge to `1` at rate `o(qⁿ)`, and it is not a polynomial.
(3) Hence neither the equivalence alone, nor the "unless" clause alone (even restricted to
q-hypergeometric series of radius `1`), nor the equivalence whose right side is "`O(qⁿ)` and,
unless `F` is a polynomial, not `o(qⁿ)`" holds. -/
theorem conjecture_false (q : ℂ) (_hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (QHypergeometricType q F2 ∧ radius F2 = 1 ∧ ¬ RateBigO q F2) ∧
    (QHypergeometricType q F1 ∧ radius F1 = 1 ∧ RateBigO q F1 ∧ RateLittleO q F1 ∧
      ¬ IsPoly F1) ∧
    ¬ (∀ F : PowerSeries ℤ, (QHypergeometricType q F ∧ radius F = 1) ↔ RateBigO q F) ∧
    ¬ (∀ F : PowerSeries ℤ, QHypergeometricType q F → radius F = 1 → RateLittleO q F →
      IsPoly F) ∧
    ¬ (∀ F : PowerSeries ℤ, (QHypergeometricType q F ∧ radius F = 1) ↔
      (RateBigO q F ∧ (RateLittleO q F → IsPoly F))) := by
  refine ⟨⟨qHyp_F2 hq1, radius_F2, not_rateBigO_F2 hq1⟩,
    ⟨qHyp_F1 hq1, radius_F1, rateBigO_F1 q, rateLittleO_F1 q, not_isPoly_F1⟩, ?_, ?_, ?_⟩
  · intro h
    exact not_rateBigO_F2 hq1 ((h F2).mp ⟨qHyp_F2 hq1, radius_F2⟩)
  · intro h
    exact not_isPoly_F1 (h F1 (qHyp_F1 hq1) radius_F1 (rateLittleO_F1 q))
  · intro h
    exact not_isPoly_F1 (((h F1).mp ⟨qHyp_F1 hq1, radius_F1⟩).2 (rateLittleO_F1 q))

/-! ### The same refutation with the functional equation read formally in `ℂ[[z]]` -/

/-- `F` as a complex power series. -/
noncomputable def toC (F : PowerSeries ℤ) : PowerSeries ℂ := PowerSeries.map (Int.castRingHom ℂ) F

/-- Formal q-hypergeometric type: with `R = A/B`, `S = C/D` (`B, D ≠ 0`), the identity
`F(qz) = R(z) F(z) + S(z)` after clearing denominators, `B D F(qz) = A D F(z) + B C`, holds in
`ℂ[[z]]`; here `F(qz)` is `rescale q F`. -/
def QHypergeometricTypeFormal (q : ℂ) (F : PowerSeries ℤ) : Prop :=
  ∃ A B C D : Polynomial ℂ, B ≠ 0 ∧ D ≠ 0 ∧
    ((B * D : Polynomial ℂ) : PowerSeries ℂ) * rescale q (toC F) =
      ((A * D : Polynomial ℂ) : PowerSeries ℂ) * toC F + ((B * C : Polynomial ℂ) : PowerSeries ℂ)

lemma toC_F1 : toC F1 = PowerSeries.mk 1 := by ext n; simp [toC, F1]

lemma toC_F2 : toC F2 = PowerSeries.mk fun n => ((Nat.choose (1 + n) 1 : ℕ) : ℂ) := by
  ext n; simp [toC, F2, add_comm]

theorem qHypFormal_F1 (q : ℂ) : QHypergeometricTypeFormal q F1 := by
  refine ⟨1 - Polynomial.X, 1 - Polynomial.C q * Polynomial.X, 0, 1, ?_, one_ne_zero, ?_⟩
  · intro h; have := congrArg (Polynomial.eval 0) h; simp at this
  · have h1 : (PowerSeries.mk 1 : PowerSeries ℂ) * (1 - PowerSeries.X) = 1 :=
      mk_one_mul_one_sub_eq_one ℂ
    have h2 := congrArg (rescale q) h1
    rw [map_mul, map_sub, map_one, rescale_X] at h2
    rw [toC_F1]
    push_cast
    rw [mul_one, mul_one, mul_zero, add_zero, mul_comm, h2, mul_comm, h1]

theorem qHypFormal_F2 (q : ℂ) : QHypergeometricTypeFormal q F2 := by
  refine ⟨(1 - Polynomial.X) ^ 2, (1 - Polynomial.C q * Polynomial.X) ^ 2, 0, 1, ?_, one_ne_zero,
    ?_⟩
  · intro h; have := congrArg (Polynomial.eval 0) h; simp at this
  · have h1 : (PowerSeries.mk fun n => ((Nat.choose (1 + n) 1 : ℕ) : ℂ)) *
        (1 - PowerSeries.X) ^ (1 + 1) = 1 := mk_add_choose_mul_one_sub_pow_eq_one ℂ 1
    have h2 := congrArg (rescale q) h1
    rw [map_mul, map_pow, map_sub, map_one, rescale_X] at h2
    rw [toC_F2]
    push_cast
    rw [mul_one, mul_one, mul_zero, add_zero, mul_comm, h2, mul_comm, h1]

/-- **Conjecture 00000007661 is false** with the formal reading of the functional equation. -/
theorem conjecture_false_formal (q : ℂ) (_hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ¬ (∀ F : PowerSeries ℤ, (QHypergeometricTypeFormal q F ∧ radius F = 1) ↔ RateBigO q F) ∧
    ¬ (∀ F : PowerSeries ℤ, QHypergeometricTypeFormal q F → radius F = 1 → RateLittleO q F →
      IsPoly F) ∧
    ¬ (∀ F : PowerSeries ℤ, (QHypergeometricTypeFormal q F ∧ radius F = 1) ↔
      (RateBigO q F ∧ (RateLittleO q F → IsPoly F))) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact not_rateBigO_F2 hq1 ((h F2).mp ⟨qHypFormal_F2 q, radius_F2⟩)
  · exact not_isPoly_F1 (h F1 (qHypFormal_F1 q) radius_F1 (rateLittleO_F1 q))
  · exact not_isPoly_F1 (((h F1).mp ⟨qHypFormal_F1 q, radius_F1⟩).2 (rateLittleO_F1 q))

end C7661
