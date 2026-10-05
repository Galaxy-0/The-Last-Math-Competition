import Mathlib

/-!
# Conjecture 00000007664 is false

Conjecture 00000007664 reads:

> Definition: The Jackson q-Gamma function is
> `Gamma_q(x) = (1-q)^{1-x} (q;q)_infinity / (q^x;q)_infinity`, where `(a;q)_infinity` is the
> infinite q-Pochhammer product `prod_{k>=0} (1 - a q^k)`. Conjecture: For every algebraic `q` in
> `(0,1)` and any two distinct positive integers `m, n`, the numbers `Gamma_q(m/n)` and
> `Gamma_q(1-m/n)` are algebraically independent over `Q(q)`, except when `m/n = 1/2`.

Counterexample: `q = 1/4` (rational, hence algebraic), `m = 3`, `n = 2`. Then `m/n = 3/2` and
`1 - m/n = -1/2`; neither is a pole of `Gamma_q` (the poles are `0, -1, -2, ...`). The defining
products satisfy `(q^{-1/2};q)_∞ = (1 - q^{-1/2})(1 - q^{1/2}) (q^{3/2};q)_∞`, which at `q = 1/4`
gives `9 Γ_q(3/2) + 8 Γ_q(-1/2) = 0`. So the nonzero polynomial `9X + 8Y ∈ ℚ(q)[X,Y]` vanishes
at the pair, which is therefore algebraically dependent.

Definitions (all from scratch, matching the statement):
* `qPochPartial a q N = ∏_{k<N} (1 - a q^k)`; `qPochInf a q` is the limit of these partial
  products (`limUnder atTop`); for every product used we prove the limit exists
  (`counterexample_values_genuine`), so no junk value is involved.
* `qGamma q x = (1-q)^{1-x} (q;q)_∞ / (q^x;q)_∞` with real powers `Real.rpow`.
* Algebraic independence is Mathlib's `AlgebraicIndependent` over the intermediate field
  `ℚ(q) = IntermediateField.adjoin ℚ {q}` of `ℝ`.

Main theorem: `C7664.conjecture_00000007664_false : ¬ C7664.Conjecture`.
-/

open Filter Topology

namespace C7664

/-- Partial products `∏_{k<N} (1 - a q^k)` of the q-Pochhammer symbol. -/
def qPochPartial (a q : ℝ) (N : ℕ) : ℝ := ∏ k ∈ Finset.range N, (1 - a * q ^ k)

/-- The infinite q-Pochhammer symbol `(a;q)_∞ = ∏_{k≥0} (1 - a q^k)`, the limit of the partial
products. -/
noncomputable def qPochInf (a q : ℝ) : ℝ := limUnder atTop (qPochPartial a q)

/-- Jackson's q-Gamma function `Γ_q(x) = (1-q)^{1-x} (q;q)_∞ / (q^x;q)_∞` (real powers). -/
noncomputable def qGamma (q x : ℝ) : ℝ := (1 - q) ^ (1 - x) * qPochInf q q / qPochInf (q ^ x) q

section Convergence

variable {a q : ℝ}

lemma factor_mem (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    0 ≤ 1 - a * q ^ k ∧ 1 - a * q ^ k ≤ 1 := by
  have h1 : q ^ k ≤ 1 := pow_le_one₀ hq0 hq1.le
  have h2 : 0 ≤ q ^ k := pow_nonneg hq0 k
  constructor <;> nlinarith

lemma partial_nonneg (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    0 ≤ qPochPartial a q N :=
  Finset.prod_nonneg fun k _ => (factor_mem ha0 ha1 hq0 hq1 k).1

lemma partial_antitone (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Antitone (qPochPartial a q) := by
  refine antitone_nat_of_succ_le fun N => ?_
  simp only [qPochPartial, Finset.prod_range_succ]
  have := partial_nonneg ha0 ha1 hq0 hq1 N
  have h := factor_mem ha0 ha1 hq0 hq1 N
  unfold qPochPartial at this
  nlinarith

/-- Weierstrass product inequality: `∏_{k<N} (1 - a q^k) ≥ 1 - a ∑_{k<N} q^k`. -/
lemma partial_ge (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    1 - a * ∑ k ∈ Finset.range N, q ^ k ≤ qPochPartial a q N := by
  induction N with
  | zero => simp [qPochPartial]
  | succ N ih =>
    simp only [qPochPartial, Finset.prod_range_succ, Finset.sum_range_succ] at ih ⊢
    have h := factor_mem ha0 ha1 hq0 hq1 N
    have hs : 0 ≤ ∑ k ∈ Finset.range N, q ^ k := Finset.sum_nonneg fun k _ => pow_nonneg hq0 k
    have hp : 0 ≤ a * q ^ N := mul_nonneg ha0 (pow_nonneg hq0 N)
    nlinarith [mul_nonneg (mul_nonneg ha0 hs) hp]

/-- For `0 ≤ a ≤ 1` and `0 ≤ q < 1` the partial products converge, and the limit
`(a;q)_∞` is at least `1 - a/(1-q)`. -/
lemma tendsto_partial (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (qPochPartial a q) atTop (𝓝 (qPochInf a q)) ∧ 1 - a / (1 - q) ≤ qPochInf a q := by
  have hanti := partial_antitone ha0 ha1 hq0 hq1
  have hbdd : BddBelow (Set.range (qPochPartial a q)) := by
    refine ⟨0, ?_⟩
    rw [mem_lowerBounds, Set.forall_mem_range]
    exact partial_nonneg ha0 ha1 hq0 hq1
  have ht := tendsto_atTop_ciInf hanti hbdd
  rw [qPochInf, ht.limUnder_eq]
  refine ⟨ht, le_ciInf fun N => le_trans ?_ (partial_ge ha0 ha1 hq0 hq1 N)⟩
  have hg : ∑ k ∈ Finset.range N, q ^ k ≤ 1 / (1 - q) := by
    have h := geom_sum_Ico_le_of_lt_one (x := q) (m := 0) (n := N) hq0 hq1
    rwa [← Finset.range_eq_Ico, pow_zero] at h
  have : a * ∑ k ∈ Finset.range N, q ^ k ≤ a * (1 / (1 - q)) := mul_le_mul_of_nonneg_left hg ha0
  rw [mul_one_div] at this
  linarith

end Convergence

/-! ### The concrete point `q = 1/4`, `x = 3/2` and `1 - x = -1/2` -/

lemma rpow_three_halves : ((1:ℝ)/4) ^ ((3:ℝ)/2) = 1/8 := by
  rw [show ((1:ℝ)/4) = ((1:ℝ)/2) ^ (2:ℝ) by norm_num [Real.rpow_two], ← Real.rpow_mul (by norm_num)]
  norm_num

lemma rpow_neg_half : ((1:ℝ)/4) ^ (-(1:ℝ)/2) = 2 := by
  rw [show ((1:ℝ)/4) = ((1:ℝ)/2) ^ (2:ℝ) by norm_num [Real.rpow_two], ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `(q;q)_∞` at `q = 1/4` converges and is `≥ 2/3`. -/
lemma A_spec : Tendsto (qPochPartial (1/4) (1/4)) atTop (𝓝 (qPochInf (1/4) (1/4))) ∧
    (2:ℝ)/3 ≤ qPochInf (1/4) (1/4) := by
  obtain ⟨h1, h2⟩ := tendsto_partial (a := 1/4) (q := 1/4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨h1, by norm_num at h2 ⊢; linarith⟩

/-- `(q^{3/2};q)_∞ = (1/8; 1/4)_∞` converges and is `≥ 5/6`. -/
lemma L_spec : Tendsto (qPochPartial (1/8) (1/4)) atTop (𝓝 (qPochInf (1/8) (1/4))) ∧
    (5:ℝ)/6 ≤ qPochInf (1/8) (1/4) := by
  obtain ⟨h1, h2⟩ := tendsto_partial (a := 1/8) (q := 1/4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨h1, by norm_num at h2 ⊢; linarith⟩

/-- The shift identity `(q^{-1/2};q)_∞ = (1 - q^{-1/2})(1 - q^{1/2}) (q^{3/2};q)_∞` at `q = 1/4`:
the partial products of `(2; 1/4)_∞` converge to `-(1/2) (1/8; 1/4)_∞`. -/
lemma shift_tendsto :
    Tendsto (qPochPartial 2 (1/4)) atTop (𝓝 (-(1/2) * qPochInf (1/8) (1/4))) := by
  rw [← tendsto_add_atTop_iff_nat 2]
  have heq : (fun N => qPochPartial 2 (1/4) (N + 2)) =
      fun N => -(1/2) * qPochPartial (1/8) (1/4) N := by
    funext N
    simp only [qPochPartial]
    rw [add_comm N 2, Finset.prod_range_add]
    congr 1
    · simp [Finset.prod_range_succ]; norm_num
    · refine Finset.prod_congr rfl fun k _ => ?_
      rw [pow_add]; ring
  rw [heq]
  exact L_spec.1.const_mul _

lemma shift_eq : qPochInf 2 (1/4) = -(1/2) * qPochInf (1/8) (1/4) := by
  rw [qPochInf, shift_tendsto.limUnder_eq]

/-- `Γ_{1/4}(3/2) = (3/4)^{-1/2} A / L`. -/
lemma gamma_three_halves :
    qGamma (1/4) (3/2) = (3/4) ^ (-(1:ℝ)/2) * qPochInf (1/4) (1/4) / qPochInf (1/8) (1/4) := by
  rw [qGamma, rpow_three_halves]; norm_num

/-- `Γ_{1/4}(-1/2) = (3/4)^{3/2} A / (-(1/2) L)`. -/
lemma gamma_neg_half :
    qGamma (1/4) (-(1:ℝ)/2) = (3/4) ^ ((3:ℝ)/2) * qPochInf (1/4) (1/4) /
      (-(1/2) * qPochInf (1/8) (1/4)) := by
  rw [qGamma, rpow_neg_half, shift_eq]; norm_num

lemma rpow_relation : (16:ℝ) * (3/4) ^ ((3:ℝ)/2) = 9 * (3/4) ^ (-(1:ℝ)/2) := by
  rw [show (3:ℝ)/2 = 2 + (-(1:ℝ)/2) by norm_num, Real.rpow_add (by norm_num), Real.rpow_two]
  ring

/-- The linear relation `9 Γ_q(3/2) + 8 Γ_q(-1/2) = 0` at `q = 1/4`. -/
lemma linear_relation : 9 * qGamma (1/4) (3/2) + 8 * qGamma (1/4) (-(1:ℝ)/2) = 0 := by
  rw [gamma_three_halves, gamma_neg_half]
  have hL : qPochInf (1/8) (1/4) ≠ 0 := by
    have := L_spec.2; intro h; rw [h] at this; norm_num at this
  have key : ∀ c₁ c₂ A L : ℝ, L ≠ 0 →
      9 * (c₁ * A / L) + 8 * (c₂ * A / (-(1/2) * L)) = A / L * (9 * c₁ - 16 * c₂) := by
    intro c₁ c₂ A L hL; field_simp; ring
  rw [key _ _ _ _ hL, ← rpow_relation, sub_self, mul_zero]

/-! ### The conjecture and its refutation -/

/-- Conjecture 00000007664, read literally: for every algebraic `q ∈ (0,1)` and any two distinct
positive integers `m, n` with `m/n ≠ 1/2`, the numbers `Γ_q(m/n)` and `Γ_q(1 - m/n)` are
algebraically independent over `ℚ(q)` (the subfield of `ℝ` generated by `q`). -/
def Conjecture : Prop :=
  ∀ q : ℝ, IsAlgebraic ℚ q → 0 < q → q < 1 →
    ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n → (m : ℝ) / n ≠ 1 / 2 →
      AlgebraicIndependent (IntermediateField.adjoin ℚ ({q} : Set ℝ))
        ![qGamma q ((m : ℝ) / n), qGamma q (1 - (m : ℝ) / n)]

/-- The two values at the counterexample `q = 1/4`, `m/n = 3/2` are genuine: every q-Pochhammer
product in the definition converges (as a limit of partial products), both denominators
`(q^{3/2};q)_∞` and `(q^{-1/2};q)_∞` are nonzero, and `Γ_q(3/2) > 0 > Γ_q(-1/2)`. -/
theorem counterexample_values_genuine :
    Tendsto (qPochPartial (1/4) (1/4)) atTop (𝓝 (qPochInf (1/4) (1/4))) ∧
    0 < qPochInf (1/4) (1/4) ∧
    Tendsto (qPochPartial ((1/4) ^ ((3:ℝ)/2)) (1/4)) atTop
      (𝓝 (qPochInf ((1/4) ^ ((3:ℝ)/2)) (1/4))) ∧
    0 < qPochInf ((1/4) ^ ((3:ℝ)/2)) (1/4) ∧
    Tendsto (qPochPartial ((1/4) ^ (-(1:ℝ)/2)) (1/4)) atTop
      (𝓝 (qPochInf ((1/4) ^ (-(1:ℝ)/2)) (1/4))) ∧
    qPochInf ((1/4) ^ (-(1:ℝ)/2)) (1/4) < 0 ∧
    0 < qGamma (1/4) (3/2) ∧ qGamma (1/4) (-(1:ℝ)/2) < 0 := by
  obtain ⟨hA, hA'⟩ := A_spec
  obtain ⟨hL, hL'⟩ := L_spec
  have hc₁ : (0:ℝ) < (3/4) ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
  have hc₂ : (0:ℝ) < (3/4) ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
  have hApos : 0 < qPochInf (1/4) (1/4) := by linarith
  have hLpos : 0 < qPochInf (1/8) (1/4) := by linarith
  rw [rpow_three_halves, rpow_neg_half, gamma_three_halves, gamma_neg_half, shift_eq]
  refine ⟨hA, hApos, hL, hLpos, ?_, by nlinarith, by positivity, ?_⟩
  · rw [← shift_eq, qPochInf, shift_tendsto.limUnder_eq]; exact shift_tendsto
  · apply div_neg_of_pos_of_neg (by positivity); nlinarith

/-- The explicit algebraic relation at the counterexample: the nonzero linear polynomial
`P(X, Y) = 9X + 8Y` with rational coefficients vanishes at `(Γ_q(3/2), Γ_q(-1/2))`, `q = 1/4`. -/
theorem not_algebraicIndependent :
    ¬ AlgebraicIndependent (IntermediateField.adjoin ℚ ({(1/4 : ℝ)} : Set ℝ))
        ![qGamma (1/4) (3/2), qGamma (1/4) (-(1:ℝ)/2)] := by
  intro h
  set K := IntermediateField.adjoin ℚ ({(1/4 : ℝ)} : Set ℝ)
  let P : MvPolynomial (Fin 2) K := 9 * MvPolynomial.X 0 + 8 * MvPolynomial.X 1
  have hP : MvPolynomial.aeval ![qGamma (1/4) (3/2), qGamma (1/4) (-(1:ℝ)/2)] P = 0 := by
    simp only [P, map_add, map_mul, map_ofNat, MvPolynomial.aeval_X]
    simpa using linear_relation
  have h0 := (algebraicIndependent_iff.1 h) P hP
  have h1 : MvPolynomial.aeval (![1, 0] : Fin 2 → ℝ) P = 9 := by
    simp [P]
  rw [h0, map_zero] at h1
  norm_num at h1

/-- **Main theorem.** Conjecture 00000007664 is false: at the algebraic number `q = 1/4 ∈ (0,1)`
and the distinct positive integers `m = 3`, `n = 2` (so `m/n = 3/2 ≠ 1/2`), the numbers
`Γ_q(3/2)` and `Γ_q(1 - 3/2) = Γ_q(-1/2)` are not algebraically independent over `ℚ(q)`. -/
theorem conjecture_00000007664_false : ¬ Conjecture := by
  intro hC
  have halg : IsAlgebraic ℚ (1/4 : ℝ) := by
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (1/4 : ℚ)
  have h := hC (1/4) halg (by norm_num) (by norm_num) 3 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have e1 : ((3:ℕ) : ℝ) / (2:ℕ) = 3/2 := by norm_num
  have e2 : 1 - (3:ℝ) / 2 = -(1:ℝ)/2 := by norm_num
  rw [e1, e2] at h
  exact not_algebraicIndependent h

end C7664
