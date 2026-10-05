import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

/-!
# The explicit asymptotic clause in conjecture 00000007668 is false

Here `(z;q)_N` has its standard finite q-Pochhammer meaning
`∏ k ∈ range N, (1 - z * q^k)`.  All roots below are the actual complex
polynomial roots, counted with their algebraic multiplicities.
-/

noncomputable section

open scoped BigOperators Topology
open Polynomial Filter

namespace Conjecture7668

/-- The standard finite q-Pochhammer polynomial, in the complex variable `X`. -/
def qPochhammer (q : ℝ) (N : ℕ) : ℂ[X] :=
  ∏ k ∈ Finset.range N, (1 - C ((q : ℂ) ^ k) * X)

/-- Product of the moduli of all roots, including algebraic multiplicities. -/
def rootModulusProduct (q : ℝ) (N : ℕ) : ℝ :=
  ((qPochhammer q N).roots.map (fun z : ℂ => ‖z‖)).prod

/-- The nonnegative real `N`th root of the product of root moduli.
Only `N > 0` is used in the statements about the conjecture. -/
def geometricMean (q : ℝ) (N : ℕ) : ℝ :=
  (rootModulusProduct q N) ^ (1 / (N : ℝ))

theorem qPochhammer_eval (q : ℝ) (N : ℕ) (z : ℂ) :
    (qPochhammer q N).eval z =
      ∏ k ∈ Finset.range N, (1 - z * (q : ℂ) ^ k) := by
  simp [qPochhammer, Polynomial.eval_prod, mul_comm]

theorem linear_factor_ne_zero (a : ℂ) : (1 - C a * X : ℂ[X]) ≠ 0 := by
  intro h
  have h' := congrArg (Polynomial.eval 0) h
  simp at h'

theorem qPochhammer_ne_zero (q : ℝ) (N : ℕ) : qPochhammer q N ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  exact linear_factor_ne_zero _

theorem linear_factor_roots (a : ℂ) (ha : a ≠ 0) :
    (1 - C a * X : ℂ[X]).roots = {a⁻¹} := by
  have hfactor : (1 - C a * X : ℂ[X]) = C (-a) * (X - C a⁻¹) := by
    rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ ha]
    simp
    ring
  rw [hfactor, Polynomial.roots_C_mul _ (neg_ne_zero.mpr ha),
    Polynomial.roots_X_sub_C]

theorem qPochhammer_roots (q : ℝ) (hq : q ≠ 0) (N : ℕ) :
    (qPochhammer q N).roots =
      (Finset.range N).val.map (fun k => ((q : ℂ) ^ k)⁻¹) := by
  rw [qPochhammer, Polynomial.roots_prod _ _ (qPochhammer_ne_zero q N)]
  simp_rw [linear_factor_roots _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hq))]
  simp

theorem qPochhammer_roots_card (q : ℝ) (hq : q ≠ 0) (N : ℕ) :
    (qPochhammer q N).roots.card = N := by
  rw [qPochhammer_roots q hq N]
  simp

theorem rootModulusProduct_eq (q : ℝ) (hq : 0 < q) (N : ℕ) :
    rootModulusProduct q N = ∏ k ∈ Finset.range N, (q ^ k)⁻¹ := by
  rw [rootModulusProduct, qPochhammer_roots q hq.ne' N, Multiset.map_map]
  simp [Function.comp_def, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hq, Finset.prod]

theorem sum_range_real (N : ℕ) :
    (∑ k ∈ Finset.range N, (k : ℝ)) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem rootModulusProduct_rpow (q : ℝ) (hq : 0 < q) (N : ℕ) :
    rootModulusProduct q N = q ^ (-((N : ℝ) * ((N : ℝ) - 1) / 2)) := by
  rw [rootModulusProduct_eq q hq N]
  simp_rw [← Real.rpow_natCast, ← Real.rpow_neg hq.le]
  rw [← Real.rpow_sum_of_pos hq, Finset.sum_neg_distrib, sum_range_real]

theorem geometricMean_eq (q : ℝ) (hq : 0 < q) (N : ℕ) (hN : 0 < N) :
    geometricMean q N = q ^ (-((N : ℝ) - 1) / 2) := by
  rw [geometricMean, rootModulusProduct_rpow q hq N, ← Real.rpow_mul hq.le]
  congr 1
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem rootModulusProduct_nonneg (q : ℝ) (N : ℕ) :
    0 ≤ rootModulusProduct q N := by
  unfold rootModulusProduct
  generalize (qPochhammer q N).roots = s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
      simpa only [Multiset.map_cons, Multiset.prod_cons] using mul_nonneg (norm_nonneg z) ih

theorem geometricMean_nonneg (q : ℝ) (N : ℕ) : 0 ≤ geometricMean q N :=
  Real.rpow_nonneg (rootModulusProduct_nonneg q N) _

theorem geometricMean_pow (q : ℝ) (N : ℕ) (hN : 0 < N) :
    geometricMean q N ^ N = rootModulusProduct q N := by
  simpa only [geometricMean, one_div] using
    Real.rpow_inv_natCast_pow (rootModulusProduct_nonneg q N) hN.ne'

/-- The leading expression appearing in the source, retaining its factor `1/(1+q)`. -/
def claimedMainTerm (q : ℝ) (N : ℕ) : ℝ :=
  q ^ (-((N : ℝ) - 1) / 2) / (1 + q)

/-- The asserted exponentially decaying relative-error scale, with real division by `2`. -/
def errorScale (q : ℝ) (N : ℕ) : ℝ := q ^ ((N : ℝ) / 2)

/-- Relative error, so the Big-O term is inside the multiplicative parentheses. -/
def relativeError (q : ℝ) (N : ℕ) : ℝ :=
  geometricMean q N / claimedMainTerm q N - 1

/-- The precise eventual bound asserted for a fixed real `q`. -/
def RelativeAsymptotic (q : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → |relativeError q N| ≤ C * errorScale q N

/-- The explicit necessary asymptotic clause of the bilingual conjecture.
The additional unspecified theta/Jensen/transcendence clauses are not defined here. -/
def NecessaryClause : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 → RelativeAsymptotic q

theorem errorScale_nonneg (q : ℝ) (hq : 0 ≤ q) (N : ℕ) :
    0 ≤ errorScale q N := Real.rpow_nonneg hq _

/-- The explicit quantifiers are exactly the usual fixed-`q` relative Big-O statement. -/
theorem relativeAsymptotic_iff_isBigO (q : ℝ) (hq : 0 ≤ q) :
    RelativeAsymptotic q ↔
      Asymptotics.IsBigO atTop (relativeError q) (errorScale q) := by
  rw [Asymptotics.isBigO_iff']
  constructor
  · rintro ⟨C, hC, N₀, _, hbound⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [eventually_ge_atTop N₀] with N hN
    simpa only [Real.norm_eq_abs, abs_of_nonneg (errorScale_nonneg q hq N)] using
      hbound N hN
  · rintro ⟨C, hC, hbound⟩
    obtain ⟨M, hM⟩ := eventually_atTop.mp hbound
    refine ⟨C, hC, max 1 M, le_max_left _ _, ?_⟩
    intro N hN
    have hb := hM N ((le_max_right 1 M).trans hN)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (errorScale_nonneg q hq N)] using hb

theorem relativeError_eq (q : ℝ) (hq : 0 < q) (N : ℕ) (hN : 0 < N) :
    relativeError q N = q := by
  rw [relativeError, geometricMean_eq q hq N hN, claimedMainTerm]
  have ha : q ^ (-((N : ℝ) - 1) / 2) ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  have hb : 1 + q ≠ 0 := by positivity
  field_simp

theorem errorScale_tendsto_zero (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (errorScale q) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (Real.rpow_nonneg hq.le (1 / 2 : ℝ))
    (Real.rpow_lt_one hq.le hq1 (by norm_num : (0 : ℝ) < 1 / 2))
  convert h using 1
  ext N
  rw [errorScale, ← Real.rpow_mul_natCast hq.le]
  congr 1
  ring

theorem not_relativeAsymptotic (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    ¬ RelativeAsymptotic q := by
  rintro ⟨C, _, N₀, hN₀, hbound⟩
  have hlim : Tendsto (fun N => C * errorScale q N) atTop (𝓝 0) := by
    simpa using (errorScale_tendsto_zero q hq hq1).const_mul C
  have hsmall : ∀ᶠ N in atTop, C * errorScale q N < q :=
    hlim.eventually (gt_mem_nhds hq)
  obtain ⟨N, hN, hsmallN⟩ := ((eventually_ge_atTop N₀).and hsmall).exists
  have hb := hbound N hN
  rw [relativeError_eq q hq N (lt_of_lt_of_le (by omega : 0 < N₀) hN),
    abs_of_pos hq] at hb
  exact (not_lt_of_ge hb) hsmallN

/-- Hence the explicit necessary clause of conjecture 00000007668 is false. -/
theorem conjecture7668_disproof : ¬ NecessaryClause := by
  intro h
  exact not_relativeAsymptotic (1 / 2) (by norm_num) (by norm_num)
    (h (1 / 2) (by norm_num) (by norm_num))

theorem not_relative_isBigO (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    ¬ Asymptotics.IsBigO atTop (relativeError q) (errorScale q) := by
  intro h
  exact not_relativeAsymptotic q hq hq1
    ((relativeAsymptotic_iff_isBigO q hq.le).mpr h)

/-- Any full interpretation retaining the explicit clause is therefore false.
The hypothesis expresses necessity, not equivalence with unspecified refinements. -/
theorem no_completion (FullSource : Prop) (hnecessary : FullSource → NecessaryClause) :
    ¬ FullSource := fun h => conjecture7668_disproof (hnecessary h)

end Conjecture7668
