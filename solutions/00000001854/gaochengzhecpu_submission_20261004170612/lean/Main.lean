import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The number of `n × n` matrices over a finite field with `q` elements whose characteristic
polynomial is squarefree is not `q ^ (n ^ 2) * ∏ (1 - q ^ (-i ^ 2))`: for the product over
`1 ≤ i ≤ n` the identity fails for every finite field and every `n ≥ 1`, and at `n = 1` it
fails for every non-empty truncation of the product and for the infinite product. -/
namespace Conjecture1854

open Finset

/-- The number of `n × n` matrices over `F` whose characteristic polynomial is squarefree. -/
noncomputable def sqfreeCount (F : Type) [Field F] (n : ℕ) : ℕ :=
  Nat.card {M : Matrix (Fin n) (Fin n) F // Squarefree M.charpoly}

/-- The proposed closed form with the product taken over `1 ≤ i ≤ m`. -/
def formula (q n m : ℕ) : ℚ :=
  (q : ℚ) ^ (n ^ 2) * ∏ i ∈ Icc 1 m, (1 - 1 / (q : ℚ) ^ (i ^ 2))

/-- The partial products of the infinite product `∏_{i ≥ 1} (1 - q ^ (-i ^ 2))`. -/
noncomputable def partialProduct (q m : ℕ) : ℝ :=
  ∏ i ∈ Icc 1 m, (1 - 1 / (q : ℝ) ^ (i ^ 2))

section Count

variable {F : Type} [Field F]

/-- The characteristic polynomial of a `1 × 1` matrix has degree one, so it is irreducible and
in particular squarefree. -/
theorem squarefree_charpoly_one (M : Matrix (Fin 1) (Fin 1) F) : Squarefree M.charpoly := by
  apply Irreducible.squarefree
  apply Polynomial.irreducible_of_degree_eq_one
  rw [Matrix.charpoly_degree_eq_dim]
  simp

/-- Every `1 × 1` matrix counts: the true value at `n = 1` is `q`. -/
theorem sqfreeCount_one [Fintype F] : sqfreeCount F 1 = Fintype.card F := by
  unfold sqfreeCount
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv squarefree_charpoly_one)]
  change Nat.card (Fin 1 → Fin 1 → F) = Fintype.card F
  rw [Nat.card_congr (Equiv.funUnique (Fin 1) (Fin 1 → F)),
    Nat.card_congr (Equiv.funUnique (Fin 1) F), Nat.card_eq_fintype_card]

end Count

section Arithmetic

/-- Clearing denominators in the proposed closed form. -/
theorem formula_mul (q n m : ℕ) (hq : 2 ≤ q) :
    formula q n m * (q : ℚ) ^ (∑ i ∈ Icc 1 m, i ^ 2) =
      (q : ℚ) ^ (n ^ 2) * ∏ i ∈ Icc 1 m, ((q : ℚ) ^ (i ^ 2) - 1) := by
  have hq0 : (q : ℚ) ≠ 0 := by
    have : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
    exact this.ne'
  unfold formula
  rw [mul_assoc, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro i _
  have : (q : ℚ) ^ (i ^ 2) ≠ 0 := pow_ne_zero _ hq0
  field_simp

/-- For `n ≥ 2` the exponents `1 ^ 2 + ⋯ + n ^ 2` add up to more than `n ^ 2`. -/
theorem sum_sq_gt (n : ℕ) (hn : 2 ≤ n) : n ^ 2 + 1 ≤ ∑ i ∈ Icc 1 n, i ^ 2 := by
  have hsub : ({1, n} : Finset ℕ) ⊆ Icc 1 n := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rw [mem_Icc]
    omega
  have h : ∑ i ∈ ({1, n} : Finset ℕ), i ^ 2 ≤ ∑ i ∈ Icc 1 n, i ^ 2 :=
    sum_le_sum_of_subset hsub
  have h1n : (1 : ℕ) ∉ ({n} : Finset ℕ) := by
    rw [mem_singleton]
    omega
  rw [sum_insert h1n, sum_singleton] at h
  omega

/-- Each factor `q ^ (i ^ 2) - 1` with `i ≥ 1` is coprime to `q`, hence so is their product. -/
theorem isCoprime_prod (q n : ℕ) :
    IsCoprime (q : ℤ) (∏ i ∈ Icc 1 n, ((q : ℤ) ^ (i ^ 2) - 1)) := by
  apply IsCoprime.prod_right
  intro i hi
  rw [mem_Icc] at hi
  obtain ⟨k, hk⟩ : ∃ k, i ^ 2 = k + 1 := by
    have : 1 ≤ i ^ 2 := Nat.one_le_pow _ _ (by omega)
    exact ⟨i ^ 2 - 1, by omega⟩
  refine ⟨(q : ℤ) ^ k, -1, ?_⟩
  rw [hk, pow_succ]
  ring

/-- If `1 ^ 2 + ⋯ + m ^ 2` exceeds `n ^ 2`, then for `q ≥ 2` the value of the proposed closed
form with the product over `1 ≤ i ≤ m` is not a natural number at all. -/
theorem formula_not_natural_of_sum (q n m : ℕ) (hq : 2 ≤ q)
    (hS : n ^ 2 + 1 ≤ ∑ i ∈ Icc 1 m, i ^ 2) (N : ℕ) : (N : ℚ) ≠ formula q n m := by
  intro h
  have hQ := formula_mul q n m hq
  rw [← h] at hQ
  have hZ : (N : ℤ) * (q : ℤ) ^ (∑ i ∈ Icc 1 m, i ^ 2) =
      (q : ℤ) ^ (n ^ 2) * ∏ i ∈ Icc 1 m, ((q : ℤ) ^ (i ^ 2) - 1) := by
    exact_mod_cast hQ
  obtain ⟨t, ht⟩ : ∃ t, ∑ i ∈ Icc 1 m, i ^ 2 = n ^ 2 + 1 + t :=
    ⟨_, (Nat.add_sub_cancel' hS).symm⟩
  have hq0 : (q : ℤ) ^ (n ^ 2) ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (by omega : q ≠ 0)
  have hdvd : (q : ℤ) ∣ ∏ i ∈ Icc 1 m, ((q : ℤ) ^ (i ^ 2) - 1) := by
    apply (mul_dvd_mul_iff_left hq0).mp
    rw [← hZ, ht]
    exact ⟨(N : ℤ) * (q : ℤ) ^ t, by ring⟩
  have hunit : IsUnit (q : ℤ) := (isCoprime_prod q m).isUnit_of_dvd' (dvd_refl _) hdvd
  rcases Int.isUnit_iff.mp hunit with h1 | h1
  · have : q = 1 := by exact_mod_cast h1
    omega
  · have : (0 : ℤ) ≤ q := Int.natCast_nonneg q
    omega

/-- For `q ≥ 2` and `n ≥ 2` the value of the proposed closed form (product over `1 ≤ i ≤ n`) is
not a natural number at all. -/
theorem formula_not_natural (q n : ℕ) (hq : 2 ≤ q) (hn : 2 ≤ n) (N : ℕ) :
    (N : ℚ) ≠ formula q n n :=
  formula_not_natural_of_sum q n n hq (sum_sq_gt n hn) N

/-- A non-empty truncation of the product is at most its first factor `1 - 1 / x`. -/
theorem prod_le_first {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (x : K)
    (hx : 1 < x) (m : ℕ) (hm : 1 ≤ m) :
    ∏ i ∈ Icc 1 m, (1 - 1 / x ^ (i ^ 2)) ≤ 1 - 1 / x := by
  have hfac : ∀ i : ℕ, 0 ≤ 1 - 1 / x ^ (i ^ 2) ∧ 1 - 1 / x ^ (i ^ 2) ≤ 1 := by
    intro i
    have hpow : (1 : K) ≤ x ^ (i ^ 2) := one_le_pow₀ hx.le
    have hpos : (0 : K) < x ^ (i ^ 2) := lt_of_lt_of_le zero_lt_one hpow
    have hinv : 1 / x ^ (i ^ 2) ≤ 1 := by
      rw [div_le_one hpos]
      exact hpow
    have hinv0 : 0 ≤ 1 / x ^ (i ^ 2) := by positivity
    constructor <;> linarith
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [prod_Icc_succ_top (by omega)]
    have h0 : 0 ≤ ∏ i ∈ Icc 1 k, (1 - 1 / x ^ (i ^ 2)) := prod_nonneg fun i _ => (hfac i).1
    calc (∏ i ∈ Icc 1 k, (1 - 1 / x ^ (i ^ 2))) * (1 - 1 / x ^ ((k + 1) ^ 2))
        ≤ (∏ i ∈ Icc 1 k, (1 - 1 / x ^ (i ^ 2))) * 1 :=
          mul_le_mul_of_nonneg_left (hfac (k + 1)).2 h0
      _ = ∏ i ∈ Icc 1 k, (1 - 1 / x ^ (i ^ 2)) := mul_one _
      _ ≤ 1 - 1 / x := ih

/-- At `n = 1` every non-empty truncation of the product gives a value of at most `q - 1`. -/
theorem formula_one_le (q m : ℕ) (hq : 2 ≤ q) (hm : 1 ≤ m) : formula q 1 m ≤ (q : ℚ) - 1 := by
  have hq1 : (1 : ℚ) < q := by exact_mod_cast (by omega : 1 < q)
  have hq0 : (0 : ℚ) < q := by linarith
  unfold formula
  have h1 : (q : ℚ) ^ (1 ^ 2) = q := by norm_num
  have h2 : (q : ℚ) * (1 - 1 / (q : ℚ)) = (q : ℚ) - 1 := by field_simp
  rw [h1, ← h2]
  exact mul_le_mul_of_nonneg_left (prod_le_first (q : ℚ) hq1 m hm) hq0.le

end Arithmetic

section Main

variable (F : Type) [Field F] [Fintype F]

/-- A finite field has at least two elements. -/
theorem two_le_card : 2 ≤ Fintype.card F := Fintype.one_lt_card

/-- At `n = 1` the identity fails for every finite field and every non-empty truncation
`1 ≤ i ≤ m` of the product. -/
theorem truncated_formula_fails_at_one (m : ℕ) (hm : 1 ≤ m) :
    (sqfreeCount F 1 : ℚ) ≠ formula (Fintype.card F) 1 m := by
  rw [sqfreeCount_one]
  have h := formula_one_le (Fintype.card F) m (two_le_card F) hm
  intro heq
  rw [← heq] at h
  linarith

/-- With the product over `1 ≤ i ≤ n`, the identity fails for every finite field and every
`n ≥ 1`. -/
theorem formula_fails (n : ℕ) (hn : 1 ≤ n) :
    (sqfreeCount F n : ℚ) ≠ formula (Fintype.card F) n n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    exact truncated_formula_fails_at_one F 1 (le_refl 1)
  · exact formula_not_natural _ n (two_le_card F) h _

/-- The convention with the product over `1 ≤ i ≤ n - 1`, which is empty at `n = 1`, fails at
`n = 5` for every finite field: `1 + 4 + 9 + 16 = 30 > 25`, so the value is not an integer. -/
theorem shifted_formula_fails : (sqfreeCount F 5 : ℚ) ≠ formula (Fintype.card F) 5 4 :=
  formula_not_natural_of_sum _ 5 4 (two_le_card F) (by decide) _

/-- At `n = 1` the identity also fails for the infinite product: if the partial products
converge to `L`, then the true count `q` differs from `q ^ (1 ^ 2) * L`. -/
theorem infinite_product_fails_at_one (L : ℝ)
    (hL : Filter.Tendsto (fun m => partialProduct (Fintype.card F) m) Filter.atTop (nhds L)) :
    (sqfreeCount F 1 : ℝ) ≠ (Fintype.card F : ℝ) ^ (1 ^ 2) * L := by
  have hq := two_le_card F
  have hq1 : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast (by omega : 1 < Fintype.card F)
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hle : L ≤ 1 - 1 / (Fintype.card F : ℝ) := by
    apply le_of_tendsto hL
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    exact prod_le_first _ hq1 m hm
  rw [sqfreeCount_one]
  intro h
  have h2 : (Fintype.card F : ℝ) * L ≤ (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) :=
    mul_le_mul_of_nonneg_left hle hq0.le
  have h3 : (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) = (Fintype.card F : ℝ) - 1 := by
    field_simp
  have h4 : (Fintype.card F : ℝ) ^ (1 ^ 2) = (Fintype.card F : ℝ) := by norm_num
  rw [h4] at h
  linarith

end Main

section Negation

/-- In the two-element ring `ZMod 2` the only non-zero element is its own inverse. -/
theorem zmod_two_mul_inv (a : ZMod 2) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  have ha : a = 1 := by
    revert a
    decide
  subst ha
  rw [ZMod.mul_inv_eq_gcd]
  decide

/-- The field with two elements: Mathlib's commutative ring and inversion on `ZMod 2`. -/
instance instFieldZModTwo : Field (ZMod 2) where
  mul_inv_cancel := zmod_two_mul_inv
  inv_zero := ZMod.inv_zero 2
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- The source's identity with the product over `1 ≤ i ≤ n`, for all finite fields and all
`n ≥ 1`. -/
def ClaimedClosedForm : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ), 1 ≤ n →
    (sqfreeCount F n : ℚ) = formula (Fintype.card F) n n

/-- The source's identity with the infinite product, for all finite fields and all `n ≥ 1`:
the partial products converge and the count is `q ^ (n ^ 2)` times their limit. -/
def ClaimedClosedFormInfinite : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ), 1 ≤ n → ∃ L : ℝ,
    Filter.Tendsto (fun m => partialProduct (Fintype.card F) m) Filter.atTop (nhds L) ∧
      (sqfreeCount F n : ℝ) = (Fintype.card F : ℝ) ^ (n ^ 2) * L

theorem conjecture_false : ¬ ClaimedClosedForm := fun h =>
  formula_fails (ZMod 2) 1 (le_refl 1) (h (ZMod 2) 1 (le_refl 1))

theorem conjecture_false_infinite : ¬ ClaimedClosedFormInfinite := fun h => by
  obtain ⟨L, hL, hEq⟩ := h (ZMod 2) 1 (le_refl 1)
  exact infinite_product_fails_at_one (ZMod 2) L hL hEq

end Negation

#print axioms squarefree_charpoly_one
#print axioms sqfreeCount_one
#print axioms formula_not_natural
#print axioms truncated_formula_fails_at_one
#print axioms formula_fails
#print axioms shifted_formula_fails
#print axioms infinite_product_fails_at_one
#print axioms conjecture_false
#print axioms conjecture_false_infinite

end Conjecture1854
