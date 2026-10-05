import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Disproof of conjecture 00000007662

The functional equation is interpreted in a formal power series ring.  Its
constant-one denominator is inverted by `PowerSeries.invOfUnit`.  The coefficients
are constructed over every commutative ring, including `Polynomial ℤ`; evaluation
at 2 gives exactly the integer coefficients studied below.  Prime always means
an ordinary positive natural prime, embedded in the integers.
-/

noncomputable section

namespace Conjecture7662

open scoped BigOperators
open Finset PowerSeries

/-- Coefficient convolution, with its finite range visible. -/
noncomputable def convolution {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) : R :=
  ∑ i : Fin (n + 1), a i * a (n - i)

/-- The triangular recursion extracted from the stated functional equation. -/
noncomputable def coefficient {R : Type*} [CommRing R] (q : R) : ℕ → R
  | 0 => 1
  | n + 1 => (∑ i : Fin (n + 1), coefficient q i * coefficient q (n - i)) -
      q ^ (n + 1) * coefficient q n
termination_by n => n


@[simp] theorem coefficient_zero {R : Type*} [CommRing R] (q : R) :
    coefficient q 0 = 1 := by rw [coefficient]

theorem coefficient_succ {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    coefficient q (n + 1) = convolution (coefficient q) n -
      q ^ (n + 1) * coefficient q n := by rw [coefficient]; rfl

theorem convolution_range {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) :
    convolution a n = ∑ i ∈ range (n + 1), a i * a (n - i) := by
  simpa only [convolution] using
    (Fin.sum_univ_eq_sum_range (fun i => a i * a (n - i)) (n + 1))

/-- The actual formal power series, not merely a recurrence predicate. -/
def series {R : Type*} [CommRing R] (q : R) : PowerSeries R :=
  PowerSeries.mk (coefficient q)

@[simp] theorem coeff_series {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    PowerSeries.coeff R n (series q) = coefficient q n := by
  simp [series]

/-- The equation exactly as printed, with division by the constant-one unit. -/
def FunctionalEquation {R : Type*} [CommRing R] (q : R) (F : PowerSeries R) : Prop :=
  F = (1 - PowerSeries.C R q * PowerSeries.X * PowerSeries.rescale q F) *
    PowerSeries.invOfUnit (1 - PowerSeries.X * F) 1

theorem denominator_inverse {R : Type*} [CommRing R] (F : PowerSeries R) :
    (1 - PowerSeries.X * F) * PowerSeries.invOfUnit (1 - PowerSeries.X * F) 1 = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp

theorem functionalEquation_iff {R : Type*} [CommRing R] (q : R) (F : PowerSeries R) :
    FunctionalEquation q F ↔
      F = 1 + PowerSeries.X * (F * F - PowerSeries.C R q * PowerSeries.rescale q F) := by
  have hi := denominator_inverse F
  have hic : PowerSeries.invOfUnit (1 - PowerSeries.X * F) 1 *
      (1 - PowerSeries.X * F) = 1 := by rw [mul_comm]; exact hi
  have hc : FunctionalEquation q F ↔
      F * (1 - PowerSeries.X * F) =
        1 - PowerSeries.C R q * PowerSeries.X * PowerSeries.rescale q F := by
    constructor
    · intro h
      rw [FunctionalEquation] at h
      calc
        F * (1 - PowerSeries.X * F) =
            ((1 - PowerSeries.C R q * PowerSeries.X * PowerSeries.rescale q F) *
              PowerSeries.invOfUnit (1 - PowerSeries.X * F) 1) *
                (1 - PowerSeries.X * F) := congrArg (fun Z => Z * (1 - PowerSeries.X * F)) h
        _ = _ := by rw [mul_assoc, hic, mul_one]
    · intro h
      unfold FunctionalEquation
      calc
        F = F * ((1 - PowerSeries.X * F) *
            PowerSeries.invOfUnit (1 - PowerSeries.X * F) 1) := by rw [hi, mul_one]
        _ = _ := by rw [← mul_assoc, h]
  rw [hc]
  constructor <;> intro h <;> linear_combination h

theorem coeff_square {R : Type*} [CommRing R] (F : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff R n (F * F) = convolution (fun k => PowerSeries.coeff R k F) n := by
  rw [PowerSeries.coeff_mul, convolution_range]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff R i F * PowerSeries.coeff R j F) n

theorem functionalEquation_coefficients {R : Type*} [CommRing R]
    (q : R) (F : PowerSeries R) :
    FunctionalEquation q F ↔
      PowerSeries.coeff R 0 F = 1 ∧ ∀ n,
      PowerSeries.coeff R (n + 1) F =
        convolution (fun k => PowerSeries.coeff R k F) n -
          q ^ (n + 1) * PowerSeries.coeff R n F := by
  rw [functionalEquation_iff]
  constructor
  · intro h
    constructor
    · have h0 := congrArg (PowerSeries.coeff R 0) h
      simpa using h0
    · intro n
      have hn := congrArg (PowerSeries.coeff R (n + 1)) h
      simpa [PowerSeries.coeff_succ_X_mul, coeff_square,
        PowerSeries.coeff_rescale, pow_succ, mul_assoc, mul_left_comm] using hn
  · rintro ⟨h0, hs⟩
    ext n
    cases n with
    | zero => simpa using h0
    | succ n =>
      simpa [PowerSeries.coeff_succ_X_mul, coeff_square,
        PowerSeries.coeff_rescale, pow_succ, mul_assoc, mul_left_comm] using hs n

theorem series_satisfies {R : Type*} [CommRing R] (q : R) :
    FunctionalEquation q (series q) := by
  rw [functionalEquation_coefficients]
  simp only [coeff_series, coefficient_zero, true_and]
  exact coefficient_succ q

theorem coefficients_unique {R : Type*} [CommRing R] (q : R) (a : ℕ → R)
    (h0 : a 0 = 1)
    (hs : ∀ n, a (n + 1) = convolution a n - q ^ (n + 1) * a n) :
    a = coefficient q := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using h0
    | succ n =>
      rw [hs, coefficient_succ, ih n (by omega)]
      congr 1
      unfold convolution
      apply Finset.sum_congr rfl
      intro i _
      rw [ih i (by omega), ih (n - i) (by omega)]

theorem exists_unique_series {R : Type*} [CommRing R] (q : R) :
    ∃! F : PowerSeries R, FunctionalEquation q F := by
  refine ⟨series q, series_satisfies q, ?_⟩
  intro F hF
  obtain ⟨h0, hs⟩ := (functionalEquation_coefficients q F).mp hF
  have he := coefficients_unique q (fun n => PowerSeries.coeff R n F) h0 hs
  ext n
  simpa using congrFun he n

theorem coefficient_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : R) (n : ℕ) :
    f (coefficient q n) = coefficient (f q) n := by
  have h := coefficients_unique (f q) (fun k => f (coefficient q k))
    (by simp) (fun k => by
      dsimp only
      rw [coefficient_succ]
      simp [convolution, map_sum])
  exact congrFun h n

/-- The polynomial family C_n(Q) specified by the original equation. -/
def catalanPolynomial (n : ℕ) : Polynomial ℤ := coefficient Polynomial.X n

/-- Evaluation of that family at 2 is the integer sequence under study. -/
theorem polynomial_evaluation (n : ℕ) :
    Polynomial.eval 2 (catalanPolynomial n) = coefficient (2 : ℤ) n := by
  simpa [catalanPolynomial] using
    coefficient_map (Polynomial.evalRingHom (2 : ℤ)) Polynomial.X n

/-- An auxiliary signed transform. Its positivity is proved, not assumed. -/
noncomputable def b : ℕ → ℤ
  | 0 => 1
  | n + 1 => 2 ^ (n + 1) * b n - ∑ i : Fin (n + 1), b i * b (n - i)
termination_by n => n

@[simp] theorem b_zero : b 0 = 1 := by rw [b]

theorem b_succ (n : ℕ) : b (n + 1) = 2 ^ (n + 1) * b n - convolution b n := by
  rw [b]; rfl

/-- Growth bounds imply the product bound needed for the convolution. -/
theorem product_bound_from_growth (a : ℕ → ℤ) (n : ℕ)
    (h0 : a 0 = 1) (hnon : ∀ k ≤ n, 0 ≤ a k)
    (hlow : ∀ k < n, 2 ^ k * a k ≤ a (k + 1))
    (hupp : ∀ k < n, a (k + 1) ≤ 2 ^ (k + 1) * a k) :
    ∀ i j, i + j ≤ n → a i * a j ≤ a (i + j) := by
  intro i
  induction i with
  | zero => intro j _; simp [h0]
  | succ i ih =>
    intro j hij
    by_cases hj : j = 0
    · subst j; simp [h0]
    have hi : i < n := by omega
    have hij' : i + j < n := by omega
    have hn0 := hnon (i + j) (by omega)
    calc
      a (i + 1) * a j ≤ (2 ^ (i + 1) * a i) * a j :=
        mul_le_mul_of_nonneg_right (hupp i hi) (hnon j (by omega))
      _ = 2 ^ (i + 1) * (a i * a j) := by ring
      _ ≤ 2 ^ (i + 1) * a (i + j) :=
        mul_le_mul_of_nonneg_left (ih j (by omega)) (by positivity)
      _ ≤ 2 ^ (i + j) * a (i + j) := by
        apply mul_le_mul_of_nonneg_right _ hn0
        exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega)
      _ ≤ a (i + j + 1) := hlow (i + j) hij'
      _ = a (i + 1 + j) := by congr 1; omega

theorem index_bound (n : ℕ) : (n + 1 : ℤ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    push_cast
    linarith

/-- Simultaneous nonnegativity and two-sided growth, valid at every index. -/
theorem b_growth : ∀ n, 1 ≤ b n ∧
    2 ^ n * b n ≤ b (n + 1) ∧ b (n + 1) ≤ 2 ^ (n + 1) * b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hb : 1 ≤ b n := by
      cases n with
      | zero => simp
      | succ k =>
        have hk := ih k (by omega)
        have hp : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        nlinarith [hk.2.1]
    have hnon : ∀ k ≤ n, 0 ≤ b k := by
      intro k hk
      rcases lt_or_eq_of_le hk with hlt | rfl
      · linarith [(ih k hlt).1]
      · linarith
    have hprod := product_bound_from_growth b n b_zero hnon
      (fun k hk => (ih k hk).2.1) (fun k hk => (ih k hk).2.2)
    have hconv0 : 0 ≤ convolution b n := by
      unfold convolution
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (hnon i (by omega)) (hnon (n - i) (by omega))
    have hconv : convolution b n ≤ (n + 1 : ℤ) * b n := by
      unfold convolution
      calc
        _ ≤ ∑ _i : Fin (n + 1), b n := by
          apply Finset.sum_le_sum
          intro i _
          simpa only [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)] using
            hprod i (n - i) (by omega)
        _ = _ := by simp
    have hpow := mul_le_mul_of_nonneg_right (index_bound n) (hnon n le_rfl)
    refine ⟨hb, ?_, ?_⟩ <;> rw [b_succ, pow_succ] <;> nlinarith

/-- The auxiliary sequence is exactly the alternating-sign transform. -/
theorem coefficient_signed (n : ℕ) : coefficient (2 : ℤ) n = (-1) ^ n * b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hc : convolution (coefficient (2 : ℤ)) n = (-1) ^ n * convolution b n := by
        unfold convolution
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [ih i (by omega), ih (n - i) (by omega)]
        have he : (i : ℕ) + (n - i) = n := Nat.add_sub_of_le (by omega)
        calc
          (-1 : ℤ) ^ (i : ℕ) * b i * ((-1) ^ (n - i) * b (n - i)) =
              ((-1) ^ (i : ℕ) * (-1) ^ (n - i)) * (b i * b (n - i)) := by ring
          _ = _ := by rw [← pow_add, he]
      rw [coefficient_succ, hc, ih n (by omega), b_succ, pow_succ]
      ring

/-- An odd convolution has two equal halves, by reflection. -/
theorem convolution_odd (a : ℕ → ℤ) (k : ℕ) :
    convolution a (2 * k + 1) =
      2 * ∑ i ∈ range (k + 1), a i * a (2 * k + 1 - i) := by
  rw [convolution_range]
  have hlen : 2 * k + 1 + 1 = (k + 1) + (k + 1) := by omega
  rw [hlen, Finset.sum_range_add]
  have hr : (∑ i ∈ range (k + 1), a (k + 1 + i) * a (2 * k + 1 - (k + 1 + i))) =
      ∑ i ∈ range (k + 1), a i * a (2 * k + 1 - i) := by
    rw [← Finset.sum_range_reflect (fun i => a i * a (2 * k + 1 - i)) (k + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have he1 : 2 * k + 1 - (k + 1 + i) = k + 1 - 1 - i := by omega
    have he2 : 2 * k + 1 - (k + 1 - 1 - i) = k + 1 + i := by omega
    rw [he1, he2, mul_comm]
  rw [hr]
  ring

/-- Every positive even-index coefficient is an even integer. -/
theorem even_index_coefficient (k : ℕ) : Even (coefficient (2 : ℤ) (2 * k + 2)) := by
  have he : 2 * k + 2 = (2 * k + 1) + 1 := by omega
  rw [he, coefficient_succ, convolution_odd, pow_succ]
  refine ⟨(∑ i ∈ range (k + 1), coefficient (2 : ℤ) i *
      coefficient (2 : ℤ) (2 * k + 1 - i)) -
        2 ^ (2 * k + 1) * coefficient (2 : ℤ) (2 * k + 1), ?_⟩
  ring

theorem odd_index_negative {n : ℕ} (hn : Odd n) : coefficient (2 : ℤ) n < 0 := by
  rw [coefficient_signed, hn.neg_one_pow]
  have hb := (b_growth n).1
  linarith

theorem even_index_positive {n : ℕ} (hn : Even n) : 1 ≤ coefficient (2 : ℤ) n := by
  rw [coefficient_signed, hn.neg_one_pow, one_mul]
  exact (b_growth n).1

theorem b_large {n : ℕ} (hn : 3 ≤ n) : 4 ≤ b n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hg := b_growth (2 + k)
  have hp : (4 : ℤ) ≤ 2 ^ (2 + k) := by
    calc
      (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 + k) := pow_le_pow_right₀ (by norm_num) (by omega)
  have he : 3 + k = (2 + k) + 1 := by omega
  rw [he]
  nlinarith [hg.1, hg.2.1]

/-- Positive primality, without replacing negative integers by their absolute values. -/
def PositivePrime (z : ℤ) : Prop := ∃ p : ℕ, p.Prime ∧ z = (p : ℤ)

@[simp] theorem coefficient_one : coefficient (2 : ℤ) 1 = -1 := by
  norm_num [coefficient_succ, convolution, Fin.sum_univ_succ]

@[simp] theorem coefficient_two : coefficient (2 : ℤ) 2 = 2 := by
  norm_num [coefficient_succ, convolution, Fin.sum_univ_succ]

/-- Exact classification of all prime values of the specified sequence. -/
theorem positivePrime_iff (n : ℕ) : PositivePrime (coefficient (2 : ℤ) n) ↔ n = 2 := by
  constructor
  · rintro ⟨p, hp, he⟩
    have hpos : 0 < coefficient (2 : ℤ) n := by
      rw [he]
      exact_mod_cast hp.pos
    have hn : Even n := by
      rcases Nat.even_or_odd n with hn | hn
      · exact hn
      · have := odd_index_negative hn; linarith
    have hn0 : n ≠ 0 := by
      intro hz
      subst n
      have htwo := hp.two_le
      norm_num at he
      omega
    obtain ⟨k, hk⟩ := hn
    have hk0 : 0 < k := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hform : n = 2 * j + 2 := by omega
    have heven := even_index_coefficient j
    rw [← hform, he] at heven
    have hp2 : p = 2 := hp.even_iff.mp (by exact_mod_cast heven)
    subst p
    by_contra hne
    have hlarge : 3 ≤ n := by omega
    have hbn := b_large hlarge
    rw [coefficient_signed, (show Even n from ⟨j + 1, hk⟩).neg_one_pow, one_mul] at he
    norm_num at he
    linarith
  · rintro rfl
    exact ⟨2, Nat.prime_two, coefficient_two⟩

/-- The set of prime indices is exactly the singleton {2}. -/
theorem prime_indices_eq_singleton :
    {n : ℕ | PositivePrime (coefficient (2 : ℤ) n)} = {2} := by
  ext n
  simp [positivePrime_iff]

/-- Negation of the conjecture's explicit necessary infinitude clause. -/
theorem not_infinite_prime_indices :
    ¬ Set.Infinite {n : ℕ | PositivePrime (coefficient (2 : ℤ) n)} := by
  rw [prime_indices_eq_singleton]
  exact Set.finite_singleton 2 |>.not_infinite

/-- The exact same classification for coefficients of any actual solution. -/
theorem solution_prime_iff (F : PowerSeries ℤ) (hF : FunctionalEquation (2 : ℤ) F) (n : ℕ) :
    PositivePrime (PowerSeries.coeff ℤ n F) ↔ n = 2 := by
  have huni := (exists_unique_series (2 : ℤ)).unique hF (series_satisfies (2 : ℤ))
  rw [huni, coeff_series]
  exact positivePrime_iff n

/-- Non-vacuous disproof directly quantified over the specified formal series. -/
theorem formal_series_disproof :
    (∃! F : PowerSeries ℤ, FunctionalEquation (2 : ℤ) F) ∧
    ∀ F : PowerSeries ℤ, FunctionalEquation (2 : ℤ) F →
      ¬ Set.Infinite {n : ℕ | PositivePrime (PowerSeries.coeff ℤ n F)} := by
  refine ⟨exists_unique_series (2 : ℤ), ?_⟩
  intro F hF
  have hs : {n : ℕ | PositivePrime (PowerSeries.coeff ℤ n F)} = {2} := by
    ext n
    simp [solution_prime_iff F hF]
  rw [hs]
  exact Set.finite_singleton 2 |>.not_infinite

/-- Classification stated directly for evaluation of C_n(Q) at q = 2. -/
theorem polynomial_prime_iff (n : ℕ) :
    PositivePrime (Polynomial.eval 2 (catalanPolynomial n)) ↔ n = 2 := by
  rw [polynomial_evaluation]
  exact positivePrime_iff n

/-- The source counting function, with real cutoff and natural indices. -/
def primeCounting (x : ℝ) : ℕ :=
  Set.ncard {n : ℕ | (n : ℝ) ≤ x ∧ PositivePrime (Polynomial.eval 2 (catalanPolynomial n))}

/-- The counting function is exactly zero before 2, and one from 2 onward. -/
theorem primeCounting_eq (x : ℝ) : primeCounting x = if 2 ≤ x then 1 else 0 := by
  have hs : {n : ℕ | (n : ℝ) ≤ x ∧ PositivePrime (Polynomial.eval 2 (catalanPolynomial n))} =
      if 2 ≤ x then {2} else ∅ := by
    ext n
    by_cases hx : 2 ≤ x
    · simp only [polynomial_prime_iff, if_pos hx, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · exact And.right
      · rintro rfl
        exact ⟨by exact_mod_cast hx, rfl⟩
    · simp only [polynomial_prime_iff, if_neg hx, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hn he
      subst n
      norm_num at hn
      exact hx hn
  unfold primeCounting
  rw [hs]
  split <;> simp

/-- Full disproof of the explicit infinitude assertion using the polynomial family. -/
theorem conjecture_00000007662_disproved :
    ¬ Set.Infinite {n : ℕ | PositivePrime (Polynomial.eval 2 (catalanPolynomial n))} := by
  simpa only [polynomial_evaluation] using not_infinite_prime_indices

end Conjecture7662
