import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic

/-!
# Conjecture 00000000106

A proof of the source's largest-prime-factor assertion. All powers in the
statement have real bases and real exponents. `largestPrimeFactor` agrees with
the actual largest prime divisor at every input at least two; its value at
zero or one is zero and is irrelevant to `Good`.
-/

namespace Conjecture106

open scoped BigOperators

/-- The maximum of the finite set of natural prime divisors, with value zero
at zero and one. The specification below supplies its positive-input meaning. -/
noncomputable def largestPrimeFactor (m : ℕ) : ℕ := m.primeFactors.sup id

/-- Agreement with the actual largest prime divisor on the intended domain. -/
theorem largestPrimeFactor_spec {m : ℕ} (hm : 2 ≤ m) :
    (largestPrimeFactor m).Prime ∧ largestPrimeFactor m ∣ m ∧
      ∀ q : ℕ, q.Prime → q ∣ m → q ≤ largestPrimeFactor m := by
  have hne : m.primeFactors.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    have hsmall := Nat.primeFactors_eq_empty.mp hempty
    omega
  have hmem : largestPrimeFactor m ∈ m.primeFactors := by
    simpa [largestPrimeFactor] using
      (Finset.sup_mem_of_nonempty (f := id) hne)
  have hfactor := Nat.mem_primeFactors.mp hmem
  refine ⟨hfactor.1, hfactor.2.1, ?_⟩
  intro q hq hqm
  exact Finset.le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hq, hqm, by omega⟩)

/-- Exact semantic bridge from an above-threshold prime divisor to the maximum. -/
theorem threshold_iff_prime_divisor {m : ℕ} (hm : 2 ≤ m) (t : ℝ) :
    t < (largestPrimeFactor m : ℝ) ↔
      ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ t < (p : ℝ) := by
  obtain ⟨hprime, hdvd, hmax⟩ := largestPrimeFactor_spec hm
  constructor
  · intro h
    exact ⟨largestPrimeFactor m, hprime, hdvd, h⟩
  · rintro ⟨p, hp, hpm, hpt⟩
    exact lt_of_lt_of_le hpt (by exact_mod_cast hmax p hp hpm)

/-- All offsets use the same integer and the same positive real exponent. -/
def Good (k : ℕ) (c : ℝ) (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ i : ℕ, 1 ≤ i → i ≤ k →
    (n : ℝ) ^ c < (largestPrimeFactor (n + i) : ℝ)

/-- The full bilingual source assertion, with its implicit standard domains explicit. -/
def Statement : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ c : ℝ, 0 < c ∧ {n : ℕ | Good k c n}.Infinite

/-- Successive dyadic intervals supply distinct primes of controlled size. -/
theorem dyadic_primes {t : ℕ} (ht : 0 < t) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      ∀ i : ℕ, (p i).Prime ∧ 2 ^ i * t < p i ∧ p i ≤ 2 ^ (i + 1) * t := by
  have hex (i : ℕ) := Nat.exists_prime_lt_and_le_two_mul (2 ^ i * t) (by positivity)
  choose p hp using hex
  have hupper (i : ℕ) : p i ≤ 2 ^ (i + 1) * t := by
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (hp i).2.2
  refine ⟨p, ?_, fun i => ⟨(hp i).1, (hp i).2.1, hupper i⟩⟩
  intro i j hij
  calc
    p i ≤ 2 ^ (i + 1) * t := hupper i
    _ ≤ 2 ^ j * t := Nat.mul_le_mul_right t (Nat.pow_le_pow_right (by decide) (by omega))
    _ < p j := (hp j).2.1

/-- A bounded simultaneous CRT representative whose shifts have the chosen divisors. -/
theorem bounded_representative {k t : ℕ} (hk : 0 < k) (ht : k < t)
    (htpow : 2 ^ k ≤ t) :
    ∃ n : ℕ, t ≤ n ∧ n < t ^ (2 * k) ∧
      ∀ i : ℕ, i < k → ∃ p : ℕ, p.Prime ∧ p ∣ n + (i + 1) ∧ t < p := by
  obtain ⟨p, hmono, hp⟩ := dyadic_primes (by omega : 0 < t)
  have hpmin (i : ℕ) : t < p i := by
    have hpow : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by decide)
    exact lt_of_le_of_lt (by simpa using Nat.mul_le_mul_right t hpow) (hp i).2.1
  have hpos : ∀ i ∈ Finset.range k, p i ≠ 0 := fun i _ => (hp i).1.ne_zero
  have hcop : Set.Pairwise (Finset.range k) (fun i j => Nat.Coprime (p i) (p j)) := by
    intro i _ j _ hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (hmono.injective.ne hij)
  let a : ℕ → ℕ := fun i => p i - (i + 1)
  let r := Nat.chineseRemainderOfFinset a p (Finset.range k) hpos hcop
  have hdiv (i : ℕ) (hi : i < k) : p i ∣ (r : ℕ) + (i + 1) := by
    have hile : i + 1 ≤ p i := by have := hpmin i; omega
    have heq := (r.property i (Finset.mem_range.mpr hi)).add_right (i + 1)
    have hmod : (r : ℕ) + (i + 1) ≡ p i [MOD p i] := by
      simpa only [a, Nat.sub_add_cancel hile] using heq
    exact Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)))
  have hlower : t ≤ (r : ℕ) := by
    have hdiv0 := hdiv 0 hk
    have hle := Nat.le_of_dvd (by omega : 0 < (r : ℕ) + (0 + 1)) hdiv0
    have hmin := hpmin 0
    omega
  have hprod : (∏ i ∈ Finset.range k, p i) ≤ t ^ (2 * k) := by
    calc
      (∏ i ∈ Finset.range k, p i) ≤ ∏ _i ∈ Finset.range k, t ^ 2 := by
        apply Finset.prod_le_prod (fun i _ => Nat.zero_le (p i))
        intro i hi
        have hik : i + 1 ≤ k := by have := Finset.mem_range.mp hi; omega
        calc
          p i ≤ 2 ^ (i + 1) * t := (hp i).2.2
          _ ≤ 2 ^ k * t := Nat.mul_le_mul_right t (Nat.pow_le_pow_right (by decide) hik)
          _ ≤ t * t := Nat.mul_le_mul_right t htpow
          _ = t ^ 2 := (pow_two t).symm
      _ = t ^ (2 * k) := by simp [← pow_mul]
  refine ⟨r, hlower, lt_of_lt_of_le ?_ hprod, ?_⟩
  · exact Nat.chineseRemainderOfFinset_lt_prod a p hpos hcop
  · intro i hi
    exact ⟨p i, (hp i).1, hdiv i hi, hpmin i⟩

/-- The canonical predicate has witnesses beyond every prescribed bound. -/
theorem unbounded_good (k : ℕ) (hk : 2 ≤ k) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ Good k (((2 * k : ℕ) : ℝ)⁻¹) n := by
  let t := max (2 ^ k) (N + k + 3)
  have htk : k < t := lt_of_lt_of_le (by omega) (le_max_right _ _)
  have htN : N < t := lt_of_lt_of_le (by omega) (le_max_right _ _)
  have ht2 : 2 ≤ t := le_trans (by omega) (le_max_right _ _)
  obtain ⟨n, htn, hnupper, hdiv⟩ := bounded_representative (by omega) htk (le_max_left _ _)
  have hroot : (n : ℝ) ^ (((2 * k : ℕ) : ℝ)⁻¹) < (t : ℝ) := by
    apply (Real.rpow_inv_lt_iff_of_pos (by positivity) (by positivity) (by positivity)).mpr
    rw [Real.rpow_natCast]
    exact_mod_cast hnupper
  refine ⟨n, lt_of_lt_of_le htN htn, le_trans ht2 htn, ?_⟩
  intro i hi hik
  obtain ⟨p, hp, hpn, htp⟩ := hdiv (i - 1) (by omega)
  have hi_eq : i - 1 + 1 = i := by omega
  rw [hi_eq] at hpn
  apply (threshold_iff_prime_divisor (by omega : 2 ≤ n + i) _).mpr
  exact ⟨p, hp, hpn, lt_trans hroot (by exact_mod_cast htp)⟩

/-- Conjecture 00000000106, for every natural length k ≥ 2. -/
theorem conjecture : Statement := by
  intro k hk
  refine ⟨((2 * k : ℕ) : ℝ)⁻¹, by positivity, ?_⟩
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  obtain ⟨n, hnN, hgood⟩ := unbounded_good k hk N
  exact ⟨n, hgood, hnN⟩

end Conjecture106
