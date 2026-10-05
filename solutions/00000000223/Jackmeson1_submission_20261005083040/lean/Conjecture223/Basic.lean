import Mathlib

/-!
# Conjecture 00000000223: the density clause for Euclid numbers fails

Conjecture text (last clause): "for a fixed prime q, the density of n with q dividing E_n is an
explicit value of q^{-2} type", where `E_n = p_n# + 1` is one plus the product of the first `n`
primes.

Mathlib's `primorial n` is the product of the primes `<= n`, not of the first `n` primes, so we
define `p_n#` directly as `prod_{i < n} nth Nat.Prime i` (`nth Nat.Prime 0 = 2` is `p_1`).
We use natural density on `ℕ` (`0 ∈ ℕ`; including or excluding `n = 0` does not change any
density).

Euclid's argument: if `q = p_{r+1}` then `q ∣ p_n#` for every `n > r`, hence `q ∤ E_n`. So
`{n | q ∣ E_n} ⊆ [0, r]` is finite and its natural density is `0` for every prime `q`.
This refutes every reading under which the claimed value is nonzero for some prime `q`, in
particular `c * q^{-2}` with `c ≠ 0`, and `q^2 * density(q) → c ≠ 0` as `q → ∞`.
The other clauses (least prime factors, log-scale equidistribution) are not addressed.
-/

open Filter Topology
open scoped Classical

namespace C223

/-- `p_n#`: the product of the first `n` primes `p_1 = 2, ..., p_n`. -/
noncomputable def primorialFirst (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

/-- The Euclid number `E_n = p_n# + 1`. -/
noncomputable def euclid (n : ℕ) : ℕ := primorialFirst n + 1

/-- The set of indices `n` with `q ∣ E_n`. -/
def divSet (q : ℕ) : Set ℕ := {n | q ∣ euclid n}

/-- Natural density: `#(S ∩ [0, N)) / N → d`. -/
def HasNatDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ((Finset.range N).filter (· ∈ S)).card / (N : ℝ)) atTop (𝓝 d)

/-- Euclid: the `(r+1)`-st prime `nth Nat.Prime r` never divides `E_n` once `n > r`. -/
theorem not_dvd_euclid {r n : ℕ} (hn : r < n) : ¬ Nat.nth Nat.Prime r ∣ euclid n := by
  intro h
  have hp : (Nat.nth Nat.Prime r).Prime := Nat.prime_nth_prime r
  have hprod : Nat.nth Nat.Prime r ∣ primorialFirst n :=
    Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hn)
  have h1 : Nat.nth Nat.Prime r ∣ 1 := (Nat.dvd_add_right hprod).mp h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-- For a prime `q`, the set `{n | q ∣ E_n}` is contained in `[0, r]` where `q = nth Prime r`. -/
theorem divSet_subset {q : ℕ} (hq : q.Prime) :
    divSet q ⊆ {n | n ≤ Nat.count Nat.Prime q} := by
  intro n hn
  have hqr : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq
  by_contra hlt
  have hlt' : Nat.count Nat.Prime q < n := Nat.lt_of_not_le hlt
  have hn' : q ∣ euclid n := hn
  rw [← hqr] at hn'
  exact not_dvd_euclid hlt' hn'

/-- A set contained in `[0, R]` has natural density `0`. -/
theorem hasNatDensity_zero_of_subset {S : Set ℕ} {R : ℕ} (hS : S ⊆ {n | n ≤ R}) :
    HasNatDensity S 0 := by
  have hcard : ∀ N : ℕ, ((Finset.range N).filter (· ∈ S)).card ≤ R + 1 := by
    intro N
    calc ((Finset.range N).filter (· ∈ S)).card ≤ (Finset.range (R + 1)).card := by
          apply Finset.card_le_card
          intro n hn
          simp only [Finset.mem_filter] at hn
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hS hn.2))
      _ = R + 1 := Finset.card_range _
  have hlim : Tendsto (fun N : ℕ => ((R : ℝ) + 1) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine squeeze_zero (fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (fun N => ?_) hlim
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hcard N

/-- For every prime `q`, the natural density of `{n | q ∣ E_n}` is `0`. -/
theorem hasNatDensity_divSet (q : ℕ) (hq : q.Prime) : HasNatDensity (divSet q) 0 :=
  hasNatDensity_zero_of_subset (divSet_subset hq)

/-- Natural densities are unique, so the only possible density value is `0`. -/
theorem density_eq_zero {q : ℕ} (hq : q.Prime) {d : ℝ} (h : HasNatDensity (divSet q) d) :
    d = 0 :=
  tendsto_nhds_unique h (hasNatDensity_divSet q hq)

/-- Main theorem: there is no prime `q` for which `{n | q ∣ E_n}` has a nonzero natural
density. Hence every reading of "an explicit value of `q^{-2}` type" that assigns a nonzero
value to at least one prime `q` is false. -/
theorem no_nonzero_density : ¬ ∃ q : ℕ, q.Prime ∧ ∃ d : ℝ, d ≠ 0 ∧ HasNatDensity (divSet q) d := by
  rintro ⟨q, hq, d, hd, h⟩
  exact hd (density_eq_zero hq h)

/-- Reading (i), exact form: the density equals `c / q^2` for every prime `q`, with `c ≠ 0`. -/
theorem not_exact_form :
    ¬ ∃ c : ℝ, c ≠ 0 ∧ ∀ q : ℕ, q.Prime → HasNatDensity (divSet q) (c / (q : ℝ) ^ 2) := by
  rintro ⟨c, hc, h⟩
  have h2 := density_eq_zero Nat.prime_two (h 2 Nat.prime_two)
  norm_num at h2
  exact hc h2

/-- Reading (ii), asymptotic form: the densities `d(q)` exist and `q^2 d(q) → c ≠ 0` along the
primes `q = nth Prime r`, `r → ∞` (this includes `d(q) ~ c q^{-2}`). -/
theorem not_asymptotic_form :
    ¬ ∃ (d : ℕ → ℝ) (c : ℝ), c ≠ 0 ∧ (∀ q : ℕ, q.Prime → HasNatDensity (divSet q) (d q)) ∧
      Tendsto (fun r : ℕ => ((Nat.nth Nat.Prime r : ℕ) : ℝ) ^ 2 * d (Nat.nth Nat.Prime r))
        atTop (𝓝 c) := by
  rintro ⟨d, c, hc, hd, hlim⟩
  have h0 : (fun r : ℕ => ((Nat.nth Nat.Prime r : ℕ) : ℝ) ^ 2 * d (Nat.nth Nat.Prime r)) =
      fun _ => 0 := by
    funext r
    rw [density_eq_zero (Nat.prime_nth_prime r) (hd _ (Nat.prime_nth_prime r)), mul_zero]
  rw [h0] at hlim
  exact hc (tendsto_nhds_unique hlim tendsto_const_nhds)

/-- Capstone: the density clause of Conjecture 00000000223 fails under the exact-form reading
(i), the asymptotic reading (ii), and every reading that needs a nonzero value for some `q`;
the true density is `0` for every prime `q`. -/
theorem conjecture_223_density_clause_false :
    (∀ q : ℕ, q.Prime → HasNatDensity (divSet q) 0) ∧
    (¬ ∃ q : ℕ, q.Prime ∧ ∃ d : ℝ, d ≠ 0 ∧ HasNatDensity (divSet q) d) ∧
    (¬ ∃ c : ℝ, c ≠ 0 ∧ ∀ q : ℕ, q.Prime → HasNatDensity (divSet q) (c / (q : ℝ) ^ 2)) ∧
    (¬ ∃ (d : ℕ → ℝ) (c : ℝ), c ≠ 0 ∧ (∀ q : ℕ, q.Prime → HasNatDensity (divSet q) (d q)) ∧
      Tendsto (fun r : ℕ => ((Nat.nth Nat.Prime r : ℕ) : ℝ) ^ 2 * d (Nat.nth Nat.Prime r))
        atTop (𝓝 c)) :=
  ⟨hasNatDensity_divSet, no_nonzero_density, not_exact_form, not_asymptotic_form⟩

end C223
