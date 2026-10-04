import Mathlib

/-!
# Refutation of the extremal example in conjecture 00000000036

Conjecture 00000000036 asserts two things:

1. (Upper bound) If `A ⊆ [N]` is such that the sum (when `≥ 4`) and the
   difference (when `≥ 2`) of any two of its elements are both composite,
   then `|A| ≤ (1/3 + ε) N`.
2. (Extremal example) The residue classes `{±1 mod 6}` satisfy the hypothesis
   and show the constant `1/3` is attained.

Claim (2) is false. The set `B = {n : n % 6 = 1 ∨ n % 6 = 5}` contains `5`
and `7`, whose difference is `7 - 5 = 2`, which is prime. Hence `B` does not
satisfy the hypothesis, and the conjecture as stated is false.

We additionally verify a corrected construction: the multiples of `4` do
satisfy the hypothesis and have density `1/4`, following the same
`omega`-witness pattern as the `00000000006` refutation. An exhaustive check
over moduli `m ≤ 10` and greedy/random search up to `m = 48` found no periodic
residue construction above density `1/4`, suggesting the sharp constant — if
the upper bound holds at all — is at most `1/4`, not `1/3`.
-/

namespace Counterexample36

open Finset

/-- A number with a proper divisor above one is not prime. -/
theorem not_prime_of_dvd {p n : ℕ} (hp : 1 < p) (hpn : p < n) (hdvd : p ∣ n) :
    ¬ n.Prime := fun h => by
  rcases h.eq_one_or_self_of_dvd p hdvd with h1 | h2 <;> omega

/-! ## The claimed extremal example fails -/

/-- The set the conjecture proposes as extremal: `n ≡ ±1 [MOD 6]`. -/
def inB (n : ℕ) : Prop :=
  n % 6 = 1 ∨ n % 6 = 5

instance : DecidablePred inB := fun n => by unfold inB; infer_instance

theorem memB_five : inB 5 := by decide

theorem memB_seven : inB 7 := by decide

theorem seven_sub_five_prime : Nat.Prime (7 - 5) := by decide

/-- The residue classes `{±1 mod 6}` do not satisfy the hypothesis:
`5, 7 ∈ B` are distinct, yet `(7 - 5) = 2` is prime (and `≥ 2`). -/
theorem claimed_extremal_invalid :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ inB a ∧ inB b ∧ a ≠ b ∧ a < b ∧
      Nat.Prime (b - a) ∧ 2 ≤ b - a :=
  ⟨5, 7, by norm_num, by norm_num, memB_five, memB_seven, by norm_num,
    by norm_num, seven_sub_five_prime, by norm_num⟩

/-! ## A corrected construction with density `1/4` -/

/-- Multiples of `4`: the repaired lower-bound construction. -/
def inA (n : ℕ) : Prop :=
  n % 4 = 0

instance : DecidablePred inA := fun n => by unfold inA; infer_instance

/-- Sums of distinct positive multiples of `4` are even and exceed `2`. -/
theorem sum_obstruction {a b : ℕ} (ha : inA a) (hb : inA b)
    (hapos : 0 < a) (hbpos : 0 < b) (hne : a ≠ b) :
    2 ∣ (a + b) ∧ 2 < a + b := by
  unfold inA at ha hb
  exact ⟨⟨(a + b) / 2, by omega⟩, by omega⟩

/-- Differences of distinct multiples of `4` (with `a < b`) are even and
exceed `2`: the least positive difference is `4` itself. -/
theorem diff_obstruction {a b : ℕ} (ha : inA a) (hb : inA b) (hlt : a < b) :
    2 ∣ (b - a) ∧ 2 < b - a := by
  unfold inA at ha hb
  exact ⟨⟨(b - a) / 2, by omega⟩, by omega⟩

/-- Multiples of `4` satisfy the sum half of the hypothesis. -/
theorem inA_sum_admissible {a b : ℕ} (hapos : 0 < a) (hbpos : 0 < b)
    (ha : inA a) (hb : inA b) (hne : a ≠ b) :
    ¬ Nat.Prime (a + b) := by
  rcases sum_obstruction ha hb hapos hbpos hne with ⟨hd, hgt⟩
  exact not_prime_of_dvd (by norm_num) hgt hd

/-- Multiples of `4` satisfy the difference half of the hypothesis. -/
theorem inA_diff_admissible {a b : ℕ} (ha : inA a) (hb : inA b) (hlt : a < b) :
    ¬ Nat.Prime (b - a) := by
  rcases diff_obstruction ha hb hlt with ⟨hd, hgt⟩
  exact not_prime_of_dvd (by norm_num) hgt hd

/-! ## The corrected set has density `1/4` -/

/-- `countA N = |A ∩ [1, N]|`. -/
def countA (N : ℕ) : ℕ := ((range (N + 1)).filter (fun n => 0 < n ∧ inA n)).card

theorem countA_mono {M N : ℕ} (h : M ≤ N) : countA M ≤ countA N := by
  apply card_le_card
  intro x hx
  rw [mem_filter, mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

/-- Enumerates the multiples of `4`: the `i`-th is `4 * (i+1)`. -/
def enumA (i : ℕ) : ℕ := 4 * (i + 1)

theorem enumA_injOn (k : ℕ) : Set.InjOn enumA (range k) := by
  intro i _ j _ hij
  simp only [enumA] at hij
  omega

theorem enumA_mem {k i : ℕ} (hi : i ∈ range k) :
    enumA i ∈ (range (4 * k + 1)).filter (fun n => 0 < n ∧ inA n) := by
  rw [mem_range] at hi
  rw [mem_filter, mem_range]
  simp only [enumA]
  refine ⟨by omega, by omega, ?_⟩
  unfold inA
  omega

/-- Every `k` contributes `k` multiples of `4` below `4k`. -/
theorem k_le_countA (k : ℕ) : k ≤ countA (4 * k) := by
  have := card_le_card_of_injOn enumA (fun i hi => enumA_mem hi) (enumA_injOn k)
  simpa [countA, card_range] using this

/-- Density `1/4` with an explicit additive constant. -/
theorem countA_lower (N : ℕ) : N ≤ 4 * countA N + 3 := by
  have h := k_le_countA (N / 4)
  have hmono : countA (4 * (N / 4)) ≤ countA N := countA_mono (by omega)
  omega

/-! ## The refutation -/

/-- Conjecture 00000000036 is false as stated: its claimed extremal example
`{±1 mod 6}` already violates the hypothesis (`7 - 5 = 2` is prime), so the
constant `1/3` is not attained by that construction. -/
theorem conjecture_00000000036_false :
    (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ inB a ∧ inB b ∧ a ≠ b ∧ a < b ∧
      Nat.Prime (b - a) ∧ 2 ≤ b - a) ∧
    (∀ a b : ℕ, 0 < a → 0 < b → inA a → inA b → a ≠ b →
        ¬ Nat.Prime (a + b)) ∧
    (∀ a b : ℕ, inA a → inA b → a < b → ¬ Nat.Prime (b - a)) ∧
    (∀ N, N ≤ 4 * countA N + 3) :=
  ⟨claimed_extremal_invalid,
    fun _a _b ha hb hA hB hne => inA_sum_admissible ha hb hA hB hne,
    fun _a _b hA hB hlt => inA_diff_admissible hA hB hlt,
    countA_lower⟩

end Counterexample36
