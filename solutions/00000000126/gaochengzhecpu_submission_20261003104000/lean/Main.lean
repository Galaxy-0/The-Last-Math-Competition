import Std

/-! Base-four generalized repunits have exactly one prime value, namely five.
All lengths are treated symbolically; no search bound is used. -/
namespace Conjecture126

/-- Length n: 1 + a + ... + a^(n-1), with the empty sum at n = 0. -/
def repunit (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => repunit a n + a ^ n

/-- The ordinary positive-prime definition in terms of all factorizations. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ a b : Nat, p = a * b → a = 1 ∨ b = 1

theorem geometric_identity (n : Nat) : 3 * repunit 4 n + 1 = 4 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [repunit, Nat.pow_succ]
    omega

theorem square_identity (n : Nat) :
    3 * repunit 4 n + 1 = 2 ^ n * 2 ^ n := by
  calc
    3 * repunit 4 n + 1 = 4 ^ n := geometric_identity n
    _ = 2 ^ n * 2 ^ n := Nat.mul_pow 2 2 n

theorem pow_two_nonzero_mod_three (n : Nat) :
    2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hstep : 2 ^ (n + 1) % 3 = ((2 ^ n % 3) * 2) % 3 := by
      rw [Nat.pow_succ, Nat.mul_mod]
    rcases ih with h | h
    · rw [hstep, h]; decide
    · rw [hstep, h]; decide

theorem pow_two_at_least_eight (n : Nat) (hn : 3 ≤ n) : 8 ≤ 2 ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have positive : ∀ m : Nat, 1 ≤ 2 ^ m := by
    intro m
    induction m with
    | zero => decide
    | succ m ih => simp only [Nat.pow_succ]; omega
  have hm := positive m
  rw [Nat.pow_add]
  omega

theorem predecessor_product (p : Nat) (hp : 0 < p) :
    (p - 1) * (p + 1) + 1 = p * p := by
  have hpred : p - 1 + 1 = p := by omega
  calc
    (p - 1) * (p + 1) + 1 = (p - 1) * p + (p - 1) + 1 := by
      rw [Nat.mul_add, Nat.mul_one]
    _ = (p - 1) * p + p := by omega
    _ = ((p - 1) + 1) * p := by rw [Nat.add_mul, Nat.one_mul]
    _ = p * p := by rw [hpred]

/-- An actual factorization with both factors greater than one for every n >= 3. -/
theorem all_long_repunit_composite (n : Nat) (hn : 3 ≤ n) :
    ∃ a b : Nat, 1 < a ∧ 1 < b ∧ repunit 4 n = a * b := by
  let p := 2 ^ n
  let q := p / 3
  have hp : 8 ≤ p := pow_two_at_least_eight n hn
  have hdiv : p % 3 + 3 * q = p := Nat.mod_add_div p 3
  have hsquare : 3 * repunit 4 n + 1 = p * p := square_identity n
  have hprod := predecessor_product p (by omega)
  rcases pow_two_nonzero_mod_three n with hmod | hmod
  · have hmod' : p % 3 = 1 := hmod
    have hpred : p - 1 = 3 * q := by omega
    have hq : 1 < q := by omega
    have heq : repunit 4 n = q * (p + 1) := by
      rw [hpred, Nat.mul_assoc] at hprod
      omega
    exact ⟨q, p + 1, hq, by omega, heq⟩
  · have hmod' : p % 3 = 2 := hmod
    have hsucc : p + 1 = 3 * (q + 1) := by omega
    have hq : 1 < q + 1 := by omega
    have heq : repunit 4 n = (p - 1) * (q + 1) := by
      rw [hsucc, ← Nat.mul_left_comm] at hprod
      omega
    exact ⟨p - 1, q + 1, by omega, hq, heq⟩

theorem prime_repunit_length (n : Nat) (h : IsPrime (repunit 4 n)) : n = 2 := by
  have hshort : n < 3 := by
    by_cases hn : n < 3
    · exact hn
    · have hn' : 3 ≤ n := by omega
      rcases all_long_repunit_composite n hn' with ⟨a, b, ha, hb, heq⟩
      rcases h.2 a b heq with h1 | h1 <;> omega
  have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn with rfl | rfl | rfl
  · have hp := h.1
    simp [repunit] at hp
  · have hp := h.1
    simp [repunit] at hp
  · rfl

theorem five_is_prime : IsPrime 5 := by
  refine ⟨by decide, ?_⟩
  intro a b hab
  have ha : 1 ≤ a := by
    cases a with
    | zero => simp at hab
    | succ a => omega
  have hb : 1 ≤ b := by
    cases b with
    | zero => simp at hab
    | succ b => omega
  have ha5 : a ≤ 5 := by
    have h := Nat.mul_le_mul_left a hb
    simp only [Nat.mul_one] at h
    omega
  have hb5 : b ≤ 5 := by
    have h := Nat.mul_le_mul_right b ha
    simp only [Nat.one_mul] at h
    omega
  have checked : ∀ a b : Fin 6, 5 = a.val * b.val → a.val = 1 ∨ b.val = 1 := by decide
  exact checked ⟨a, by omega⟩ ⟨b, by omega⟩ hab

theorem prime_repunit_exact (n : Nat) : IsPrime (repunit 4 n) ↔ n = 2 := by
  constructor
  · exact prime_repunit_length n
  · intro hn
    subst n
    exact five_is_prime

theorem every_prime_repunit_is_five (n : Nat) (h : IsPrime (repunit 4 n)) :
    repunit 4 n = 5 := by
  rw [prime_repunit_length n h]
  rfl

-- For subsets of natural numbers, infinitude is equivalent to being unbounded.
-- Length n = k+1 corresponds exactly to the final exponent k in SOURCE.md.
def InfinitelyManyPrimeRepunits (a : Nat) : Prop :=
  ∀ B : Nat, ∃ n : Nat, 0 < n ∧ IsPrime (repunit a n) ∧ B < repunit a n

def OriginalClaim : Prop :=
  ∀ a : Nat, 2 ≤ a → InfinitelyManyPrimeRepunits a

theorem base_four_not_infinitely_many : ¬ InfinitelyManyPrimeRepunits 4 := by
  intro h
  rcases h 5 with ⟨n, _, hn, hbig⟩
  have heq := every_prime_repunit_is_five n hn
  omega

theorem conjecture126_counterexample : ¬ OriginalClaim := by
  intro h
  exact base_four_not_infinitely_many (h 4 (by decide))

#print axioms all_long_repunit_composite
#print axioms prime_repunit_length
#print axioms five_is_prime
#print axioms prime_repunit_exact
#print axioms every_prime_repunit_is_five
#print axioms base_four_not_infinitely_many
#print axioms conjecture126_counterexample

end Conjecture126
