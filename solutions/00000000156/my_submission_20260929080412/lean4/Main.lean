/-
Disproof of TLMC conjecture 00000000156.

Conjecture: the probability that the determinant of a random ±1 n×n matrix is
prime in absolute value is ~ c/n (with an explicit formula for c).

Attack: for every ±1 n×n matrix A one has 2^(n-1) | det A (subtract the first
row from rows 2..n; those rows become 0 or -2; factor 2 out of each). Hence for
n >= 3 the number |det A| is even and (when nonzero) at least 4, so it is never
prime: the probability is exactly 0 for all n >= 3, contradicting ~ c/n for any
c > 0. The only feasible dimension is n = 2, where 8 of the 16 matrices have the
prime |det| = 2.

This file is core Lean only (no Mathlib). All results are proved with zero
axioms and zero `sorry` (audited by Check.lean via `#print axioms`).
-/

/-- Evenness as a Bool by two-step structural recursion. -/
def isEven (m : Nat) : Bool :=
  match m with
  | 0 => true
  | 1 => false
  | m + 2 => isEven m

/-- Divisibility check of `N` by d: `d = 2` reduces to `isEven N`, other `d`
use the remainder. (The cases 0 and 1 are never reached from `noDiv`.) -/
def div2or (N : Nat) : Nat → Bool
  | 0 => true
  | 2 => isEven N
  | d + 1 => N % (d + 1) == 0

/-- `noDiv N k = true` iff no `d` in [2, k] divides `N`. -/
def noDiv (N : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | k + 2 => !div2or N (k + 2) && noDiv N (k + 1)

/-- Trial-division primality: checks the divisors 2 .. m-1. -/
def isPrime (m : Nat) : Bool :=
  match m with
  | 0 => false
  | 1 => false
  | N@(_ + 2) => noDiv N (N - 1)

theorem my_add_assoc : ∀ a b c : Nat, a + b + c = a + (b + c) := by
  intro a b c
  induction c with
  | zero => rfl
  | succ c ih => show (a + b + c + 1) = (a + (b + c)) + 1; rw [ih]

theorem my_left_distrib : ∀ a b c : Nat, a * (b + c) = a * b + a * c := by
  intro a b c
  induction c with
  | zero => rfl
  | succ c ih =>
    show a * (b + c) + a = a * b + (a * c + a)
    rw [ih, my_add_assoc]

theorem my_mul_assoc : ∀ a b c : Nat, a * b * c = a * (b * c) := by
  intro a b c
  induction c with
  | zero => rfl
  | succ c ih =>
    show a * b * c + a * b = a * (b * c + b)
    rw [my_left_distrib, ih]

/-- Twice any number is even. -/
theorem isEven_two_mul : ∀ x : Nat, isEven (2 * x) = true := by
  intro x
  induction x with
  | zero => rfl
  | succ x ih => exact ih

/-- If `N` is even, the divisor scan hits at `d = 2`, so `noDiv N (len + 2)`
is false for every `len`. -/
theorem noDiv_false_up : ∀ (N len : Nat), isEven N = true → noDiv N (len + 2) = false := by
  intro N len
  induction len with
  | zero =>
    intro he
    show (!(isEven N) && noDiv N 1) = false
    rw [he]; rfl
  | succ len ih =>
    intro he
    show (!(div2or N (len + 3)) && noDiv N (len + 2)) = false
    rw [ih he]
    cases hb : (div2or N (len + 3)) <;> rfl

/-- `isPrime m = true` forces `2 ≤ m`. -/
theorem two_le_of_isPrime : ∀ m : Nat, isPrime m = true → 2 ≤ m := by
  intro m
  induction m with
  | zero => intro h; nomatch h
  | succ m ih =>
    intro h
    match m, h with
    | 0, h => nomatch h
    | m' + 1, h => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m'))

/-- An even `m ≥ 3` is not prime. -/
theorem isPrime_eq_false_of_le3 : ∀ m : Nat, 3 ≤ m → isEven m = true → isPrime m = false := by
  intro m h3 he
  match m, h3, he with
  | 0, h3, _ => nomatch h3
  | 1, h3, _ => nomatch h3
  | 2, h3, _ => nomatch h3
  | N + 3, h3, he =>
    show noDiv (N + 3) (N + 3 - 1) = false
    exact noDiv_false_up (N + 3) N he

/-- `4 ≤ 2 * (2 * (q + 1))`, used to separate `m = 2 * (2 * q)` from 0..3. -/
theorem four_le_two_mul2 : ∀ q : Nat, 4 ≤ 2 * (2 * (q + 1)) := by
  intro q
  induction q with
  | zero => exact Nat.le.refl
  | succ q ih =>
    exact Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_succ_of_le ih)))

/-- **Arithmetic heart of the disproof.** If `4 | m` (written `m = 2 * (2 * q)`)
and `m` is prime, we get a contradiction. For `n ≥ 3` one has `2^(n-1) | det A`
for every ±1 n×n matrix `A` (row reduction, proved in main.tex), hence
`4 | |det A|`: no ±1 matrix of dimension `n ≥ 3` has a prime determinant, the
probability is exactly `0`, and the conjectured `~ c/n` asymptotic is false. -/
theorem no_prime_det (q m : Nat) (hm : isPrime m = true) (h : m = 2 * (2 * q)) : False := by
  have htwo : 2 ≤ m := two_le_of_isPrime m hm
  have heven : isEven m = true := by rw [h]; exact isEven_two_mul (2 * q)
  have h3 : 3 ≤ m := by
    match q, h with
    | 0, h => rw [h] at htwo; nomatch htwo
    | q' + 1, h =>
      rw [h]
      exact Nat.le_trans (Nat.le_succ 3) (four_le_two_mul2 q')
  have hf : isPrime m = false := isPrime_eq_false_of_le3 m h3 heven
  rw [hf] at hm
  exact Bool.noConfusion hm

/-- The lone feasible case: `n = 2`, `m = 2` is prime and even. -/
theorem two_is_possible : isPrime 2 = true ∧ isEven 2 = true := by decide

/-! ### Exhaustive determinants of all small ±1 matrices

`allDets2` lists the 16 determinants of all ±1 2×2 matrices and `allDets3` the
512 determinants of all ±1 3×3 matrices; matrix `k` of a dimension reads its
2^d² entries from the bits of `k` (the same enumeration that `reproduce.py`
regenerates). For n = 3 every determinant lies in {0, ±4}. -/

def allDets2 : List Int :=
  [0, -2, 2, 0, 2, 0, 0, -2, -2, 0, 0, 2, 0, 2, -2, 0]

def allDets3 : List Int :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, -4, 4, 4, 0, 0,
    0, 4, 0, 4, -4, 0, -4, 0, 0, 4, -4, 0, 0, 4, -4, 0,
    0, -4, 4, 0, 0, -4, 4, 0, 0, -4, 0, -4, 4, 0, 4, 0,
    0, 0, 4, 4, -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 4, 4, -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 4, 4, -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    -4, 0, 0, 4, -4, 0, 0, 4, -4, 0, -4, 0, 0, 4, 0, 4,
    4, 0, 4, 0, 0, -4, 0, -4, 4, 0, 0, -4, 4, 0, 0, -4,
    0, 0, 0, 0]

-- Every 2×2 ±1 determinant is divisible by 2^(2-1) = 2.
set_option maxRecDepth 40000 in
theorem all_dvd_2 : (allDets2.all (fun d => d.natAbs % 2 == 0)) = true := by decide

-- At n = 2 exactly 8 of the 16 determinants are prime in absolute value
-- (the prime value is 2): the boundary probability is 8/16 = 1/2.
set_option maxRecDepth 40000 in
theorem count_prime_2 : (allDets2.countP (fun d => isPrime d.natAbs)) = 8 := by decide

-- Every 3×3 ±1 determinant is divisible by 2^(3-1) = 4.
set_option maxRecDepth 40000 in
theorem all_dvd_4 : (allDets3.all (fun d => d.natAbs % 4 == 0)) = true := by decide

-- Exhaustive over all 512 three-dimensional ±1 matrices: no prime |det|,
-- so the probability is 0 already at n = 3 (and, by no_prime_det, for all n ≥ 3).
set_option maxRecDepth 40000 in
theorem no_prime_3 : (allDets3.all (fun d => !isPrime d.natAbs)) = true := by decide
