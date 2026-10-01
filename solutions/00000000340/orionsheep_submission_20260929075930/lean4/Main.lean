/-!
# TLMC conjecture 00000000340 — counterexample certificate

Conjecture 00000000340 claims: for every algebraic irrational `α`,
`liminf_N G_N(α) = 1` and `limsup_N G_N(α) = ∞`, where
`G_N(α) = (∏_{j≤N} a_j)^(1/N)` and `a_j` are the continued-fraction partial
quotients of `α`.

Counterexample: `α = √2 = [1; 2, 2, 2, …]` (algebraic irrational, root of
`x² − 2`). Its partial quotients are `a₀ = 1` and `a_j = 2` for `j ≥ 1`, so
`∏_{j<N} a_j = 2^(N−1)` and `G_N = (2^(N−1))^(1/N) = 2^((N−1)/N) → 2`.
Hence `G` is bounded: `G_N ≤ 2` for every `N` (so `limsup ≤ 2 < ∞`), and
`G_N² ≥ 2` for every `N ≥ 2` (so `liminf ≥ √2 > 1`). Both claims of the
conjecture fail. Numerically, `G_N ≥ 1.99` for every `N ≥ 139` (sharp
threshold) and `G_1000 ≈ 1.99861`.

This file is self-contained: core Lean 4 only, no Mathlib, and **zero axioms,
zero `sorry`** — every proof is `rfl`/`decide` or an explicit `Nat` argument.
-/

namespace TLMC340

/-! ## Small self-contained arithmetic helpers -/

/-- `x ≤ 2 * x`. -/
theorem le_double (x : Nat) : x ≤ 2 * x := by
  induction x with
  | zero => exact Nat.le_refl 0
  | succ y ih =>
      have h1 : y + 1 ≤ Nat.succ (2 * y) := Nat.succ_le_succ ih
      have h2 : Nat.succ (2 * y) ≤ Nat.succ (2 * y + 1) := Nat.succ_le_succ (Nat.le_succ (2 * y))
      exact Nat.le_trans h1 h2

/-- Right-multiplication by a fixed natural is monotone. -/
theorem mul_le_mul_right' {m n : Nat} (k : Nat) (h : m ≤ n) : m * k ≤ n * k :=
  Nat.mul_le_mul h (Nat.le_refl k)

/-- `a * b * c = a * (b * c)`, proved from scratch (the core `Nat.mul_assoc`
of this toolchain is proved with `propext`). -/
theorem mul_assoc' : ∀ (a b c : Nat), a * b * c = a * (b * c)
  | _, _, 0 => rfl
  | a, b, c + 1 => by
      show a * b * c + a * b = a * (b * c + b)
      rw [mul_assoc' a b c, Nat.mul_add a (b * c) b]

/-- `n * (m * k) = m * (n * k)` (from `mul_assoc'` and `Nat.mul_comm`). -/
theorem mul_left_comm' (n m k : Nat) : n * (m * k) = m * (n * k) := by
  rw [← mul_assoc' n m k, Nat.mul_comm n m, mul_assoc' m n k]

/-- Powers with a common exponent are monotone in the base. -/
theorem pow_le_pow_left' : ∀ (k x y : Nat), x ≤ y → x ^ k ≤ y ^ k
  | 0, _, _, _ => Nat.le_refl 1
  | k + 1, x, y, h => Nat.mul_le_mul (pow_le_pow_left' k x y h) h

/-- `2 ^ (n+1) = 2 ^ n * 2` (the definitional unfolding direction). -/
theorem pow2_succ_mul (n : Nat) : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n

theorem pow100_succ_mul (n : Nat) : 100 ^ (n + 1) = 100 ^ n * 100 :=
  Nat.pow_succ 100 n

theorem pow201_succ_mul (n : Nat) : 201 ^ (n + 1) = 201 ^ n * 201 :=
  Nat.pow_succ 201 n

/-- `2 ^ n ≤ 2 ^ n * 2`. -/
theorem pow2_le_double (n : Nat) : 2 ^ n ≤ 2 ^ n * 2 := by
  induction n with
  | zero => exact Nat.le_succ 1
  | succ m ih =>
      calc 2 ^ (m + 1) = 2 ^ m * 2 := rfl
        _ ≤ (2 ^ m * 2) * 2 := mul_le_mul_right' 2 ih
        _ = 2 ^ (m + 1) * 2 := rfl

/-- `2 ^ n ≤ 2 ^ (n + 1)`. -/
theorem pow2_succ_le (n : Nat) : 2 ^ n ≤ 2 ^ (n + 1) := pow2_le_double n

/-- Regrouping: `(A * 2) * (B * 100) = 200 * (A * B)`. -/
theorem mul_pair_swap (A B : Nat) : (A * 2) * (B * 100) = 200 * (A * B) :=
  calc (A * 2) * (B * 100)
      = A * (2 * (B * 100)) := mul_assoc' A 2 (B * 100)
    _ = A * (2 * (100 * B)) :=
          congrArg (fun x => A * x)
            (congrArg (fun x => 2 * x) (Nat.mul_comm B 100))
    _ = A * ((2 * 100) * B) :=
          congrArg (fun x => A * x) (mul_assoc' 2 100 B).symm
    _ = (2 * 100) * (A * B) := mul_left_comm' A (2 * 100) B
    _ = 200 * (A * B) := rfl

/-! ## The continued fraction of √2 -/

/-- Partial quotients of `√2 = [1; 2, 2, 2, …]`, indexed from `0`:
`a 0 = 1` and `a (j+1) = 2`. -/
def a : Nat → Nat
  | 0 => 1
  | _ + 1 => 2

/-- `prodA N = ∏_{j<N} a j`, the product of the first `N` partial quotients.
Under 1-based indexing (as in the conjecture) this is `∏_{j≤N} a_j`. -/
def prodA : Nat → Nat
  | 0 => 1
  | n + 1 => a n * prodA n

theorem a_zero : a 0 = 1 := rfl

theorem a_succ (j : Nat) : a (j + 1) = 2 := rfl

/-- **Key identity.** `∏_{j<N} a j = 2^(N−1)`, i.e. `G_N(√2) = (2^(N−1))^(1/N)
= 2^((N−1)/N) → 2`. -/
theorem prodA_eq : ∀ n : Nat, prodA n = 2 ^ (n - 1)
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
      have h1 : prodA (n + 1) = 2 ^ n := prodA_eq (n + 1)
      calc prodA (n + 2) = 2 * prodA (n + 1) := rfl
        _ = 2 * 2 ^ n := congrArg (fun x => 2 * x) h1
        _ = 2 ^ n * 2 := Nat.mul_comm _ _
        _ = 2 ^ (n + 2 - 1) := Nat.pow_succ 2 n

/-- Concrete instance: the product of the first `1000` partial quotients of
`√2` is exactly `2^999`, so `G_1000 = (2^999)^(1/1000) ≈ 1.99861`. -/
theorem prodA_1000 : prodA 1000 = 2 ^ 999 := prodA_eq 1000

/-- Numeric certificate at `N = 1000`, as exact integer inequalities:
`199^1000 ≤ 2^999 · 100^1000` and `2^999 · 100^1000 ≤ 201^1000`, i.e.
`1.99 ≤ G_1000 ≤ 2.01`. -/
theorem G1000_bounds :
    199 ^ 1000 ≤ 2 ^ 999 * 100 ^ 1000 ∧ 2 ^ 999 * 100 ^ 1000 ≤ 201 ^ 1000 := by
  set_option maxRecDepth 8000 in
  set_option exponentiation.threshold 100000 in
  decide

/-! ## Global bounds that refute both claims of the conjecture -/

/-- `G_N ≤ 2` for every `N` (integer form `∏_{j<N} a j ≤ 2^N`).
This kills `limsup G_N = ∞`: the sequence is bounded by `2`. -/
theorem prodA_le_pow2 (n : Nat) : prodA n ≤ 2 ^ n := by
  cases n with
  | zero => exact Nat.le_refl 1
  | succ m =>
      have h1 : prodA (m + 1) = 2 ^ m := prodA_eq (m + 1)
      rw [h1]
      exact pow2_succ_le m

/-- `G_N² ≥ 2` for every `N ≥ 2` (integer form `2^(n+2) ≤ prodA (n+2)²`),
so `G_N ≥ √2 > 1`. This kills `liminf G_N = 1`. -/
theorem pow2_le_sq_prodA : ∀ n : Nat, 2 ^ (n + 2) ≤ prodA (n + 2) * prodA (n + 2)
  | 0 => Nat.le_refl (2 * 2)
  | m + 1 =>
      have ih := pow2_le_sq_prodA m
      have hs : prodA (m + 2) * prodA (m + 2) * 2
          ≤ (2 * prodA (m + 2)) * (2 * prodA (m + 2)) :=
        calc prodA (m + 2) * prodA (m + 2) * 2
            = 2 * (prodA (m + 2) * prodA (m + 2)) := Nat.mul_comm _ _
          _ ≤ 2 * (prodA (m + 2) * (2 * prodA (m + 2))) :=
                Nat.mul_le_mul_left 2
                  (Nat.mul_le_mul (Nat.le_refl (prodA (m + 2)))
                    (le_double (prodA (m + 2))))
          _ = (2 * prodA (m + 2)) * (2 * prodA (m + 2)) :=
                (mul_assoc' 2 (prodA (m + 2)) (2 * prodA (m + 2))).symm
      calc 2 ^ (m + 1 + 2) = 2 ^ (m + 2 + 1) := rfl
        _ = 2 ^ (m + 2) * 2 := Nat.pow_succ 2 (m + 2)
        _ ≤ prodA (m + 2) * prodA (m + 2) * 2 :=
              mul_le_mul_right' 2 ih
        _ ≤ (2 * prodA (m + 2)) * (2 * prodA (m + 2)) := hs

/-- Sharp eventual bound: `G_N ≥ 1.99` for every `N ≥ 139` (integer form
`199^N ≤ 2^(N−1) · 100^N`). The threshold `139` is sharp: at `N = 138` the
inequality fails (verified by exact integer arithmetic in `reproduce.py`). -/
theorem G_ge_199 : ∀ n : Nat, 199 ^ (139 + n) ≤ 2 ^ (138 + n) * 100 ^ (139 + n) := by
  intro n
  induction n with
  | zero =>
      set_option maxRecDepth 8000 in
      set_option exponentiation.threshold 100000 in
      decide
  | succ m ih =>
      calc 199 ^ (139 + (m + 1))
          = 199 ^ (139 + m) * 199 := Nat.pow_succ 199 (139 + m)
        _ = 199 * 199 ^ (139 + m) := Nat.mul_comm _ _
        _ ≤ 199 * (2 ^ (138 + m) * 100 ^ (139 + m)) :=
              Nat.mul_le_mul (Nat.le_refl 199) ih
        _ ≤ 200 * (2 ^ (138 + m) * 100 ^ (139 + m)) :=
              mul_le_mul_right' _ (Nat.le_succ 199)
        _ = 2 ^ (138 + (m + 1)) * 100 ^ (139 + (m + 1)) :=
              (mul_pair_swap _ _).symm

/-- Derived numeric certificate: `199^1000 ≤ 2^999 · 100^1000`
(i.e. `G_1000 ≥ 1.99`), obtained from `G_ge_199` at `n = 861`. -/
theorem G1000_lower : 199 ^ 1000 ≤ 2 ^ 999 * 100 ^ 1000 := by
  set_option maxRecDepth 8000 in
  exact G_ge_199 861

/-- `(200)^n = 2^n · 100^n` is `≤ 201^n`; i.e. `G_N ≤ 2 < 2.01` for all `N`
in integer form `2^N · 100^N ≤ 201^N`. -/
theorem pow200_le : ∀ n : Nat, 2 ^ n * 100 ^ n ≤ 201 ^ n
  | 0 => Nat.le_refl 1
  | n + 1 =>
      have e1 : 2 ^ (n + 1) * 100 ^ (n + 1) = (2 ^ n * 2) * (100 ^ n * 100) := by
        rw [pow2_succ_mul, pow100_succ_mul]
      calc 2 ^ (n + 1) * 100 ^ (n + 1)
          = (2 ^ n * 2) * (100 ^ n * 100) := e1
        _ = 200 * (2 ^ n * 100 ^ n) := mul_pair_swap _ _
        _ ≤ 200 * 201 ^ n := Nat.mul_le_mul_left 200 (pow200_le n)
        _ ≤ 201 * 201 ^ n := mul_le_mul_right' _ (Nat.le_succ 200)
        _ = 201 ^ n * 201 := Nat.mul_comm _ _
        _ = 201 ^ (n + 1) := (pow201_succ_mul n).symm

/-- Derived numeric certificate: `2^999 · 100^1000 ≤ 201^1000`
(i.e. `G_1000 ≤ 2 < 2.01`). -/
theorem G1000_upper : 2 ^ 999 * 100 ^ 1000 ≤ 201 ^ 1000 :=
  calc 2 ^ 999 * 100 ^ 1000 ≤ 2 ^ 1000 * 100 ^ 1000 :=
        mul_le_mul_right' _ (pow2_succ_le 999)
    _ ≤ 201 ^ 1000 := pow200_le 1000

/-! ## Summary certificate -/

/-- **Disproof certificate for conjecture 00000000340.** For the algebraic
irrational `α = √2`:
* `∏_{j<N} a j = 2^(N−1)` for all `N`, hence `G_N = 2^((N−1)/N) → 2`;
* `G_N ≤ 2` for all `N`, hence `limsup G_N ≤ 2 < ∞` — contradicts `limsup = ∞`;
* `G_N² ≥ 2` for all `N ≥ 2`, hence `liminf G_N ≥ √2 > 1` — contradicts `liminf = 1`;
* moreover `G_N ≥ 1.99` for all `N ≥ 139` and `G_1000 = (2^999)^(1/1000)`.
So the conjecture is FALSE. -/
theorem disproof :
    (∀ n : Nat, prodA n = 2 ^ (n - 1)) ∧
    (∀ n : Nat, prodA n ≤ 2 ^ n) ∧
    (∀ n : Nat, 2 ^ (n + 2) ≤ prodA (n + 2) * prodA (n + 2)) ∧
    (∀ n : Nat, 199 ^ (139 + n) ≤ 2 ^ (138 + n) * 100 ^ (139 + n)) ∧
    prodA 1000 = 2 ^ 999 :=
  ⟨prodA_eq, prodA_le_pow2, pow2_le_sq_prodA, G_ge_199, prodA_1000⟩

end TLMC340
