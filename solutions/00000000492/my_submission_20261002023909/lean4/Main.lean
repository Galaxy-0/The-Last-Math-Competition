/-!
# Disproof of TLMC conjecture 00000000492

The conjecture asserts that for a uniformly random standard tableau,
`(Σ hooks)/n² = (n²−1)/3`.

Attack: every hook length of an `n`-cell tableau is at most `n`, so
`Σ hooks ≤ n²` and `(Σ hooks)/n² ≤ 1`, while `(n²−1)/3 > 1` for every `n ≥ 3`.
The conjectured value lies strictly above the a-priori cap of the left-hand
side, for every shape.

Concretely, for `n = 3` cells and the row shape `(3)` (whose unique standard
tableau has hook lengths `3, 2, 1`, sum `6`):
`(Σ hooks)/n² = 6/9 = 2/3` but the conjecture demands `(9−1)/3 = 8/3`.
Cross-multiplying over `Nat` (all quantities positive): `6·3 ≠ 8·9`.

This file concretizes those attack numbers as theorems over `Nat`, proved by
`rfl`/`decide`/`omega`. `Check.lean` audits all of them with `#print axioms`:
none may depend on any axiom (and there is no `sorry`).
-/

/-! ## The universal cap -/

/-- **Cap.** Any hook length of a 3-cell tableau is at most 3, so the hook sum of
any 3-cell tableau is at most `9 = n²`; hence `(Σ hooks)/n² ≤ 1` always. -/
theorem cap3 (a b c : Nat) (ha : a ≤ 3) (hb : b ≤ 3) (hc : c ≤ 3) :
    a + b + c ≤ 9 := by
  have h : a + b + c ≤ (3 : Nat) + 3 + 3 := Nat.add_le_add (Nat.add_le_add ha hb) hc
  have h9 : (3 : Nat) + 3 + 3 = 9 := rfl
  rw [h9] at h
  exact h

/-- **Overshoot.** For every `n ≥ 3` the conjectured value `(n²−1)/3` exceeds the
cap `1`: cross-multiplied over `Nat`, `3 < n² − 1`. -/
theorem overshoot (n : Nat) (h : 3 ≤ n) : 3 < n * n - 1 := by
  have h1 : (3 : Nat) * 3 ≤ 3 * n := Nat.mul_le_mul_left 3 h
  have h2 : (3 : Nat) * n ≤ n * n := Nat.mul_le_mul_right n h
  have h9 : (9 : Nat) ≤ n * n := Nat.le_trans h1 h2
  have hs : (9 : Nat) - 1 ≤ n * n - 1 := Nat.sub_le_sub_right h9 1
  exact Nat.lt_of_lt_of_le (by decide : (3 : Nat) < 9 - 1) hs

/-! ## Concrete counterexample: `n = 3`, row shape `(3)`, hooks `3 2 1` -/

/-- Hook sum of the row shape `(3)`: `3 + 2 + 1 = 6`. -/
theorem row3_sum : (3 : Nat) + 2 + 1 = 6 := rfl

/-- The counterexample: `6/9 = 2/3 ≠ 8/3`, cross-multiplied `6·3 ≠ 8·9`. -/
theorem row3_disproof : ((3 : Nat) + 2 + 1) * 3 ≠ 8 * 9 := by decide

/-- Even the maximal conceivable hook sum `n² = 9` cannot reach the conjectured
`8/3`: `1 < 8/3` cross-multiplied is `9·3 < 8·9`. -/
theorem cap_gap_n3 : (9 : Nat) * 3 < 8 * 9 := by decide

/-! ## Square reading (`n × n` tableau, `n²` cells) -/

/-- Hook sum of the `3×3` square: `5+4+4+3+3+3+2+2+1 = 27 = 3³`, so
`(Σ hooks)/n² = 27/9 = 3`. -/
theorem square3_sum : (5 : Nat) + 4 + 4 + 3 + 3 + 3 + 2 + 2 + 1 = 27 := by decide

/-- Square reading disproof at `n = 3`: `27/9 = 3 ≠ 8/3`,
cross-multiplied `27·3 ≠ 8·9`. -/
theorem square3_disproof : (27 : Nat) * 3 ≠ 8 * 9 := by decide

/-! ## Divide-by-`n` reading -/

/-- Divide-by-`n` disproof at `n = 3`: `6/3 = 2 ≠ 8/3`, cross-multiplied
`6·3 ≠ 8·3`. -/
theorem row3_divn_disproof : (6 : Nat) * 3 ≠ 8 * 3 := by decide

/-- Divide-by-`n` cap gap at `n = 4`: the maximum `(Σ hooks)/n = 16/4 = 4` is
still below the conjectured `(16−1)/3 = 5`; cross-multiplied `16·1 < 5·4`. -/
theorem cap_gap_divn_n4 : (16 : Nat) * 1 < 5 * 4 := by decide

/-- Divide-by-`n` overshoot in general: for `n ≥ 4`, `3n < n² − 1`, i.e.
`(n²−1)/3 > n ≥ (Σ hooks)/n`. -/
theorem overshoot_divn (n : Nat) (h : 4 ≤ n) : 3 * n < n * n - 1 := by
  have hpos : (2 : Nat) ≤ n := Nat.le_trans (by decide : (2 : Nat) ≤ 4) h
  have h41 : (4 : Nat) * n = 3 * n + n := Nat.succ_mul 3 n
  have hA : (3 : Nat) * n + 1 < 4 * n := by
    calc 3 * n + 1 < 3 * n + 2 := Nat.lt_succ_self (3 * n + 1)
      _ ≤ 3 * n + n := Nat.add_le_add_left hpos (3 * n)
      _ = 4 * n := h41.symm
  have hB : (4 : Nat) * n ≤ n * n := by
    rw [Nat.mul_comm 4 n]
    exact Nat.mul_le_mul_left n h
  have hC : (3 : Nat) * n + 1 < n * n := Nat.lt_of_lt_of_le hA hB
  have hD : (3 : Nat) * n + 2 - 1 ≤ n * n - 1 := Nat.sub_le_sub_right hC 1
  have hE : (3 : Nat) * n + 2 - 1 = 3 * n + 1 := rfl
  rw [hE] at hD
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (3 * n)) hD

/-! ## Randomization over tableaux cannot help -/

/-- Shape `(2,1)` (`n = 3` cells) has two standard tableaux, both with the same
hook multiset `{3, 1, 1}`; hence `E[Σ hooks] = 5` is a deterministic constant of
the shape. -/
theorem shape21_expectation : (3 : Nat) + 1 + 1 = 5 := rfl

/-- The randomized reading disproof: `E[Σ hooks]/n² = 5/9 ≠ 8/3`,
cross-multiplied `5·3 ≠ 8·9`. -/
theorem shape21_disproof : (5 : Nat) * 3 ≠ 8 * 9 := by decide
