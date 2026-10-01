/-!
# Disproof of TLMC conjecture 00000000405

Conjecture: for every partition `λ` of `n`, the spin-pairing product of Kostka numbers
`K_{λ,(1^n)} · K_{λ',(1^n)}` divides `n!`, where `λ'` is the conjugate partition.

Counterexample: `n = 3`, `λ = (2,1)`.
* `K_{(2,1),(1^3)}` counts the standard Young tableaux of shape `(2,1)`: it is `2`
  (tableaux `1 2 / 3` and `1 3 / 2`); hook-length formula: `3!/(3·1·1) = 2`.
* `(2,1)` is self-conjugate, so `K_{(2,1)',(1^3)} = 2` as well.
* The product is `2 · 2 = 4`, but `3! = 6` and `6 % 4 = 2 ≠ 0`, so `4 ∤ 6`.

Everything below is pure core Lean (no Mathlib). All attack numbers are concretized
by `rfl` on a brute-force enumeration of the 64 candidate fillings of shape `(2,1)`;
the whole development is axiom-free (see `Check.lean`).
-/

/-- The shape `(2,1)` as the list of its row lengths. -/
def shape21 : List Nat := [2, 1]

/-- Column heights of a shape given by its row lengths: column `j` (0-indexed)
has one cell for every row strictly longer than `j`. -/
def colHeights (sh : List Nat) : List Nat :=
  (List.range sh.length).map fun j => (sh.filter (fun r => r > j)).length

/-- `(2,1)` is self-conjugate: its column heights are again `2,1`
(two columns, of heights 2 and 1). -/
theorem shape21_selfConjugate : colHeights shape21 = shape21 := rfl

/-- A filling of shape `(2,1)` by entries `(a, b, c)`: `a` at cell (0,0),
`b` at cell (0,1) (top row), `c` at cell (1,0) (bottom-left).
It is a standard tableau exactly when `{a,b,c} = {1,2,3}` (all distinct, in range),
the top row increases (`a < b`) and the first column increases (`a < c`). -/
def isStandard21 (a b c : Nat) : Bool :=
  1 ≤ a && a ≤ 3 && 1 ≤ b && b ≤ 3 && 1 ≤ c && c ≤ 3 &&
  a != b && a != c && b != c && a < b && a < c

/-- All `4 × 4 × 4 = 64` candidate fillings `(a, b, c)` with `a, b, c ∈ {0,...,3}`. -/
def allCandidates : List (Nat × Nat × Nat) :=
  (List.range 4).flatMap fun a =>
    (List.range 4).flatMap fun b =>
      (List.range 4).map fun c => (a, b, c)

/-- `K_{(2,1),(1^3)}`: number of standard tableaux of shape `(2,1)`, by brute-force
enumeration of all 64 candidate fillings. -/
def sytShape21 : Nat :=
  (allCandidates.filter fun t => isStandard21 t.1 t.2.1 t.2.2).length

set_option maxHeartbeats 1000000

/-- `K_{(2,1),(1^3)} = 2`: exactly the tableaux `1 2 / 3` and `1 3 / 2`. -/
theorem K_21_eq_2 : sytShape21 = 2 := rfl

/-- Factorial in core Lean: `0! = 1`, `(n+1)! = (n+1) · n!`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Cross-check with the hook-length formula: `f^{(2,1)} = 3!/(3·1·1) = 2`. -/
theorem hookCheck : fact 3 / (3 * 1 * 1) = sytShape21 := rfl

/-- Since `(2,1)' = (2,1)` (self-conjugate), the spin-pairing product is
`K_{(2,1),(1^3)} · K_{(2,1)',(1^3)} = 2 · 2 = 4`. -/
theorem product_eq_4 : sytShape21 * sytShape21 = 4 := rfl

/-- `3! = 6`. -/
theorem factorial3_eq_6 : fact 3 = 6 := rfl

/-- The conjecture's divisibility instance would require `n! % (K·K') = 0`;
here `3! % 4` computes to `2`. -/
theorem six_mod_product : fact 3 % (sytShape21 * sytShape21) = 2 := rfl

/-- The remainder is not zero, as a Bool computation: `6 % 4 == 0` is `false`. -/
theorem remainder_not_zero : (fact 3 % (sytShape21 * sytShape21) == 0) = false := rfl

/-- `6 % 4 = 2` and `2` is `Nat.succ (Nat.succ Nat.zero)`, a constructor application
that cannot equal `Nat.zero` (`Nat.noConfusion`, pure constructor logic) — refuting the
divisibility instance `4 ∣ 3!` demanded by the conjecture. -/
theorem notDivides : ¬ (fact 3 % (sytShape21 * sytShape21) = 0) :=
  fun h => Nat.noConfusion h

/-- **Disproof of conjecture 00000000405.** All ingredients of the counterexample
`n = 3, λ = (2,1)`, concretely:
`K_{(2,1),(1^3)} = 2`, `(2,1)` self-conjugate (so `K_{λ',(1^3)} = 2`),
product `4`, `3! = 6`, and `6 % 4 = 2 ≠ 0` — the divisibility fails. -/
theorem disproof_00000000405 :
    sytShape21 = 2                                -- K_{(2,1),(1^3)}
    ∧ colHeights shape21 = shape21                -- λ' = λ, so K_{λ',(1^3)} = 2
    ∧ sytShape21 * sytShape21 = 4                 -- spin-pairing product
    ∧ fact 3 = 6                                  -- n!
    ∧ fact 3 % (sytShape21 * sytShape21) = 2      -- 6 mod 4 = 2
    ∧ (fact 3 % (sytShape21 * sytShape21) == 0) = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms disproof_00000000405
