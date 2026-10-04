import Mathlib

/-!
# Conjecture 00000004163

For every residue modulo 9 we give an explicit tuple of seven actual primes
whose cubes sum to that residue. This directly contradicts the assertion that
there are exactly three local obstruction classes modulo 9.
-/

namespace Submission00000004163

/-- The sum of the seven cubic powers in a tuple. -/
def primeCubeSum (xs : Fin 7 → ℕ) : ℕ :=
  (xs 0 : ℕ) ^ 3 + (xs 1) ^ 3 + (xs 2) ^ 3 + (xs 3) ^ 3 +
    (xs 4) ^ 3 + (xs 5) ^ 3 + (xs 6) ^ 3

/-- For residue `r < 8`, use `r` copies of 19 and pad with 3s. For residue 8,
use one 2 and six 3s. Their cubes are respectively 1, 8, and 0 modulo 9. -/
def sevenWitness (r : Fin 9) : Fin 7 → ℕ := fun i =>
  if r.val = 8 then (if i.val = 0 then 2 else 3)
  else if i.val < r.val then 19 else 3

/-- Every entry of every displayed tuple is a prime. -/
theorem sevenWitness_primes (r : Fin 9) (i : Fin 7) :
    Nat.Prime (sevenWitness r i) := by
  fin_cases r <;> fin_cases i <;> norm_num [sevenWitness]

/-- Each tuple represents its residue by a sum of exactly seven prime cubes. -/
theorem sevenWitness_represents (r : Fin 9) :
    primeCubeSum (sevenWitness r) % 9 = r.val := by
  fin_cases r <;> norm_num [primeCubeSum, sevenWitness]

/-- A residue has a representation by seven cubes of primes modulo 9. -/
def RepresentedBySevenPrimeCubes (r : Fin 9) : Prop :=
  ∃ xs : Fin 7 → ℕ, (∀ i, Nat.Prime (xs i)) ∧ primeCubeSum xs % 9 = r.val

/-- Every residue class modulo 9 has an explicit seven-prime-cube representation. -/
theorem every_residue_represented :
    ∀ r : Fin 9, RepresentedBySevenPrimeCubes r := by
  intro r
  exact ⟨sevenWitness r, sevenWitness_primes r, sevenWitness_represents r⟩

/-- The conjecture asserts that exactly three residue classes are not represented. -/
def ClaimedThreeObstructions : Prop :=
  ∃ a b c : Fin 9,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    ∀ r, (¬ RepresentedBySevenPrimeCubes r) ↔ (r = a ∨ r = b ∨ r = c)

/-- Since every residue is represented by seven prime cubes, there cannot be
three non-representable residue classes modulo 9. -/
theorem conjecture_00000004163_false : ¬ ClaimedThreeObstructions := by
  rintro ⟨a, b, c, hab, hac, hbc, htable⟩
  have ha : ¬ RepresentedBySevenPrimeCubes a := (htable a).2 (Or.inl rfl)
  exact ha (every_residue_represented a)

#print axioms conjecture_00000004163_false

end Submission00000004163
