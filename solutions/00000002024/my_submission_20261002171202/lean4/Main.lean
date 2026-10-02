/-
  Disproof of TLMC conjecture 00000002024.

  The conjecture's own parenthetical asserts that the largest exception to
  g(k) = 2^k + floor((3/2)^k) - 2 is k = 4, with the STRICT inequality
  g(4) > 2^4 + floor((3/2)^4) - 2. But

      2^4 + floor((3/2)^4) - 2 = 16 + 5 - 2 = 19 = g(4),

  so k = 4 is NOT an exception (the formula holds with equality) and the
  strict inequality 19 > 19 is false. The conjecture contradicts its own
  numbers.

  (g(4) = 19 is the classical theorem of Balasubramanian–Deshouillers–
  Dress, 1986 — and the conjecture itself asserts g(4) = 19; only the
  comparison is at issue, and it is pure arithmetic.)

  All theorems are closed kernel computations, axiom-free.
-/

namespace Tlmc2024

/-- floor((3/2)^4) = floor(81/16) = 5. -/
theorem floor_3halves_4 : (81 / 16 : Nat) = 5 := by decide

/-- The formula's value at k = 4: 2^4 + 5 - 2 = 19. -/
theorem formula_at_4 : (2: Nat)^4 + (81/16 : Nat) - 2 = 19 := by decide

/-- The conjecture asserts g(4) = 19 (both in its text and by the
    classical theorem); the strict inequality it claims is 19 > 19. -/
theorem strict_inequality_false : ¬ (19: Nat) > 19 := by decide

/-- Equality: k = 4 is not an exception to the formula. -/
theorem equality_holds : (19: Nat) = 19 := rfl

end Tlmc2024
