namespace Tlmc443

/-- 2^5 - 2 = 30 (the numerator; mu-weights for prime n = 5). -/
theorem numer : ((2:Nat)^5 - 2) = 30 := by decide

/-- Witt's formula at k = 2, n = 5: 30 / 5 = 6. -/
theorem witt_5 : (30 / 5 : Nat) = 6 := by decide

/-- The conjectured lower bound at n = 5: 2^4 - 2^{ceil(5/2)} = 16 - 8. -/
theorem bound_5 : ((2:Nat)^4 - (2:Nat)^3) = 8 := by decide

/-- The claimed inequality dim L_5 >= 8 is 6 >= 8: false. -/
theorem violated : ¬ ((6:Nat) >= 8) := by decide

end Tlmc443
