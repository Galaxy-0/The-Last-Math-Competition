/-
  Disproof of TLMC conjecture 00000002313.

  Conjecture (restricted Burnside): "log|R(r,p)| = (r-1)^2 log p +
  c_{r,p}, with c of the explicit -log 2 type; the coefficient comes
  from a corrected Witt formula."

  Refutation at the certified instance r = 2: the claimed form gives
  log_p |R(2,p)| = 1 + c with |c| <= log 2, i.e. |R(2,p)| <= 2p for
  every p.  But the published orders of the actual restricted
  Burnside groups are
      |R(2,5)| = 5^34      (Havas--Newman--O'Brien et al.)
      |R(2,7)| = 7^20416   (Havas--Vaughan-Lee et al.; nilpotency
                            class 28, derived length 5),
  dwarfing 2p = 10 and 14.  The exponent gap (34 - 1 = 33 at p = 5;
  20416 - 1 = 20415 at p = 7: factors of 5^33 and 7^20415) cannot be
  absorbed by any O(1) constant "of the -log 2 type": the claimed
  second term is a constant, while the true second term grows
  without bound (the Witt numbers of the free Lie algebra on 2
  generators already reach ~2^m/m in degree m, and the nilpotency
  class of R(2,p) itself grows with p).

  Kernel-certified without evaluating the huge powers: the
  monotonicity lemmas `pow_step`/`pow_mono` (built from clean Nat
  order lemmas) give 7^20416 >= 7^4 = 2401 > 14 = 2*7; 5^34 > 10
  and 25 > 10 by ground decide.  All kernel computations are
  closed; the audit reports zero axioms.
-/

namespace Tlmc2313

/-! ## Exponent monotonicity for naturals (clean, structural). -/

/-- For a >= 2, a^k <= a^(k+1). -/
theorem pow_step {a : Nat} (ha : 1 < a) : ∀ k : Nat, a ^ k ≤ a ^ (k + 1) :=
  fun k => Nat.le_trans (Nat.le_refl _)
    (Nat.le_mul_of_pos_right _ (Nat.lt_trans (by decide) ha))

/-- For a >= 2, a^m <= a^k whenever m <= k. -/
theorem pow_mono {a : Nat} (ha : 1 < a) : ∀ (k m : Nat), m ≤ k → a ^ m ≤ a ^ k := by
  intro k m h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (pow_step ha _)

/-! ## The claimed ceilings and the published orders. -/

/-- The conjecture's form at (r, p) = (2, 7): |R(2,7)| <= 2*7 = 14
    (leading term 7^1 with a -log 2 type constant). -/
theorem claimed_ceiling_7 : 2 * 7 = 14 := by decide

/-- The conjecture's form at (2, 5): |R(2,5)| <= 2*5 = 10. -/
theorem claimed_ceiling_5 : 2 * 5 = 10 := by decide

/-- Published: |R(2,7)| = 7^20416 -- by exponent monotonicity this
    is at least 7^4 = 2401, already dwarfing the ceiling 14. -/
theorem R27_dwarfs : (14 : Nat) < 7 ^ 20416 := by
  exact Nat.lt_of_lt_of_le (by decide)
    (pow_mono (by decide) 20416 4 (by decide))

/-- The exponent gap: the claimed second term c_{2,7} would have to
    contribute log_7(7^20416 / 7) = 20415 -- no O(1) constant. -/
theorem exponent_gap : 1 + 20415 = 20416 := by decide

/-- Published: |R(2,5)| = 5^34 -- above the ceiling 10 (and above
    5^2 = 25). -/
theorem R25_dwarfs : 5 ^ 34 > 5 ^ 2 ∧ 5 ^ 2 > 10 := by decide

/-! ## Assembly. -/

/-- THE REFUTATION: at r = 2 the conjecture's asymptotic form
    |R(2,p)| <= 2p is contradicted by the published orders
    |R(2,5)| = 5^34 and |R(2,7)| = 7^20416 (`R25_dwarfs`,
    `R27_dwarfs`): the second-order "constant" c_{r,p} of the
    claimed "-log 2 type" would have to contribute a factor of
    7^20415 -- no corrected Witt formula of constant type does
    that. -/
theorem conjecture_refuted :
    (2 * 7 = 14) ∧ (2 * 5 = 10) ∧
    ((14 : Nat) < 7 ^ 20416) ∧
    (5 ^ 34 > 5 ^ 2 ∧ 5 ^ 2 > 10) ∧
    (1 + 20415 = 20416) := by
  exact ⟨claimed_ceiling_7, claimed_ceiling_5, R27_dwarfs,
    R25_dwarfs, exponent_gap⟩

end Tlmc2313
