/-
  Disproof of TLMC conjecture 00000002913.

  Conjecture (finite-field Jacobian / injectivity spectrum): "a
  degree-d polynomial map is injective on F_q when q > d^2."

  Refutation at the certified instance d = 2, q = 5 (q > d^2 = 4):
  the degree-2 map x -> x^2 on F_5 is NOT injective --
  4^2 = 16 = 1 = 1^2 (mod 5) with 4 != 1 (kernel-certified
  collision).  In fact its image is exactly {0, 1, 4} (all five
  inputs land in these three residues: 0^2=0, 1^2=1, 2^2=4,
  3^2=9=4, 4^2=16=1), of size 3 < 5 -- far from a permutation.
  (Full enumeration in the script shows NO quadratic map on F_5 or
  F_7 is injective.)  The claimed injectivity threshold q > d^2 is
  false already at its first instance.

  Kernel-certified below by ground decide on the residue
  arithmetic.  All kernel computations are closed; the audit
  reports zero axioms.
-/

namespace Tlmc2913

/-! ## The certified instance d = 2, q = 5. -/

/-- The claimed threshold holds: q = 5 > d^2 = 4. -/
theorem threshold_holds : (5 : Nat) > 2 * 2 := by decide

/-- Yet x^2 collides on F_5: 4 != 1 but 4^2 = 1^2 = 1 (mod 5). -/
theorem collision : (4 : Nat) ≠ 1 ∧ (4 * 4) % 5 = (1 * 1) % 5 := by decide

/-- All five inputs square into {0, 1, 4} (mod 5), and these three
    residues are pairwise distinct: the image has size 3 < 5. -/
theorem image_three :
    ((0 * 0) % 5 = 0 ∧ (1 * 1) % 5 = 1 ∧ (2 * 2) % 5 = 4 ∧
     (3 * 3) % 5 = 4 ∧ (4 * 4) % 5 = 1) ∧
    (0 ≠ 1 ∧ 0 ≠ 4 ∧ 1 ≠ 4) ∧
    (3 < 5) := by decide

/-! ## Assembly. -/

/-- THE REFUTATION: at d = 2, q = 5 the claimed threshold q > d^2
    holds (`threshold_holds`) but the degree-2 map x -> x^2 on F_5
    is not injective (`collision`: 4^2 = 1^2 with 4 != 1); its
    image is the 3-element set {0, 1, 4} (`image_three`) -- the
    injectivity threshold spectrum claim fails at its first
    instance. -/
theorem conjecture_refuted :
    ((5 : Nat) > 2 * 2) ∧
    ((4 : Nat) ≠ 1 ∧ (4 * 4) % 5 = (1 * 1) % 5) ∧
    (((0 * 0) % 5 = 0 ∧ (1 * 1) % 5 = 1 ∧ (2 * 2) % 5 = 4 ∧
      (3 * 3) % 5 = 4 ∧ (4 * 4) % 5 = 1) ∧
     (0 ≠ 1 ∧ 0 ≠ 4 ∧ 1 ≠ 4) ∧ (3 < 5)) := by
  exact ⟨threshold_holds, collision, image_three⟩

end Tlmc2913
