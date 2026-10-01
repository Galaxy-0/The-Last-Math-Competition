import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-!
Conjecture 00000000127 is true AS WRITTEN: no upper bound on d is imposed.
Choose d = p. This is not a claim about nontrivial residue representatives
of exponents modulo p - 1.
-/

namespace TLMC127

theorem complete_mapping_as_written (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∃ d : ℕ, d ≠ 1 ∧ d ≠ p - 2 ∧
      Function.Bijective (fun x : ZMod p => x ^ d) ∧
      Function.Bijective (fun x : ZMod p => x ^ d + x) := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  refine ⟨p, by omega, by omega, ?_, ?_⟩
  · simp [ZMod.pow_card]
  · simpa [ZMod.pow_card, ← two_mul, Equiv.mulLeft₀] using
      (Equiv.mulLeft₀ (2 : ZMod p) htwo).bijective

#print axioms complete_mapping_as_written

end TLMC127
