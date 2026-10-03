import Std

/-! The modulus 1 is expressly included by the positive-integer hypothesis.
    The counterexample works for EVERY sequence of natural numbers, hence in
    particular for the genuine partition-counting function, with no assumption
    or finite approximation to its infinitely many values. -/
namespace Conjecture7680

def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

noncomputable def distinctPrimeFactorCount (m : Nat) : Nat := by
  classical
  exact ((List.range (m+1)).filter (fun p => decide (Prime p ∧ p ∣ m))).length

def Congruence (p : Nat → Nat) (a b m : Nat) : Prop :=
  ∀ n : Nat, p (a*n+b) % m = 0

noncomputable def residueCount (p : Nat → Nat) (a m : Nat) : Nat := by
  classical
  exact ((List.finRange a).filter (fun b => decide (Congruence p a b.val m))).length

/-- Also accommodate the opening phrase that requires b itself to be positive. -/
noncomputable def positiveResidueCount (p : Nat → Nat) (a m : Nat) : Nat := by
  classical
  exact ((List.finRange a).filter
    (fun b => decide (0 < b.val ∧ Congruence p a b.val m))).length

theorem every_sequence_mod_one (p : Nat → Nat) (a b : Nat) :
    Congruence p a b 1 := by
  intro n
  exact Nat.mod_one _

theorem one_has_no_prime_divisors :
    ¬ ∃ p : Nat, Prime p ∧ p ∣ 1 := by
  rintro ⟨p, hp, hd⟩
  have heq := Nat.dvd_one.mp hd
  have hge := hp.1
  omega

theorem omega_one : distinctPrimeFactorCount 1 = 0 := by
  classical
  have hn (p : Nat) : ¬ (Prime p ∧ p ∣ 1) := by
    intro h
    exact one_has_no_prime_divisors ⟨p, h⟩
  have heq : (fun p => decide (Prime p ∧ p ∣ 1)) = (fun _ => false) := by
    funext p
    simp only [hn p, decide_false]
  unfold distinctPrimeFactorCount
  rw [heq]
  decide

theorem actual_residue_count (p : Nat → Nat) : residueCount p 2 1 = 2 := by
  classical
  simp only [residueCount, every_sequence_mod_one, decide_true]
  decide

theorem actual_positive_residue_count (p : Nat → Nat) :
    positiveResidueCount p 2 1 = 1 := by
  classical
  simp [positiveResidueCount, every_sequence_mod_one, List.finRange_succ,
    List.finRange_zero]

/-- The exact-count clause, conditional on (a,m) admitting a valid positive b.
    Any restriction on prime divisors of m is vacuous at m=1. -/
def CountAssertion (p : Nat → Nat) : Prop :=
  ∀ a m : Nat, 0 < a → 0 < m →
    (∃ b : Nat, 0 < b ∧ b < a ∧ Congruence p a b m) →
    residueCount p a m = distinctPrimeFactorCount m

def PositiveCountAssertion (p : Nat → Nat) : Prop :=
  ∀ a m : Nat, 0 < a → 0 < m →
    (∃ b : Nat, 0 < b ∧ b < a ∧ Congruence p a b m) →
    positiveResidueCount p a m = distinctPrimeFactorCount m

theorem conjecture7680_counterexample (p : Nat → Nat) :
    ¬ CountAssertion p ∧ ¬ PositiveCountAssertion p := by
  have admissible : ∃ b : Nat, 0 < b ∧ b < 2 ∧ Congruence p 2 b 1 :=
    ⟨1, by decide, by decide, every_sequence_mod_one p 2 1⟩
  constructor
  · intro h
    have hf := h 2 1 (by decide) (by decide) admissible
    rw [actual_residue_count, omega_one] at hf
    contradiction
  · intro h
    have hf := h 2 1 (by decide) (by decide) admissible
    rw [actual_positive_residue_count, omega_one] at hf
    contradiction

end Conjecture7680
#print axioms Conjecture7680.conjecture7680_counterexample
