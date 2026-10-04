import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.NormNum

namespace Conjecture747

/-- The exact power map on the ring of p-adic integers. -/
noncomputable def powerMap (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) : ℤ_[p] := x ^ p

/-- Fixed by a positive iterate of the actual power map. -/
def iterativeFixed (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) : Prop :=
  ∃ n : ℕ, 0 < n ∧ (powerMap p)^[n] x = x

/-- The direct fixed-point restriction, under the usual prime convention for Z_p. -/
def directFixedPointClaim : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
    ∀ x : ℤ_[p], powerMap p x = x → x = 0 ∨ x = 1

/-- The conjecture's restriction for fixed points of positive iterates. -/
def iterativeFixedPointClaim : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
    ∀ x : ℤ_[p], iterativeFixed p x → x = 0 ∨ x = 1

/-- Characteristic zero distinguishes -1 from both advertised points. -/
theorem neg_one_distinct (p : ℕ) [Fact p.Prime] :
    (-1 : ℤ_[p]) ≠ 0 ∧ (-1 : ℤ_[p]) ≠ 1 := by
  constructor <;> norm_num

/-- Every prime at least five is odd, so -1 is already a direct fixed point. -/
theorem neg_one_fixed (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    powerMap p (-1) = (-1 : ℤ_[p]) := by
  unfold powerMap
  exact (hp.out.odd_of_ne_two (by intro h; subst p; norm_num at hp5)).neg_one_pow

/-- In fact -1 is fixed by every iterate, not merely one positive iterate. -/
theorem neg_one_fixed_every_iterate (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (n : ℕ) :
    (powerMap p)^[n] (-1) = (-1 : ℤ_[p]) :=
  Function.iterate_fixed (neg_one_fixed p hp5) n

theorem neg_one_iterativeFixed (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    iterativeFixed p (-1) :=
  ⟨1, by norm_num, neg_one_fixed_every_iterate p hp5 1⟩

/-- A counterexample exists in the actual p-adic integers for every allowed prime. -/
theorem counterexample_every_prime (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∃ x : ℤ_[p], x ≠ 0 ∧ x ≠ 1 ∧ powerMap p x = x ∧
      ∀ n : ℕ, (powerMap p)^[n] x = x := by
  refine ⟨-1, (neg_one_distinct p).1, (neg_one_distinct p).2,
    neg_one_fixed p hp5, ?_⟩
  exact neg_one_fixed_every_iterate p hp5

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The fully concrete counterexample in Z_5. -/
theorem concrete_counterexample :
    (-1 : ℤ_[5]) ≠ 0 ∧ (-1 : ℤ_[5]) ≠ 1 ∧
      powerMap 5 (-1) = (-1 : ℤ_[5]) ∧
      ∀ n : ℕ, (powerMap 5)^[n] (-1) = (-1 : ℤ_[5]) := by
  exact ⟨(neg_one_distinct 5).1, (neg_one_distinct 5).2,
    neg_one_fixed 5 (by norm_num), neg_one_fixed_every_iterate 5 (by norm_num)⟩

theorem not_directFixedPointClaim : ¬directFixedPointClaim := by
  intro h
  rcases h 5 (by norm_num) (-1) (neg_one_fixed 5 (by norm_num)) with hzero | hone
  · exact (neg_one_distinct 5).1 hzero
  · exact (neg_one_distinct 5).2 hone

/-- The exact iterative fixed-point claim is false. -/
theorem conjecture747_disproof : ¬iterativeFixedPointClaim := by
  intro h
  rcases h 5 (by norm_num) (-1) (neg_one_iterativeFixed 5 (by norm_num)) with hzero | hone
  · exact (neg_one_distinct 5).1 hzero
  · exact (neg_one_distinct 5).2 hone

end Conjecture747
