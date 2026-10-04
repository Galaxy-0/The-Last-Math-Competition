import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.NormNum

namespace PerfectDifferenceObstruction

-- Standard positive-exponent prime-power condition.
def PrimePower (n : ℕ) : Prop :=
  ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ p ^ k = n

theorem two_prime_power : PrimePower 2 := by
  exact ⟨2, 1, Nat.prime_two, by norm_num, by norm_num⟩

variable {G : Type*} [Group G]

-- All parameter conditions and the actual ordered-difference uniqueness.
-- For g ≠ 1, a*b⁻¹=g automatically forces a ≠ b.
def SingerDifferenceSet (n : ℕ) (D : Finset G) : Prop :=
  Nat.card G = n ^ 2 + n + 1 ∧
  D.card = n + 1 ∧
  ∀ g : G, g ≠ 1 →
    ∃! pair : G × G, pair.1 ∈ D ∧ pair.2 ∈ D ∧ pair.1 * pair.2⁻¹ = g

-- The prime-cardinality theorem is about the actual ambient group.
theorem singer_two_forces_cyclic (D : Finset G) (hD : SingerDifferenceSet 2 D) :
    IsCyclic G := by
  have hcard : Nat.card G = 7 := by simpa [SingerDifferenceSet] using hD.1
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact isCyclic_of_prime_card hcard

theorem no_noncyclic_realization (hG : ¬ IsCyclic G) :
    ¬ ∃ D : Finset G, SingerDifferenceSet 2 D := by
  rintro ⟨D, hD⟩
  exact hG (singer_two_forces_cyclic D hD)

-- In particular, this excludes every noncyclic abelian group.
theorem no_noncyclic_abelian_realization {A : Type*} [CommGroup A]
    (hA : ¬ IsCyclic A) : ¬ ∃ D : Finset A, SingerDifferenceSet 2 D :=
  no_noncyclic_realization hA

-- A universal necessary-condition obstruction disproves the sufficiency at n=2.
theorem prime_power_not_sufficient {A : Type*} [CommGroup A]
    (hA : ¬ IsCyclic A) :
    PrimePower 2 ∧ ¬ ∃ D : Finset A, SingerDifferenceSet 2 D :=
  ⟨two_prime_power, no_noncyclic_abelian_realization hA⟩

-- The existential statement ranges over all abelian ambient groups.
def NoncyclicAbelianRealizable (n : ℕ) : Prop :=
  ∃ (A : Type) (inst : CommGroup A),
    letI := inst
    (¬ IsCyclic A) ∧ ∃ D : Finset A, SingerDifferenceSet n D

theorem no_ambient_group_realization : ¬ NoncyclicAbelianRealizable 2 := by
  rintro ⟨A, inst, hA, D, hD⟩
  letI : CommGroup A := inst
  exact hA (singer_two_forces_cyclic D hD)

theorem counterexample : PrimePower 2 ∧ ¬ NoncyclicAbelianRealizable 2 :=
  ⟨two_prime_power, no_ambient_group_realization⟩

-- Independent check of the claimed dihedral group-order exception.
theorem no_dihedral_order_twenty_one (m : ℕ) :
    Nat.card (DihedralGroup m) ≠ 21 := by
  rw [DihedralGroup.nat_card]
  omega

#print axioms two_prime_power
#print axioms singer_two_forces_cyclic
#print axioms no_noncyclic_abelian_realization
#print axioms prime_power_not_sufficient
#print axioms counterexample
#print axioms no_dihedral_order_twenty_one

end PerfectDifferenceObstruction
