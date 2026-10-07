import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.End
import Mathlib.Tactic

/-!
Literal counterexample to TLMC conjecture 00000001952 at rank one.

The source conjecture does not restrict `n` to be at least two or three.
At `n = 1`, its displayed value is zero, whereas subgroup indices in the
actual outer automorphism group are positive.  We define `Out(F_n)` as the
quotient of the actual automorphism group of `FreeGroup (Fin n)` by the range
of its conjugation homomorphism.
-/

namespace TLMC1952

/-- The free group `F_n` on the finite set `Fin n`. -/
abbrev F (n : ℕ) := FreeGroup (Fin n)

/-- Conjugation as a homomorphism from a group to its automorphism group. -/
abbrev innerMap (G : Type*) [Group G] : G →* MulAut G := MulAut.conj

/-- The subgroup of actual inner automorphisms, defined as the range of
conjugation. -/
def InnerAut (G : Type*) [Group G] : Subgroup (MulAut G) := (innerMap G).range

theorem conj_innerAut (G : Type*) [Group G] (f : MulAut G) (g : G) :
    MulAut.conj f (MulAut.conj g) = MulAut.conj (f g) := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- The range of conjugation is normal in the full automorphism group. -/
instance innerAut_normal (G : Type*) [Group G] : (InnerAut G).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro f
  apply le_antisymm
  · rintro φ ⟨ψ, hψ, hφ⟩
    change ψ ∈ (innerMap G).range at hψ
    rcases hψ with ⟨g, rfl⟩
    refine ⟨f g, ?_⟩
    calc
      MulAut.conj (f g) = MulAut.conj f (MulAut.conj g) := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      _ = φ := by simpa [innerMap] using hφ
  · rintro φ hφ
    change φ ∈ (innerMap G).range at hφ
    rcases hφ with ⟨g, rfl⟩
    refine ⟨MulAut.conj (f⁻¹ g), ?_, ?_⟩
    · exact ⟨f⁻¹ g, rfl⟩
    · simpa using conj_innerAut G f (f⁻¹ g)

/-- The outer automorphism group is `Aut(G)` modulo the actual inner
automorphism subgroup. -/
abbrev Out (G : Type*) [Group G] := MulAut G ⧸ InnerAut G

/-- The rank-one free group from the competition statement. -/
abbrev F1 := F 1

/-- The actual group `Out(F_1)`. -/
abbrev OutF1 := Out F1

/-- The displayed value `2^n * choose(n,2)` at `n = 1`. -/
def ClaimedValueAtOne : ℕ := 2 ^ 1 * Nat.choose 1 2

/-- A finite-index subgroup is a subgroup whose actual quotient is finite,
expressed by the equivalent nonzero-index condition from Mathlib. -/
def IsFiniteIndexSubgroup {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  H.index ≠ 0

theorem finiteIndex_iff_finiteQuotient {G : Type*} [Group G] (H : Subgroup G) :
    IsFiniteIndexSubgroup H ↔ Finite (G ⧸ H) := by
  simpa [IsFiniteIndexSubgroup] using (Subgroup.index_ne_zero_iff_finite (H := H))

/-- `m` is the minimum finite subgroup index when it is attained and no
finite-index subgroup has smaller index. -/
def IsMinimumFiniteIndex (G : Type*) [Group G] (m : ℕ) : Prop :=
  (∃ H : Subgroup G, IsFiniteIndexSubgroup H ∧ H.index = m) ∧
    ∀ H : Subgroup G, IsFiniteIndexSubgroup H → m ≤ H.index

/-- The corresponding minimum if the phrase “finite-index subgroup” is read
as “proper finite-index subgroup”. -/
def IsMinimumProperFiniteIndex (G : Type*) [Group G] (m : ℕ) : Prop :=
  (∃ H : Subgroup G, H ≠ ⊤ ∧ IsFiniteIndexSubgroup H ∧ H.index = m) ∧
    ∀ H : Subgroup G, H ≠ ⊤ → IsFiniteIndexSubgroup H → m ≤ H.index

theorem claimed_value_at_one_zero : ClaimedValueAtOne = 0 := by
  norm_num [ClaimedValueAtOne]

theorem finite_index_is_positive {G : Type*} [Group G] (H : Subgroup G)
    (hH : IsFiniteIndexSubgroup H) : 0 < H.index := Nat.pos_of_ne_zero hH

theorem whole_group_index_one {G : Type*} [Group G] :
    IsFiniteIndexSubgroup (⊤ : Subgroup G) ∧ (⊤ : Subgroup G).index = 1 := by
  constructor
  · simp [IsFiniteIndexSubgroup]
  · simp

/-- Under the literal definition that allows the whole group, the actual
minimum finite index of `Out(F_1)` is 1. -/
theorem outF1_minimum_index_is_one : IsMinimumFiniteIndex OutF1 1 := by
  constructor
  · exact ⟨⊤, whole_group_index_one.1, whole_group_index_one.2⟩
  · intro H hH
    exact Nat.one_le_iff_ne_zero.mpr hH

/-- The rank-one instance of the conjectured minimum-index formula is false
for the actual outer automorphism group, not merely for a numeric proxy. -/
theorem conjecture_01952_false_at_one :
    ¬ ∃ m : ℕ, IsMinimumFiniteIndex OutF1 m ∧ m = ClaimedValueAtOne := by
  rintro ⟨m, hmin, hval⟩
  have hm : m = 1 := by
    rcases hmin.1 with ⟨H, hH, hindex⟩
    have hpos : 0 < m := by
      rw [← hindex]
      exact finite_index_is_positive H hH
    have hle : m ≤ 1 := by simpa using hmin.2 ⊤ whole_group_index_one.1
    have hge : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos)
    exact Nat.le_antisymm hle hge
  rw [hm, claimed_value_at_one_zero] at hval
  omega

/-- Even if only proper subgroups are included in the minimum, a minimum
attaining the rank-one displayed value 0 is impossible: every finite index is
positive in the actual quotient group. -/
theorem conjecture_01952_false_at_one_proper :
    ¬ ∃ m : ℕ, IsMinimumProperFiniteIndex OutF1 m ∧ m = ClaimedValueAtOne := by
  rintro ⟨m, hmin, hval⟩
  rcases hmin.1 with ⟨H, hproper, hfinite, hindex⟩
  have hpos : 0 < H.index := finite_index_is_positive H hfinite
  have hposm : 0 < m := by simpa [hindex] using hpos
  rw [claimed_value_at_one_zero] at hval
  omega

end TLMC1952

#print axioms TLMC1952.innerAut_normal
#print axioms TLMC1952.finiteIndex_iff_finiteQuotient
#print axioms TLMC1952.outF1_minimum_index_is_one
#print axioms TLMC1952.conjecture_01952_false_at_one
#print axioms TLMC1952.conjecture_01952_false_at_one_proper
