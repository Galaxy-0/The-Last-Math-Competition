import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum

/-!
# A finite-group counterexample to TLMC 00000002320

The conjecture quantifies over all finite groups, not merely two-generated groups.
We use the elementary abelian group of order eight.  The generating relation is
mathlib's actual `Subgroup.closure`, and the probability counts ordered pairs
sampled independently and uniformly, with replacement.

All finite checks below use kernel-checked `decide`, never `native_decide`.
-/

namespace Counterexample2320

abbrev G := Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)

/-- The at-most-four possible words in two elements of an elementary abelian
2-group.  This predicate is subsequently proved to define a genuine subgroup. -/
def inFour (a b x : G) : Prop :=
  x = 1 ∨ x = a ∨ x = b ∨ x = a * b

instance (a b x : G) : Decidable (inFour a b x) := by
  unfold inFour
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem four_mul_closed :
    ∀ a b x y : G, inFour a b x → inFour a b y → inFour a b (x * y) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem four_inv_closed :
    ∀ a b x : G, inFour a b x → inFour a b x⁻¹ := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem four_misses_element : ∀ a b : G, ∃ x : G, ¬ inFour a b x := by
  decide

def fourSubgroup (a b : G) : Subgroup G where
  carrier := {x | inFour a b x}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    exact four_mul_closed a b x y hx hy
  inv_mem' := by
    intro x hx
    exact four_inv_closed a b x hx

theorem pair_closure_le_four (a b : G) :
    Subgroup.closure ({a, b} : Set G) ≤ fourSubgroup a b := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  change inFour a b x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))

theorem no_pair_generates (a b : G) :
    Subgroup.closure ({a, b} : Set G) ≠ ⊤ := by
  intro h
  obtain ⟨x, hx⟩ := four_misses_element a b
  apply hx
  have hxclosure : x ∈ Subgroup.closure ({a, b} : Set G) := by
    rw [h]
    trivial
  change x ∈ fourSubgroup a b
  exact pair_closure_le_four a b hxclosure

/- Ordered pairs generating the entire group in the standard group-theoretic
sense.  Classical decidability is used only to express the finite subset. -/
open Classical in
noncomputable def generatingPairs (H : Type*) [Group H] [Fintype H] : Finset (H × H) :=
  Finset.univ.filter (fun p => Subgroup.closure ({p.1, p.2} : Set H) = ⊤)

/-- The exact rational probability for two uniform independent draws from H.
This is N₂(H)/|H|², the standard finite counting definition. -/
noncomputable def generatingPairProbability (H : Type*) [Group H] [Fintype H] : ℚ :=
  (generatingPairs H).card / (Fintype.card H : ℚ) ^ 2

theorem group_order : Fintype.card G = 8 := by decide

theorem ordered_pair_count : Fintype.card (G × G) = 64 := by decide

theorem generatingPairs_empty : generatingPairs G = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro p _hp
  exact no_pair_generates p.1 p.2

theorem generatingPairProbability_zero : generatingPairProbability G = 0 := by
  simp [generatingPairProbability, generatingPairs_empty]

/-- A necessary consequence of the asserted spectrum being a subset of [1/4,1].
Refuting this consequence refutes the original conjunctive conjecture; no claim
about the separate PSL(2,p) limit is required. -/
def conjectureInterval : Prop :=
  ∀ (H : Type) [Group H] [Fintype H],
    (1 / 4 : ℚ) ≤ generatingPairProbability H ∧ generatingPairProbability H ≤ 1

theorem conjectureInterval_false : ¬ conjectureInterval := by
  intro h
  have hG := (h G).1
  rw [generatingPairProbability_zero] at hG
  norm_num at hG

theorem counterexample :
    Fintype.card G = 8 ∧ generatingPairProbability G = 0 ∧
      ¬ ((1 / 4 : ℚ) ≤ generatingPairProbability G) := by
  refine ⟨group_order, generatingPairProbability_zero, ?_⟩
  rw [generatingPairProbability_zero]
  norm_num

end Counterexample2320
