import Mathlib.Algebra.AlgebraicCard
import Mathlib.Data.Real.Cardinality
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# A necessary clause of conjecture 00000009700 is false

Conventions: sets of real numbers, algebraic independence and transcendence over
the rationals, and the standard metric on the real line. Neither the real ambient
space nor the rational ground field is literally named in the bilingual source;
these are the declared ordinary number-theoretic conventions of this result.

The source asserts Hausdorff dimension one for every algebraically independent
set of transcendental numbers. It imposes no cardinality or maximality condition.
The counterexample below is nonempty: a singleton of a transcendental real.

`HausdorffClause` retains the exact universal quantifier and both hypotheses of
that necessary clause. The independence map is the inclusion of the set itself.
`dimH` is Mathlib's Hausdorff-measure-based dimension, not a new invariant.

No meaning is assigned to the undefined box-dimension-spectrum phrase. The last
two theorems record the logical obstruction to any conjunction, or any statement,
that implies the necessary Hausdorff clause with this same domain.
-/

namespace Conjecture9700

/-- The precise first necessary clause, under the declared real/rational convention. -/
def HausdorffClause : Prop :=
  ∀ S : Set ℝ,
    AlgebraicIndependent ℚ ((↑) : S → ℝ) →
    (∀ x ∈ S, Transcendental ℚ x) →
    dimH S = 1

/-- Algebraic reals are countable, whereas the full real line is uncountable. -/
theorem exists_transcendental_real : ∃ x : ℝ, Transcendental ℚ x := by
  classical
  by_contra h
  push_neg at h
  apply Cardinal.not_countable_real
  apply (Algebraic.countable ℚ ℝ).mono
  intro x _
  exact not_not.mp (h x)

/-- For an actual singleton set, independence of its inclusion is transcendence. -/
theorem singleton_independent_iff (x : ℝ) :
    AlgebraicIndependent ℚ ((↑) : ({x} : Set ℝ) → ℝ) ↔ Transcendental ℚ x :=
  algebraicIndependent_singleton_iff (⟨x, Set.mem_singleton x⟩ : ({x} : Set ℝ))

/-- Every member of the singleton is transcendental when its unique member is. -/
theorem singleton_members_transcendental (x : ℝ) (hx : Transcendental ℚ x) :
    ∀ y ∈ ({x} : Set ℝ), Transcendental ℚ y := by
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  exact hy ▸ hx

/-- The standard metric Hausdorff dimension of this singleton is zero. -/
theorem singleton_dimension_zero (x : ℝ) : dimH ({x} : Set ℝ) = 0 :=
  dimH_singleton x

/-- The counterexample is a genuine nonempty set satisfying both source hypotheses. -/
theorem exists_nonempty_counterexample :
    ∃ S : Set ℝ, S.Nonempty ∧
      AlgebraicIndependent ℚ ((↑) : S → ℝ) ∧
      (∀ x ∈ S, Transcendental ℚ x) ∧
      dimH S = 0 ∧ dimH S ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_transcendental_real
  refine ⟨{x}, Set.singleton_nonempty x, (singleton_independent_iff x).mpr hx,
    singleton_members_transcendental x hx, singleton_dimension_zero x, ?_⟩
  rw [singleton_dimension_zero]
  exact zero_ne_one

/-- Main result: the source's necessary universal Hausdorff clause is false. -/
theorem hausdorff_clause_false : ¬ HausdorffClause := by
  intro h
  obtain ⟨S, _, hS, ht, _, hd⟩ := exists_nonempty_counterexample
  exact hd (h S hS ht)

/-- Pure conjunction elimination, independent of any interpretation of later claims. -/
theorem conjunction_implies_hausdorff_clause (P : Set ℝ → Prop)
    (h : ∀ S : Set ℝ,
      AlgebraicIndependent ℚ ((↑) : S → ℝ) →
      (∀ x ∈ S, Transcendental ℚ x) → dimH S = 1 ∧ P S) :
    HausdorffClause := by
  intro S hS ht
  exact (h S hS ht).1

/-- Every such conjunctive assertion fails, regardless of its further conjunct. -/
theorem universal_conjunction_false (P : Set ℝ → Prop) :
    ¬ (∀ S : Set ℝ,
      AlgebraicIndependent ℚ ((↑) : S → ℝ) →
      (∀ x ∈ S, Transcendental ℚ x) → dimH S = 1 ∧ P S) := by
  intro h
  exact hausdorff_clause_false (conjunction_implies_hausdorff_clause P h)

/-- Any larger statement entailing this necessary clause is false. -/
theorem not_statement_implying_hausdorff_clause (P : Prop)
    (h : P → HausdorffClause) : ¬ P :=
  fun hP => hausdorff_clause_false (h hP)

end Conjecture9700
