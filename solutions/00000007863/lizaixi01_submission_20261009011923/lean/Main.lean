import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Exp

open Filter Topology

namespace FullBudgetOracle

noncomputable section

abbrev Ground (n : ℕ) := Fin n

/-- The exact finite set-function class named in the source. -/
structure SourceObjective (n : ℕ) where
  value : Finset (Ground n) → ℝ
  normalized : value ∅ = 0
  monotone : Monotone value
  submodular : ∀ A B,
    value (A ∪ B) + value (A ∩ B) ≤ value A + value B

/-- A nontrivial modular objective witnesses that the source class is nonempty. -/
def cardinalityObjective (n : ℕ) : SourceObjective n where
  value S := (S.card : ℝ)
  normalized := by simp
  monotone := by
    intro A B hAB
    change (A.card : ℝ) ≤ (B.card : ℝ)
    exact_mod_cast Finset.card_le_card hAB
  submodular := by
    intro A B
    apply le_of_eq
    exact_mod_cast Finset.card_union_add_card_inter A B

theorem cardinality_univ_value (n : ℕ) :
    (cardinalityObjective n).value Finset.univ = n := by
  simp [cardinalityObjective]

theorem cardinalityObjective_nonconstant {n : ℕ} (hn : 0 < n) :
    (cardinalityObjective n).value Finset.univ ≠
      (cardinalityObjective n).value ∅ := by
  rw [cardinality_univ_value, (cardinalityObjective n).normalized]
  exact_mod_cast hn.ne'

def feasibleValues {n : ℕ} (f : SourceObjective n) (k : ℕ) : Set ℝ :=
  {y | ∃ S : Finset (Ground n), S.card ≤ k ∧ y = f.value S}

theorem univ_feasible (n : ℕ) : (Finset.univ : Finset (Ground n)).card ≤ n := by
  simp

theorem univ_optimal {n : ℕ} (f : SourceObjective n) :
    IsGreatest (feasibleValues f n) (f.value Finset.univ) := by
  constructor
  · exact ⟨Finset.univ, univ_feasible n, rfl⟩
  · rintro y ⟨S, _hS, rfl⟩
    exact f.monotone (Finset.subset_univ S)

theorem objective_nonnegative {n : ℕ} (f : SourceObjective n)
    (S : Finset (Ground n)) : 0 ≤ f.value S := by
  rw [← f.normalized]
  exact f.monotone (Finset.empty_subset S)

def approximationRatio : ℝ := 1-1/Real.exp 1

theorem ratio_pos : 0 < approximationRatio := by
  have he : 1 < Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hi : 1/Real.exp 1 < 1 := (div_lt_one (Real.exp_pos 1)).2 he
  unfold approximationRatio
  linarith

theorem ratio_le_one : approximationRatio ≤ 1 := by
  unfold approximationRatio
  have : 0 ≤ 1/Real.exp 1 := by positivity
  linarith

theorem approximation_at_univ {n : ℕ} (f : SourceObjective n)
    (S : Finset (Ground n)) :
    approximationRatio*f.value S ≤ f.value Finset.univ := by
  calc
    approximationRatio*f.value S ≤ 1*f.value S :=
      mul_le_mul_of_nonneg_right ratio_le_one (objective_nonnegative f S)
    _ = f.value S := one_mul _
    _ ≤ f.value Finset.univ := f.monotone (Finset.subset_univ S)

/-- A value-query proof syntax: a query consumes its actual oracle answer. -/
inductive ValueProgram (n : ℕ) where
  | ret (S : Finset (Ground n)) : ValueProgram n
  | query (S : Finset (Ground n)) (next : ℝ → ValueProgram n) : ValueProgram n

/-- The interpreter increments query cost only at actual query nodes. -/
def run {n : ℕ} (oracle : Finset (Ground n) → ℝ) :
    ValueProgram n → Finset (Ground n) × ℕ
  | .ret S => (S, 0)
  | .query S next =>
    let result := run oracle (next (oracle S))
    (result.1, result.2+1)

def fullSetProgram (n : ℕ) : ValueProgram n := .ret Finset.univ

theorem fullSet_run {n : ℕ} (oracle : Finset (Ground n) → ℝ) :
    run oracle (fullSetProgram n) = (Finset.univ, 0) := rfl

def ValidApproximation (n k : ℕ) (P : ValueProgram n) : Prop :=
  ∀ f : SourceObjective n,
    (run f.value P).1.card ≤ k ∧
    ∀ S : Finset (Ground n), S.card ≤ k →
      approximationRatio*f.value S ≤ f.value (run f.value P).1

def UniformCostBound (n : ℕ) (P : ValueProgram n) (C : ℝ) : Prop :=
  ∀ f : SourceObjective n, ((run f.value P).2 : ℝ) ≤ C

theorem fullSet_valid (n : ℕ) : ValidApproximation n n (fullSetProgram n) := by
  intro f
  rw [fullSet_run]
  exact ⟨univ_feasible n, fun S _hS => approximation_at_univ f S⟩

theorem fullSet_uniform_zero_cost (n : ℕ) :
    UniformCostBound n (fullSetProgram n) 0 := by
  intro f
  rw [fullSet_run]
  simp

/-- Every admissible protocol would have to incur this cost on some source objective. -/
def UniversalQueryLowerBound (n k : ℕ) (C : ℝ) : Prop :=
  ∀ P : ValueProgram n, ValidApproximation n k P →
    ∃ f : SourceObjective n, C ≤ ((run f.value P).2 : ℝ)

theorem no_positive_full_budget_lower_bound (n : ℕ) (C : ℝ) (hC : 0 < C) :
    ¬ UniversalQueryLowerBound n n C := by
  intro h
  obtain ⟨f, hf⟩ := h (fullSetProgram n) (fullSet_valid n)
  rw [fullSet_run] at hf
  simp only [Nat.cast_zero] at hf
  exact (not_le_of_gt hC) hf

theorem no_eventual_linear_query_lower_bound (c : ℝ) (hc : 0 < c) :
    ¬ ∀ᶠ n : ℕ in atTop, UniversalQueryLowerBound n n (c*(n : ℝ)) := by
  intro hlarge
  obtain ⟨n, hnlarge, hn⟩ := (hlarge.and (eventually_ge_atTop 1)).exists
  have hnpos : 0 < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  exact no_positive_full_budget_lower_bound n _ (mul_pos hc hnpos) hnlarge

/-- A singleton seed has mass one, so a deterministic protocol is a randomized special case. -/
def seedMass (_r : Fin 1) : ℝ := 1

theorem seedMass_nonnegative (r : Fin 1) : 0 ≤ seedMass r := by
  simp [seedMass]

theorem seedMass_normalized : (∑ r : Fin 1, seedMass r) = 1 := by
  simp [seedMass]

def singleSeedProgram {n : ℕ} (P : ValueProgram n) : Fin 1 → ValueProgram n := fun _ => P

/-- Actual finite expectation of interpreter query cost under the normalized seed law. -/
def expectedQueries {n : ℕ} (P : Fin 1 → ValueProgram n) (f : SourceObjective n) : ℝ :=
  ∑ r : Fin 1, seedMass r * ((run f.value (P r)).2 : ℝ)

theorem singleSeed_expected_eq_cost {n : ℕ} (P : ValueProgram n)
    (f : SourceObjective n) :
    expectedQueries (singleSeedProgram P) f = ((run f.value P).2 : ℝ) := by
  simp [expectedQueries, seedMass, singleSeedProgram]

theorem fullSet_expected_zero {n : ℕ} (f : SourceObjective n) :
    expectedQueries (singleSeedProgram (fullSetProgram n)) f = 0 := by
  rw [singleSeed_expected_eq_cost, fullSet_run]
  simp

def UniversalExpectedLowerBound (n k : ℕ) (C : ℝ) : Prop :=
  ∀ P : Fin 1 → ValueProgram n, (∀ r, ValidApproximation n k (P r)) →
    ∃ f : SourceObjective n, C ≤ expectedQueries P f

theorem no_positive_full_budget_expected_lower_bound
    (n : ℕ) (C : ℝ) (hC : 0 < C) :
    ¬ UniversalExpectedLowerBound n n C := by
  intro h
  obtain ⟨f, hf⟩ := h (singleSeedProgram (fullSetProgram n)) (fun _ => fullSet_valid n)
  rw [fullSet_expected_zero] at hf
  exact (not_le_of_gt hC) hf

theorem no_eventual_linear_expected_lower_bound (c : ℝ) (hc : 0 < c) :
    ¬ ∀ᶠ n : ℕ in atTop, UniversalExpectedLowerBound n n (c*(n : ℝ)) := by
  intro hlarge
  obtain ⟨n, hnlarge, hn⟩ := (hlarge.and (eventually_ge_atTop 1)).exists
  have hnpos : 0 < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  exact no_positive_full_budget_expected_lower_bound n _ (mul_pos hc hnpos) hnlarge

theorem all_objective_full_budget_certificate (n : ℕ) :
    (∀ f : SourceObjective n,
      IsGreatest (feasibleValues f n) (f.value Finset.univ)) ∧
    ValidApproximation n n (fullSetProgram n) ∧
    UniformCostBound n (fullSetProgram n) 0 :=
  ⟨univ_optimal, fullSet_valid n, fullSet_uniform_zero_cost n⟩

/-- A premise-free uniform witness against the necessary unrestricted-budget lower bound. -/
theorem full_budget_counterexample :
    (∀ n : ℕ, (Finset.univ : Finset (Ground n)).card = n) ∧
    (∀ n : ℕ, (cardinalityObjective n).value Finset.univ = n) ∧
    (∀ n : ℕ, 0 < n → (cardinalityObjective n).value Finset.univ ≠
      (cardinalityObjective n).value ∅) ∧
    0 < approximationRatio ∧ approximationRatio ≤ 1 ∧
    (∀ r : Fin 1, 0 ≤ seedMass r) ∧ (∑ r : Fin 1, seedMass r) = 1 ∧
    (∀ n : ℕ, ValidApproximation n n (fullSetProgram n) ∧
      UniformCostBound n (fullSetProgram n) 0 ∧
      ∀ f : SourceObjective n,
        (run f.value (fullSetProgram n)).1.card ≤ n ∧
        IsGreatest (feasibleValues f n) (f.value (run f.value (fullSetProgram n)).1) ∧
        run f.value (fullSetProgram n) = (Finset.univ, 0) ∧
        expectedQueries (singleSeedProgram (fullSetProgram n)) f = 0) ∧
    (∀ c : ℝ, 0 < c →
      ¬ ∀ᶠ n : ℕ in atTop, UniversalExpectedLowerBound n n (c*(n : ℝ))) := by
  refine ⟨?_, cardinality_univ_value, fun _ hn => cardinalityObjective_nonconstant hn,
    ratio_pos, ratio_le_one, seedMass_nonnegative, seedMass_normalized, ?_,
    no_eventual_linear_expected_lower_bound⟩
  · intro n
    simp
  · intro n
    refine ⟨fullSet_valid n, fullSet_uniform_zero_cost n, ?_⟩
    intro f
    rw [fullSet_run]
    exact ⟨univ_feasible n, univ_optimal f, rfl, fullSet_expected_zero f⟩

#print axioms full_budget_counterexample

end
end FullBudgetOracle
