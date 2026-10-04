import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Set.Card
import Mathlib.Data.Matrix.Rank
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace MartingaleVertices

abbrev Ω := Fin 2
instance : MeasurableSpace Ω := borel Ω
instance : BorelSpace Ω := ⟨rfl⟩
abbrev Portfolio := Ω → ℝ

def payoff (i x : Ω) : ℝ := if i = x then 1 else 0
def price (_ : Ω) : ℝ := 1/2
def terminal (h : Portfolio) (x : Ω) : ℝ := ∑ i, h i * payoff i x
def cost (h : Portfolio) : ℝ := ∑ i, h i * price i
def payoffMatrix : Matrix Ω Ω ℝ := fun x i => payoff i x

theorem payoff_matrix_identity : payoffMatrix = 1 := by
  ext x i
  simp [payoffMatrix, payoff, Matrix.one_apply, eq_comm]
theorem payoff_rank : payoffMatrix.rank = 2 := by rw [payoff_matrix_identity]; simp

theorem terminal_eq (h : Portfolio) (x : Ω) : terminal h x = h x := by
  simp [terminal, payoff]
theorem cost_eq (h : Portfolio) : cost h = (h 0 + h 1)/2 := by
  simp [cost, price, Fin.sum_univ_two]; ring
theorem complete_market (v : Ω → ℝ) : ∃ h : Portfolio, terminal h = v :=
  ⟨v, funext (terminal_eq v)⟩
theorem bond_replication : terminal (fun _ => 1) = (fun _ => 1) ∧ cost (fun _ => 1) = 1 := by
  constructor
  · funext x; exact terminal_eq _ x
  · norm_num [cost_eq]
theorem no_arbitrage (h : Portfolio) (hc : cost h ≤ 0) (ht : ∀ x, 0 ≤ terminal h x) :
    ∀ x, terminal h x = 0 := by
  simp only [terminal_eq] at ht ⊢
  rw [cost_eq] at hc
  have h0 := ht 0
  have h1 := ht 1
  intro x
  fin_cases x <;> dsimp <;> linarith

def half : ℝ≥0 := ⟨1/2, by norm_num⟩
theorem half_add_half : half + half = 1 := by apply NNReal.eq; norm_num [half]
def rawReference : Measure Ω := half • Measure.dirac 0 + half • Measure.dirac 1
instance reference_probability : IsProbabilityMeasure rawReference where
  measure_univ := by
    simp [rawReference, ENNReal.smul_def, ← ENNReal.coe_add, half_add_half]
def reference : ProbabilityMeasure Ω := ⟨rawReference, inferInstance⟩
def weight (Q : ProbabilityMeasure Ω) : Ω → ℝ := fun x => (Q : Measure Ω).real {x}
def uniform : Ω → ℝ := fun _ => 1/2

theorem reference_weights : weight reference = uniform := by
  funext x
  fin_cases x <;> norm_num [weight, reference, rawReference, uniform, measureReal_def, ENNReal.smul_def, half]

theorem reference_positive (x : Ω) : 0 < weight reference x := by
  rw [reference_weights]
  norm_num [uniform]

-- One-period discounted martingale equations, with trivial initial information.
def MartingaleMeasure (Q : ProbabilityMeasure Ω) : Prop :=
  ∀ i, (∫ x, payoff i x ∂(Q : Measure Ω)) = price i
def EquivalentMartingaleMeasure (Q : ProbabilityMeasure Ω) : Prop :=
  MartingaleMeasure Q ∧ (Q : Measure Ω) ≪ (reference : Measure Ω) ∧
    (reference : Measure Ω) ≪ (Q : Measure Ω)

theorem expectation_eq_weight (Q : ProbabilityMeasure Ω) (i : Ω) :
    (∫ x, payoff i x ∂(Q : Measure Ω)) = weight Q i := by
  have hf : payoff i = ({i} : Set Ω).indicator (fun _ => (1 : ℝ)) := by
    funext x; simp [payoff, eq_comm, Set.indicator]
  rw [hf, integral_indicator_const 1 (measurableSet_singleton i)]
  simp [weight]

theorem weight_injective : Function.Injective weight := by
  intro Q R h
  haveI : IsProbabilityMeasure (Q : Measure Ω) := Q.property
  haveI : IsProbabilityMeasure (R : Measure Ω) := R.property
  apply Subtype.ext
  apply (ext_iff_measureReal_singleton (μ1 := (Q : Measure Ω)) (μ2 := (R : Measure Ω))).mpr
  intro x
  exact congrFun h x

theorem martingale_iff_weights (Q : ProbabilityMeasure Ω) :
    MartingaleMeasure Q ↔ weight Q = uniform := by
  simp only [MartingaleMeasure, expectation_eq_weight, price, uniform, funext_iff]

theorem martingale_unique (Q : ProbabilityMeasure Ω) : MartingaleMeasure Q ↔ Q = reference := by
  rw [martingale_iff_weights, ← reference_weights]
  exact ⟨fun h => weight_injective h, fun h => congrArg weight h⟩

theorem equivalent_martingale_unique (Q : ProbabilityMeasure Ω) :
    EquivalentMartingaleMeasure Q ↔ Q = reference := by
  constructor
  · intro h; exact (martingale_unique Q).mp h.1
  · rintro rfl
    exact ⟨(martingale_unique reference).mpr rfl, Measure.AbsolutelyContinuous.rfl,
      Measure.AbsolutelyContinuous.rfl⟩

-- The full sets of actual probability measures, in their finite mass coordinates.
def martingaleWeights : Set (Ω → ℝ) :=
  {w | ∃ Q : ProbabilityMeasure Ω, MartingaleMeasure Q ∧ weight Q = w}
def equivalentWeights : Set (Ω → ℝ) :=
  {w | ∃ Q : ProbabilityMeasure Ω, EquivalentMartingaleMeasure Q ∧ weight Q = w}

theorem martingale_weights_singleton : martingaleWeights = {uniform} := by
  ext w
  constructor
  · rintro ⟨Q,hQ,rfl⟩
    exact (martingale_iff_weights Q).mp hQ
  · rintro rfl
    exact ⟨reference, (martingale_unique reference).mpr rfl, reference_weights⟩

theorem equivalent_weights_singleton : equivalentWeights = {uniform} := by
  ext w
  constructor
  · rintro ⟨Q,hQ,rfl⟩
    rw [(equivalent_martingale_unique Q).mp hQ, reference_weights]
    exact mem_singleton _
  · rintro rfl
    exact ⟨reference, (equivalent_martingale_unique reference).mpr rfl, reference_weights⟩

theorem extreme_count : (martingaleWeights.extremePoints ℝ).ncard = 1 ∧
    (equivalentWeights.extremePoints ℝ).ncard = 1 := by
  rw [martingale_weights_singleton, equivalent_weights_singleton, extremePoints_singleton]
  simp

theorem count_formula_fails : payoffMatrix.rank = 2 ∧
    (martingaleWeights.extremePoints ℝ).ncard ≠ Fintype.card Ω - payoffMatrix.rank ∧
    (equivalentWeights.extremePoints ℝ).ncard ≠ Fintype.card Ω - payoffMatrix.rank := by
  rw [payoff_rank, extreme_count.1, extreme_count.2]
  norm_num

#print axioms complete_market
#print axioms no_arbitrage
#print axioms expectation_eq_weight
#print axioms martingale_unique
#print axioms equivalent_martingale_unique
#print axioms extreme_count
#print axioms count_formula_fails
end MartingaleVertices
