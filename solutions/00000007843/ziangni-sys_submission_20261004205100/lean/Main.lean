import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.List.FinRange
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
open Set MeasureTheory Filter Topology
namespace CompleteGreedy
open scoped ENNReal

-- Standard greedy scan: add an unchosen vertex exactly when no chosen vertex is adjacent.
def step {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (v : V) : Finset V :=
  if v ∉ s ∧ ∀ w ∈ s, ¬G.Adj v w then insert v s else s

def greedy {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (l : List V) (s : Finset V) : Finset V := l.foldl (step G) s

theorem singleton_fixed {V : Type*} [DecidableEq V] (a v : V) :
    step (⊤ : SimpleGraph V) {a} v = {a} := by
  by_cases h : v=a
  · subst v; simp [step]
  · simp [step,SimpleGraph.top_adj,h]

theorem scan_singleton {V : Type*} [DecidableEq V] (l : List V) (a : V) :
    greedy (⊤ : SimpleGraph V) l {a} = {a} := by
  induction l with
  | nil => rfl
  | cons v l ih => simpa [greedy,List.foldl_cons,singleton_fixed] using ih

theorem scan_nonempty {V : Type*} [DecidableEq V] (a : V) (l : List V) :
    greedy (⊤ : SimpleGraph V) (a::l) ∅ = {a} := by
  simpa [greedy,List.foldl_cons,step] using scan_singleton l a

abbrev graph (d : ℕ) : SimpleGraph (Fin (d+1)) := ⊤

theorem degree_regular (d : ℕ) : (graph d).IsRegularOfDegree d := by
  simpa [graph] using (SimpleGraph.IsRegularOfDegree.top (V := Fin (d+1)))

abbrev Orders (d : ℕ) := Equiv.Perm (Fin (d+1))

def order (d : ℕ) (p : Orders d) : List (Fin (d+1)) := (List.finRange (d+1)).map p

theorem genuine_order (d : ℕ) (p : Orders d) : (order d p).Perm (List.finRange (d+1)) :=
  p.map_finRange_perm

def output (d : ℕ) (p : Orders d) : Finset (Fin (d+1)) := greedy (graph d) (order d p) ∅

theorem actual_output (d : ℕ) (p : Orders d) : output d p = {p 0} := by
  simp only [output,graph,order,List.finRange_succ_eq_map,List.map_cons]
  exact scan_nonempty _ _

theorem independent_output (d : ℕ) (p : Orders d) :
    (graph d).IsIndepSet (output d p : Set (Fin (d+1))) := by
  rw [actual_output,SimpleGraph.isIndepSet_iff]
  simp

def size (d : ℕ) (p : Orders d) : ℝ := (output d p).card

theorem size_one (d : ℕ) (p : Orders d) : size d p = 1 := by
  simp [size,actual_output]

instance (d : ℕ) : MeasurableSpace (Orders d) := ⊤
instance (d : ℕ) : MeasurableSingletonClass (Orders d) := ⟨fun _ => trivial⟩

-- Actual uniform law on all permutations, with equal reciprocal-cardinality probabilities.
def law (d : ℕ) : PMF (Orders d) := PMF.ofFintype
  (fun _ => (Fintype.card (Orders d) : ℝ≥0∞)⁻¹) (by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp))

def mu (d : ℕ) : Measure (Orders d) := (law d).toMeasure
instance (d : ℕ) : IsProbabilityMeasure (mu d) :=
  inferInstanceAs (IsProbabilityMeasure (law d).toMeasure)

theorem uniform_mass (d : ℕ) (p : Orders d) : law d p = (Fintype.card (Orders d) : ℝ≥0∞)⁻¹ := rfl

def expectedSize (d : ℕ) : ℝ := ∫ p, size d p ∂mu d

theorem expectation_one (d : ℕ) : expectedSize d = 1 := by
  simp [expectedSize,size_one]

theorem almost_sure_one (d : ℕ) : mu d {p | size d p = 1} = 1 := by
  simp [size_one]

def benchmark (d : ℕ) : ℝ := ((d:ℝ)+1)*Real.log d / ((d:ℝ)+Real.log d)

theorem benchmark_lower (d : ℕ) (hd : 2 ≤ d) : Real.log d / 2 ≤ benchmark d := by
  have hdreal : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hl : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg (by linarith)
  have hle : Real.log (d:ℝ) ≤ d := Real.log_le_self (by linarith)
  have hp : 0 < (d:ℝ)+Real.log d := by linarith
  unfold benchmark
  apply (le_div_iff₀ hp).2
  nlinarith [mul_le_mul_of_nonneg_right hle hl]

theorem benchmark_diverges : Tendsto benchmark atTop atTop := by
  have hlog : Tendsto (fun d : ℕ => Real.log (d:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.2
  intro b
  filter_upwards [hlog.eventually (eventually_ge_atTop (2*b)),eventually_ge_atTop 2] with d hb hd
  have hlo := benchmark_lower d hd
  linarith

def relativeSize (d : ℕ) : ℝ := expectedSize d / benchmark d

theorem relative_limit_zero : Tendsto relativeSize atTop (𝓝 0) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).div_atTop benchmark_diverges
  change Tendsto (fun d => expectedSize d / benchmark d) atTop (𝓝 0)
  simpa only [expectation_one] using h

theorem claimed_relative_asymptotic_fails : ¬ Tendsto relativeSize atTop (𝓝 1) := by
  intro h
  have hh := tendsto_nhds_unique relative_limit_zero h
  norm_num at hh

end CompleteGreedy
#print axioms CompleteGreedy.degree_regular
#print axioms CompleteGreedy.actual_output
#print axioms CompleteGreedy.expectation_one
#print axioms CompleteGreedy.almost_sure_one
#print axioms CompleteGreedy.benchmark_diverges
#print axioms CompleteGreedy.relative_limit_zero
#print axioms CompleteGreedy.claimed_relative_asymptotic_fails
