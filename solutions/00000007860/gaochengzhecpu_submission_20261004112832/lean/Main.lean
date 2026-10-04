import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
A counterexample to the universal finite-graph bound in conjecture 00000007860.
The graph, vertex orders, first-fit algorithm, color count, chromatic number,
waste, and finite uniform expectation are all defined explicitly below.
-/

namespace Conjecture7860

noncomputable section

/-- The least nonnegative integer not in a finite set of forbidden colors. -/
def firstAvailable (s : Finset ℕ) : ℕ :=
  Nat.find (Infinite.exists_not_mem_finset s)

theorem firstAvailable_not_mem (s : Finset ℕ) : firstAvailable s ∉ s :=
  Nat.find_spec (Infinite.exists_not_mem_finset s)

theorem firstAvailable_minimal (s : Finset ℕ) (c : ℕ)
    (hc : c < firstAvailable s) : c ∈ s := by
  by_contra h
  exact Nat.find_min (Infinite.exists_not_mem_finset s) hc h

@[simp] theorem firstAvailable_empty : firstAvailable ∅ = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.find_min' (Infinite.exists_not_mem_finset (∅ : Finset ℕ)) (by simp)

/-- Colors on already processed neighbors of the current vertex. -/
def forbiddenColors {n : ℕ} (G : SimpleGraph (Fin n))
    (state : List (Fin n × ℕ)) (v : Fin n) : Finset ℕ := by
  classical
  exact ((state.filter (fun p => decide (G.Adj v p.1))).map Prod.snd).toFinset

/-- The ordinary first-fit process, with processed (vertex,color) pairs stored
in reverse order. The first legal color is chosen at each recursive step. -/
def greedyRun {n : ℕ} (G : SimpleGraph (Fin n)) :
    List (Fin n × ℕ) → List (Fin n) → List (Fin n × ℕ)
  | state, [] => state
  | state, v :: rest =>
      greedyRun G ((v, firstAvailable (forbiddenColors G state v)) :: state) rest

/-- A permutation maps processing positions to vertices, so every vertex
appears exactly once. -/
def greedyAssignment {n : ℕ} (G : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) : List (Fin n × ℕ) :=
  greedyRun G [] (List.ofFn σ)

def greedyColorsUsed {n : ℕ} (G : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((greedyAssignment G σ).map Prod.snd).toFinset.card

/-- Real subtraction of the actual greedy color count and Mathlib's minimum
proper-coloring number. Every graph here is finite, hence the latter is finite. -/
def waste {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) : ℝ :=
  (greedyColorsUsed G σ : ℝ) - (G.chromaticNumber.toNat : ℝ)

/-- Exact expectation for the uniform distribution on all vertex permutations. -/
def uniformExpectedWaste {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n), waste G σ) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)

theorem uniform_sample_space_card_pos (n : ℕ) :
    0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos

theorem finite_graph_chromatic_number_finite {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.chromaticNumber ≠ ⊤ := by
  apply (SimpleGraph.chromaticNumber_ne_top_iff_exists (G := G)).mpr
  exact ⟨Fintype.card (Fin n), G.colorable_of_fintype⟩

def claimedBound (n : ℕ) : ℝ := (n : ℝ) / 2 - Real.sqrt ((n : ℝ) / 2)

def singletonGraph : SimpleGraph (Fin 1) := ⊥

theorem singleton_no_edges (u v : Fin 1) : ¬ singletonGraph.Adj u v := by
  simp [singletonGraph]

theorem singleton_order_unique (σ : Equiv.Perm (Fin 1)) :
    σ = Equiv.refl (Fin 1) := by
  apply Equiv.ext
  intro v
  exact Subsingleton.elim _ _

theorem singleton_order_count : Fintype.card (Equiv.Perm (Fin 1)) = 1 := by
  simp [Fintype.card_perm]

theorem singleton_order_list (σ : Equiv.Perm (Fin 1)) :
    List.ofFn σ = [0] := by
  rw [singleton_order_unique σ]
  simp [List.ofFn_succ]

theorem singleton_greedy_assignment (σ : Equiv.Perm (Fin 1)) :
    greedyAssignment singletonGraph σ = [(0, 0)] := by
  unfold greedyAssignment
  rw [singleton_order_list]
  simp [greedyRun, forbiddenColors]

/-- The computed color 0 is an actual proper coloring of the graph. -/
def singletonColoring : singletonGraph.Coloring ℕ :=
  SimpleGraph.Coloring.mk (fun _ => 0) (by
    intro u v h
    exact (singleton_no_edges u v h).elim)

theorem singleton_assignment_matches_coloring (σ : Equiv.Perm (Fin 1))
    (v : Fin 1) : (v, singletonColoring v) ∈ greedyAssignment singletonGraph σ := by
  have hv : v = 0 := Subsingleton.elim _ _
  change (v, 0) ∈ greedyAssignment singletonGraph σ
  rw [singleton_greedy_assignment, hv]
  simp

theorem singleton_greedy_uses_one (σ : Equiv.Perm (Fin 1)) :
    greedyColorsUsed singletonGraph σ = 1 := by
  simp [greedyColorsUsed, singleton_greedy_assignment]

theorem singleton_chromatic_number : singletonGraph.chromaticNumber = 1 := by
  exact SimpleGraph.chromaticNumber_bot

theorem singleton_waste_zero (σ : Equiv.Perm (Fin 1)) :
    waste singletonGraph σ = 0 := by
  simp [waste, singleton_greedy_uses_one, singleton_chromatic_number]

theorem singleton_uniform_expectation_zero : uniformExpectedWaste singletonGraph = 0 := by
  simp [uniformExpectedWaste, singleton_waste_zero]

theorem claimed_bound_one_negative : claimedBound 1 < 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hn := Real.sqrt_nonneg ((1 : ℝ) / 2)
  have hlt : (1 : ℝ) / 2 < Real.sqrt (1 / 2) := by nlinarith
  simpa [claimedBound] using sub_neg.mpr hlt

/-- Failure for every order, hence also almost surely under the uniform law. -/
theorem singleton_pointwise_counterexample (σ : Equiv.Perm (Fin 1)) :
    ¬ waste singletonGraph σ ≤ claimedBound 1 := by
  rw [singleton_waste_zero]
  exact not_le.mpr claimed_bound_one_negative

theorem singleton_expectation_counterexample :
    ¬ uniformExpectedWaste singletonGraph ≤ claimedBound 1 := by
  rw [singleton_uniform_expectation_zero]
  exact not_le.mpr claimed_bound_one_negative

def UniversalPointwiseBound : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)),
    waste G σ ≤ claimedBound n

def UniversalExpectationBound : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), uniformExpectedWaste G ≤ claimedBound n

theorem not_universal_pointwise_bound : ¬ UniversalPointwiseBound := by
  intro h
  exact singleton_pointwise_counterexample (Equiv.refl _) (h 1 singletonGraph (Equiv.refl _))

theorem not_universal_expectation_bound : ¬ UniversalExpectationBound := by
  intro h
  exact singleton_expectation_counterexample (h 1 singletonGraph)

#print axioms singleton_greedy_assignment
#print axioms singleton_assignment_matches_coloring
#print axioms singleton_chromatic_number
#print axioms singleton_waste_zero
#print axioms singleton_uniform_expectation_zero
#print axioms singleton_pointwise_counterexample
#print axioms singleton_expectation_counterexample
#print axioms not_universal_pointwise_bound
#print axioms not_universal_expectation_bound

end

end Conjecture7860
