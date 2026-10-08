import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.NormNum

noncomputable section
open SimpleGraph Filter Asymptotics
open scoped Topology
namespace Conjecture2164

abbrev V (n : ℕ) := Fin (n + 3) × Fin 2
def prism (n : ℕ) : SimpleGraph (V n) := cycleGraph (n + 3) □ (⊤ : SimpleGraph (Fin 2))
def rings (n : ℕ) : SimpleGraph (V n) := cycleGraph (n + 3) □ (⊥ : SimpleGraph (Fin 2))

local instance (n : ℕ) (G : SimpleGraph (V n)) (v : V n) : Fintype (G.neighborSet v) :=
  Fintype.ofFinite _

theorem prism_cubic (n : ℕ) (v : V n) : (prism n).degree v = 3 := by
  classical
  rw [prism, boxProd_degree, cycleGraph_degree_three_le]
  norm_num

theorem prism_connected (n : ℕ) : (prism n).Connected := by
  apply Connected.boxProd
  · exact cycleGraph_connected
  · exact top_connected

theorem rings_degree (n : ℕ) (v : V n) : (rings n).degree v = 2 := by
  classical
  rw [rings, boxProd_degree, cycleGraph_degree_three_le]
  have hb : ∀ i : Fin 2, (⊥ : SimpleGraph (Fin 2)).degree i = 0 := by decide
  simp [hb]

theorem rings_subgraph (n : ℕ) : rings n ≤ prism n := by
  intro v w h
  simp only [rings, boxProd_adj, bot_adj, false_and, or_false] at h
  exact Or.inl h

/-- Spanning subgraphs in which every vertex has degree two. -/
def TwoFactor (n : ℕ) := {H : SimpleGraph (V n) // H ≤ prism n ∧ ∀ v, H.degree v = 2}

instance (n : ℕ) : Nonempty (TwoFactor n) := ⟨⟨rings n, rings_subgraph n, rings_degree n⟩⟩

instance (n : ℕ) : Finite (TwoFactor n) := inferInstanceAs
  (Finite {H : SimpleGraph (V n) // H ≤ prism n ∧ ∀ v, H.degree v = 2})

def count (n : ℕ) : ℕ := Nat.card (TwoFactor n)
def vertexCount (n : ℕ) : ℕ := Fintype.card (V n)

theorem count_positive (n : ℕ) : 1 ≤ count n := Nat.card_pos

theorem vertex_count (n : ℕ) : vertexCount n = 2 * (n + 3) := by
  simp [vertexCount, V, Nat.mul_comm]

def proposedBase : ℝ := (4 : ℝ) ^ (1 / 3 : ℝ) / Real.pi

theorem base_nonnegative : 0 ≤ proposedBase :=
  div_nonneg (Real.rpow_nonneg (by norm_num) _) Real.pi_pos.le

theorem base_less_than_one : proposedBase < 1 := by
  have hroot : (4 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
    calc
      (4 : ℝ) ^ (1 / 3 : ℝ) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := by
        rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 from by norm_num,
          Real.sqrt_sq (by norm_num)]
  apply (div_lt_one Real.pi_pos).2
  exact hroot.trans_lt ((by norm_num : (2 : ℝ) < 3).trans Real.pi_gt_three)

theorem proposed_asymptotic_tends_zero :
    Tendsto (fun n => proposedBase ^ vertexCount n) atTop (𝓝 0) := by
  apply (tendsto_pow_atTop_nhds_zero_of_lt_one base_nonnegative base_less_than_one).comp
  apply tendsto_atTop_mono (f := fun n : ℕ => n) _ tendsto_id
  intro n
  rw [vertex_count]
  change n ≤ 2 * (n + 3)
  omega

theorem count_not_tending_zero : ¬ Tendsto (fun n => (count n : ℝ)) atTop (𝓝 0) := by
  intro h
  have hle : (1 : ℝ) ≤ 0 := ge_of_tendsto h (Eventually.of_forall (fun n => by
    exact_mod_cast count_positive n))
  norm_num at hle

theorem conjectured_count_bound_false :
    ¬ (fun n => (count n : ℝ)) =O[atTop] (fun n => proposedBase ^ vertexCount n) := by
  intro h
  exact count_not_tending_zero (h.trans_tendsto proposed_asymptotic_tends_zero)

#print axioms prism_cubic
#print axioms prism_connected
#print axioms rings_degree
#print axioms rings_subgraph
#print axioms count_positive
#print axioms vertex_count
#print axioms base_less_than_one
#print axioms proposed_asymptotic_tends_zero
#print axioms conjectured_count_bound_false
end Conjecture2164
