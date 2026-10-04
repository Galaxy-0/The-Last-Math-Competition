import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace CoreVertexCounterexample
noncomputable section
open Finset
abbrev Player := Fin 2
abbrev Coalition := Finset Player
abbrev Allocation := Player → ℝ

def closure (s : Coalition) : Coalition := s

def IsConvexGeometry (cl : Coalition → Coalition) : Prop :=
  cl ∅ = ∅ ∧ (∀ s, s ⊆ cl s) ∧
  (∀ s t, s ⊆ t → cl s ⊆ cl t) ∧ (∀ s, cl (cl s) = cl s) ∧
  (∀ s x y, x ≠ y → x ∉ cl s → y ∉ cl s →
    x ∈ cl (insert y s) → y ∉ cl (insert x s))

theorem boolean_convex_geometry : IsConvexGeometry closure := by
  refine ⟨rfl, fun _ => subset_rfl, fun _ _ h => h, fun _ => rfl, ?_⟩
  intro s x y hxy hx _ h
  rcases mem_insert.mp h with h | h
  · exact (hxy h).elim
  · exact (hx h).elim

def Feasible (s : Coalition) : Prop := closure s = s

theorem every_coalition_feasible (s : Coalition) : Feasible s := rfl

theorem feasible_accessible (s : Coalition) (h : s ≠ ∅) :
    ∃ x ∈ s, Feasible (s.erase x) := by
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h
  exact ⟨x, hx, every_coalition_feasible _⟩

def game (s : Coalition) : ℝ := s.card

theorem game_normalized : game ∅ = 0 := by simp [game]

theorem game_modular (s t : Coalition) :
    game (s ∪ t) + game (s ∩ t) = game s + game t := by
  unfold game
  exact_mod_cast card_union_add_card_inter s t

theorem game_supermodular (s t : Coalition) :
    game s + game t ≤ game (s ∪ t) + game (s ∩ t) := by
  rw [game_modular]

theorem game_submodular (s t : Coalition) :
    game (s ∪ t) + game (s ∩ t) ≤ game s + game t := by
  rw [game_modular]

def ones : Allocation := fun _ => 1

def payoffCore : Set Allocation := {x | (∑ i, x i) = game univ ∧
  ∀ s : Coalition, Feasible s → game s ≤ ∑ i ∈ s, x i}

def costCore : Set Allocation := {x | (∑ i, x i) = game univ ∧
  ∀ s : Coalition, Feasible s → (∑ i ∈ s, x i) ≤ game s}

theorem payoff_core_singleton : payoffCore = {ones} := by
  ext x
  constructor
  · intro hx
    have h0 := hx.2 {0} (every_coalition_feasible _)
    have h1 := hx.2 {1} (every_coalition_feasible _)
    have ht := hx.1
    simp [game, Fin.sum_univ_two] at h0 h1 ht
    apply Set.mem_singleton_iff.mpr
    funext i
    fin_cases i <;> simp [ones] <;> linarith
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    constructor
    · simp [ones, game]
    · intro s _; simp [ones, game]

theorem cost_core_singleton : costCore = {ones} := by
  ext x
  constructor
  · intro hx
    have h0 := hx.2 {0} (every_coalition_feasible _)
    have h1 := hx.2 {1} (every_coalition_feasible _)
    have ht := hx.1
    simp [game, Fin.sum_univ_two] at h0 h1 ht
    apply Set.mem_singleton_iff.mpr
    funext i
    fin_cases i <;> simp [ones] <;> linarith
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    constructor
    · simp [ones, game]
    · intro s _; simp [ones, game]

theorem payoff_extreme_points : payoffCore.extremePoints ℝ = {ones} := by
  rw [payoff_core_singleton, extremePoints_singleton]

theorem cost_extreme_points : costCore.extremePoints ℝ = {ones} := by
  rw [cost_core_singleton, extremePoints_singleton]

theorem vertex_count_fails :
    (payoffCore.extremePoints ℝ).ncard = 1 ∧
    (costCore.extremePoints ℝ).ncard = 1 ∧
    (payoffCore.extremePoints ℝ).ncard ≠ 2 ^ (Fintype.card Player - 1) ∧
    (costCore.extremePoints ℝ).ncard ≠ 2 ^ (Fintype.card Player - 1) := by
  rw [payoff_extreme_points, cost_extreme_points]
  norm_num

#print axioms boolean_convex_geometry
#print axioms game_modular
#print axioms payoff_core_singleton
#print axioms cost_core_singleton
#print axioms vertex_count_fails
end
end CoreVertexCounterexample
