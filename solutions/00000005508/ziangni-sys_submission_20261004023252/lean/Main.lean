import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card

namespace BottleneckCounterexample

structure Network (n : ℕ) where
  capacity : Fin n → ℝ
  traffic : Fin n → ℝ
  capacity_pos : ∀ i, 0 < capacity i
  traffic_pos : ∀ i, 0 < traffic i

def residual {n : ℕ} (N : Network n) (load : ℝ) (i : Fin n) : ℝ :=
  N.capacity i - load * N.traffic i

def Saturated {n : ℕ} (N : Network n) (load : ℝ) (i : Fin n) : Prop :=
  N.capacity i ≤ load * N.traffic i

def FirstBottleneck {n : ℕ} (N : Network n) (i : Fin n) : Prop :=
  ∃ threshold : ℝ, 0 ≤ threshold ∧ Saturated N threshold i ∧
    (∀ load : ℝ, 0 ≤ load → load < threshold →
      ∀ j : Fin n, ¬ Saturated N load j)

noncomputable def bottlenecks {n : ℕ} (N : Network n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (FirstBottleneck N)

def single : Network 1 where
  capacity := fun _ => 1
  traffic := fun _ => 1
  capacity_pos := fun _ => zero_lt_one
  traffic_pos := fun _ => zero_lt_one

theorem single_saturated (load : ℝ) (i : Fin 1) :
    Saturated single load i ↔ 1 ≤ load := by
  simp [Saturated, single]

theorem single_residual (load : ℝ) (i : Fin 1) :
    residual single load i = 1 - load := by
  simp [residual, single]

theorem single_first (i : Fin 1) : FirstBottleneck single i := by
  refine ⟨1, zero_le_one, ?_, ?_⟩
  · exact (single_saturated 1 i).mpr le_rfl
  · intro load _ hlt j hsat
    exact (not_le_of_gt hlt) ((single_saturated load j).mp hsat)

theorem single_tied_count : (bottlenecks single).card = 1 := by
  classical
  have h : bottlenecks single = Finset.univ := by
    ext i
    simp [bottlenecks, single_first]
  rw [h]
  simp

noncomputable def minimumStations {n : ℕ} (N : Network n) (load : ℝ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∀ j, residual N load i ≤ residual N load j)

theorem single_minimum_multiplicity (load : ℝ) :
    (minimumStations single load).card = 1 := by
  classical
  have h : minimumStations single load = Finset.univ := by
    ext i
    simp [minimumStations, residual, single]
  rw [h]
  simp

theorem first_count_is_minimum_multiplicity :
    (bottlenecks single).card = (minimumStations single 1).card := by
  rw [single_tied_count, single_minimum_multiplicity]

def LogarithmicTieBound : Prop :=
  ∀ n : ℕ, 0 < n → ∀ N : Network n,
    ((bottlenecks N).card : ℝ) ≤ Real.log n

theorem single_violates :
    ¬ (((bottlenecks single).card : ℝ) ≤ Real.log (1 : ℝ)) := by
  rw [single_tied_count, Real.log_one]
  simp

theorem conjecture_5508_false : ¬ LogarithmicTieBound := by
  intro h
  apply single_violates
  simpa using h 1 Nat.zero_lt_one single

theorem single_violates_every_base (base : ℝ) :
    ¬ (((bottlenecks single).card : ℝ) ≤
      Real.log (1 : ℝ) / Real.log base) := by
  rw [single_tied_count, Real.log_one, zero_div]
  simp

end BottleneckCounterexample

#print axioms BottleneckCounterexample.conjecture_5508_false
#print axioms BottleneckCounterexample.single_violates_every_base
