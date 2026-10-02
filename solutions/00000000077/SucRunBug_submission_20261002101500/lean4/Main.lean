import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
open MeasureTheory Filter
noncomputable section
open scoped Topology
namespace TLMC77
instance : MeasurableSpace (Fin 2) := ⊤
noncomputable def μ : Measure (Fin 2) := (1 / 2 : ENNReal) • Measure.count
abbrev A : Set (Fin 2) := {0}
theorem total_mass : μ Set.univ = 1 := by
  norm_num [μ, Measure.smul_apply, Measure.count_apply_finite, Set.toFinset_univ]
  exact ENNReal.inv_mul_cancel (by norm_num) (by simp)
theorem half_mass : μ A = 1 / 2 := by
  simp [μ, A, Measure.smul_apply]
theorem identity_preserves : MeasurePreserving (id : Fin 2 → Fin 2) μ μ :=
  MeasurePreserving.id μ
def correlationSet (a b : ℕ) : Set (Fin 2) :=
  A ∩ ((id : Fin 2 → Fin 2)^[a]) ⁻¹' A ∩ ((id : Fin 2 → Fin 2)^[b]) ⁻¹' A
noncomputable def correlation (a b : ℕ) : ℝ := (μ (correlationSet a b)).toReal
theorem correlation_half (a b : ℕ) : correlation a b = 1 / 2 := by
  simp [correlation, correlationSet, Function.iterate_id, half_mass]
noncomputable def average (F : Finset ℕ) (a b : ℕ → ℕ) : ℝ :=
  (∑ n ∈ F, correlation (a n) (b n)) / F.card
theorem average_values (F : Finset ℕ) (a b : ℕ → ℕ) :
    average F a b = 0 ∨ average F a b = 1 / 2 := by
  simp only [average, correlation_half, Finset.sum_const, nsmul_eq_mul]
  by_cases h : F.card = 0
  · left; simp [h]
  · right
    have : (F.card : ℝ) ≠ 0 := by exact_mod_cast h
    field_simp
theorem no_claimed_limit (F : ℕ → Finset ℕ) (a b : ℕ → ℕ) :
    ¬ Tendsto (fun N => average (F N) a b) atTop (𝓝 ((μ A).toReal ^ 2)) := by
  intro h
  have hc : IsClosed ({0, (1/2 : ℝ)} : Set ℝ) := Set.Finite.isClosed (Set.toFinite _)
  have hm := hc.mem_of_tendsto h (Filter.Eventually.of_forall (fun N => by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using average_values (F N) a b))
  norm_num [half_mass] at hm
#print axioms total_mass
#print axioms identity_preserves
#print axioms no_claimed_limit
def indices (N : ℕ) : Finset ℕ := (Finset.range N).filter (fun n => n.Prime ∧ (n+2).Prime)
theorem twin_prime_limit_fails :
    ¬ Tendsto (fun N => average (indices N) id (fun n => n+2)) atTop
      (𝓝 ((μ A).toReal ^ 2)) := no_claimed_limit indices id (fun n => n+2)
#print axioms twin_prime_limit_fails
end TLMC77
