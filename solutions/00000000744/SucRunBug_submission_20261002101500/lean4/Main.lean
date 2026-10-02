import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
noncomputable section
open scoped Topology
namespace TLMC744
open MeasureTheory
variable (p : ℕ) [Fact p.Prime]
def step (c x : ℤ_[p]) : ℤ_[p] := x ^ 2 + c
def M : Set ℤ_[p] := {c | ∃ B : ℝ, ∀ n : ℕ, ‖(step p c)^[n] 0‖ ≤ B}
theorem orbit_bounded (c : ℤ_[p]) (n : ℕ) : ‖(step p c)^[n] 0‖ ≤ 1 :=
  PadicInt.norm_le_one _
theorem whole_ring : M p = Set.univ := by
  ext c
  simp only [M, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact ⟨1, orbit_bounded p c⟩
theorem clopen : IsClopen (M p) := by rw [whole_ring]; exact isClopen_univ
theorem normalized_measure [MeasurableSpace ℤ_[p]] (μ : Measure ℤ_[p])
    [IsProbabilityMeasure μ] : μ (M p) = 1 := by rw [whole_ring]; exact measure_univ
#print axioms whole_ring
#print axioms clopen
#print axioms normalized_measure
end TLMC744
