import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

noncomputable section
open MeasureTheory Filter Topology Finset
namespace DrivenAverage

abbrev Ω := Unit
instance : MeasurableSpace Ω := ⊤
def μ : Measure Ω := Measure.dirac ()
instance : IsProbabilityMeasure μ := by unfold μ; infer_instance
def T : Ω → Ω := id
def f : Ω → ℝ := fun _ => 0
def drive (i : ℕ) : ℝ := i

theorem compact_space : CompactSpace Ω := inferInstance
theorem continuous_T : Continuous T := continuous_id
theorem continuous_f : Continuous f := continuous_const
theorem system_ergodic : Ergodic T μ where
  toMeasurePreserving := MeasurePreserving.id μ
  aeconst_set _ _ _ := Filter.EventuallyConst.of_subsingleton_left

theorem driver_unbounded (B : ℝ) : ∃ i : ℕ, B < drive i := exists_nat_gt B

-- start is an arbitrary fixed origin of the sliding window.
def average (start n : ℕ) (x : Ω) : ℝ :=
  (∑ i ∈ range n, (f ((T^[i]) x) + drive (start + i))) / n

def optimal (start n : ℕ) : ℝ := sSup (Set.range (average start n))

theorem average_range (start n : ℕ) :
    Set.range (average start n) = {average start n ()} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    cases x
    exact Set.mem_singleton _
  · intro h
    exact ⟨(), Set.mem_singleton_iff.mp h |>.symm⟩

theorem optimal_attained (start n : ℕ) : optimal start n = average start n () := by
  rw [optimal, average_range, csSup_singleton]

theorem sum_formula (n : ℕ) :
    (∑ i ∈ range n, (i : ℝ)) * 2 = (n : ℝ) * ((n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    nlinarith

theorem shifted_sum (start n : ℕ) :
    (∑ i ∈ range n, ((start + i : ℕ) : ℝ)) =
      (n : ℝ) * start + ∑ i ∈ range n, (i : ℝ) := by
  simp [Nat.cast_add, sum_add_distrib, mul_comm]

theorem optimal_formula (start n : ℕ) (hn : 1 ≤ n) :
    optimal start n = start + ((n : ℝ) - 1) / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  rw [optimal_attained]
  simp only [average, f, drive, zero_add]
  rw [shifted_sum]
  apply (div_eq_iff hn0).mpr
  have h := sum_formula n
  nlinarith

theorem ratio_formula (start n : ℕ) (hn : 1 ≤ n) :
    optimal start n / n = (1 : ℝ) / 2 + ((start : ℝ) - 1 / 2) * (n : ℝ)⁻¹ := by
  rw [optimal_formula start n hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  field_simp
  ring

theorem ratio_tendsto_half (start : ℕ) :
    Tendsto (fun n : ℕ => optimal start n / n) atTop (𝓝 ((1 : ℝ) / 2)) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ) / 2) atTop (𝓝 ((1 : ℝ) / 2)) :=
    tendsto_const_nhds
  have hm : Tendsto (fun n : ℕ => ((start : ℝ) - 1 / 2) * (n : ℝ)⁻¹)
      atTop (𝓝 (((start : ℝ) - 1 / 2) * 0)) := tendsto_const_nhds.mul hi
  have h' : Tendsto (fun n : ℕ => (1 : ℝ) / 2 +
      ((start : ℝ) - 1 / 2) * (n : ℝ)⁻¹) atTop (𝓝 ((1 : ℝ) / 2)) := by
    simpa using hc.add hm
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (ratio_formula start n hn).symm

theorem not_sublinear (start : ℕ) :
    ¬ Asymptotics.IsLittleO atTop (optimal start) (fun n : ℕ => (n : ℝ)) := by
  intro h
  have he := tendsto_nhds_unique (ratio_tendsto_half start) h.tendsto_div_nhds_zero
  norm_num at he

#print axioms system_ergodic
#print axioms driver_unbounded
#print axioms optimal_attained
#print axioms optimal_formula
#print axioms ratio_tendsto_half
#print axioms not_sublinear
end DrivenAverage
