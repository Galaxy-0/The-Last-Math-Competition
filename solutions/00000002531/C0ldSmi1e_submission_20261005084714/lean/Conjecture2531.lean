import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

/-!
# A necessary density clause of conjecture 00000002531 is false

We use the usual real line, k = 1, standard normalized Hausdorff measure,
open balls centered at x, and all positive real radii approaching zero.
The source denominator is exactly r^k: no unit-ball volume is inserted.

The definitions `BorelDensityClause` and `CaratheodoryDensityClause` below
are necessary specializations of the source's first assertion. Neither is
claimed to define the entire source, whose further clauses concern dimension
and sharpness. The counterexample is E = univ. Its density is 2 everywhere.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Conjecture2531

/-- The Euclidean unit one-ball volume, used only to normalize the measure. -/
noncomputable def unitBallVolume : ℝ≥0∞ :=
  volume (Metric.ball (0 : ℝ) 1)

theorem unitBallVolume_eq_two : unitBallVolume = 2 := by
  norm_num [unitBallVolume, Real.volume_ball]

/-- The usual diameter-cover normalization coefficient omega_1 / 2^1. -/
noncomputable def hausdorffNormalization : ℝ≥0∞ := unitBallVolume / 2 ^ (1 : ℕ)

theorem hausdorffNormalization_eq_one : hausdorffNormalization = 1 := by
  rw [hausdorffNormalization, unitBallVolume_eq_two, pow_one]
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- Standard normalized H^1 on the usual Euclidean real line.
Mathlib's `hausdorffMeasure 1` uses the raw diameter gauge; the coefficient
omega_1/2^1 is explicitly included here. -/
noncomputable def normalizedHausdorff1 : Measure ℝ :=
  hausdorffNormalization • Measure.hausdorffMeasure 1

theorem normalizedHausdorff1_eq_raw :
    normalizedHausdorff1 = Measure.hausdorffMeasure 1 := by
  simp [normalizedHausdorff1, hausdorffNormalization_eq_one]

theorem normalizedHausdorff1_eq_volume : normalizedHausdorff1 = volume := by
  rw [normalizedHausdorff1_eq_raw, hausdorffMeasure_real]

/-- The metric is the ordinary Euclidean metric on the line. -/
theorem real_distance (x y : ℝ) : dist x y = |x - y| := Real.dist_eq x y

theorem normalizedHausdorff1_ball (x r : ℝ) :
    normalizedHausdorff1 (Metric.ball x r) = ENNReal.ofReal (2 * r) := by
  rw [normalizedHausdorff1_eq_volume, Real.volume_ball]

theorem normalizedHausdorff1_ball_ne_top (x r : ℝ) :
    normalizedHausdorff1 (Metric.ball x r) ≠ ∞ := by
  rw [normalizedHausdorff1_ball]
  exact ENNReal.ofReal_ne_top

theorem normalizedHausdorff1_univ : normalizedHausdorff1 (univ : Set ℝ) = ∞ := by
  rw [normalizedHausdorff1_eq_volume, Real.volume_univ]

/-- The source quotient H^1(E ∩ B(x,r))/r^1, in the extended nonnegative reals.
Its values away from positive radii have no role in the right-hand limit. -/
noncomputable def densityQuotient (E : Set ℝ) (x r : ℝ) : ℝ≥0∞ :=
  normalizedHausdorff1 (E ∩ Metric.ball x r) / ENNReal.ofReal (r ^ (1 : ℕ))

/-- Existence of the source limit with one of its two permitted finite values. -/
def HasBinaryDensity (E : Set ℝ) (x : ℝ) : Prop :=
  ∃ l : ℝ≥0∞, (l = 0 ∨ l = 1) ∧
    Tendsto (densityQuotient E x) (𝓝[>] (0 : ℝ)) (𝓝 l)

/-- A null set can depend on E; the conclusion is required at every x in E \ N. -/
def NullExceptionalBinaryDensity (E : Set ℝ) : Prop :=
  ∃ N : Set ℝ, normalizedHausdorff1 N = 0 ∧
    ∀ x ∈ E \ N, HasBinaryDensity E x

/-- The stronger ambient-a.e. reading implies the common necessary reading. -/
theorem ambient_ae_implies_nullExceptionalBinaryDensity {E : Set ℝ}
    (h : ∀ᵐ x ∂normalizedHausdorff1, HasBinaryDensity E x) :
    NullExceptionalBinaryDensity E := by
  refine ⟨{x | ¬ HasBinaryDensity E x}, ae_iff.mp h, ?_⟩
  intro x hx
  exact not_not.mp hx.2

/-- A necessary Borel specialization, with k = n = 1, of the source assertion. -/
def BorelDensityClause : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → NullExceptionalBinaryDensity E

/-- Caratheodory measurability for the specified Hausdorff outer measure. -/
def HausdorffMeasurable (E : Set ℝ) : Prop :=
  normalizedHausdorff1.toOuterMeasure.IsCaratheodory E

theorem borel_is_HausdorffMeasurable {E : Set ℝ} (hE : MeasurableSet E) :
    HausdorffMeasurable E := by
  intro A
  exact (measure_inter_add_diff A hE).symm

/-- The restricted-to-E first clause for all Caratheodory-measurable sets on ℝ.
This is still only a necessary specialization of the compound source. -/
def CaratheodoryDensityClause : Prop :=
  ∀ E : Set ℝ, HausdorffMeasurable E → NullExceptionalBinaryDensity E

theorem caratheodoryDensityClause_implies_borelDensityClause
    (h : CaratheodoryDensityClause) : BorelDensityClause := by
  intro E hE
  exact h E (borel_is_HausdorffMeasurable hE)

/-- The explicit null-set formulation agrees with the customary restricted a.e.
formulation for Borel E. No measurability of the density predicate is assumed. -/
theorem nullExceptionalBinaryDensity_iff_ae {E : Set ℝ} (hE : MeasurableSet E) :
    NullExceptionalBinaryDensity E ↔
      ∀ᵐ x ∂normalizedHausdorff1.restrict E, HasBinaryDensity E x := by
  rw [ae_restrict_iff' hE]
  constructor
  · rintro ⟨N, hN, hgood⟩
    apply ae_iff.mpr
    apply measure_mono_null _ hN
    intro x hx
    by_contra hxN
    exact hx (fun hxE => hgood x ⟨hxE, hxN⟩)
  · intro h
    refine ⟨{x | ¬ (x ∈ E → HasBinaryDensity E x)}, ae_iff.mp h, ?_⟩
    intro x hx
    exact (not_not.mp hx.2) hx.1

theorem densityQuotient_univ (x : ℝ) {r : ℝ} (hr : 0 < r) :
    densityQuotient univ x r = 2 := by
  rw [densityQuotient, univ_inter, normalizedHausdorff1_ball, pow_one,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [ENNReal.mul_div_cancel_right (ne_of_gt (ENNReal.ofReal_pos.mpr hr))
    ENNReal.ofReal_ne_top]
  norm_num

/-- Positive real radii approach zero nonvacuously. -/
theorem positiveRadii_neBot : NeBot (𝓝[>] (0 : ℝ)) := inferInstance

/-- Full right-hand real-radius convergence, not only convergence along a sequence. -/
theorem densityQuotient_univ_tendsto_two (x : ℝ) :
    Tendsto (densityQuotient univ x) (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ≥0∞)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (densityQuotient_univ x hr).symm

theorem univ_has_no_binary_density (x : ℝ) : ¬ HasBinaryDensity univ x := by
  rintro ⟨l, hl, hlim⟩
  have htwo : l = 2 := tendsto_nhds_unique hlim (densityQuotient_univ_tendsto_two x)
  rcases hl with hzero | hone
  · rw [hzero] at htwo
    norm_num at htwo
  · rw [hone] at htwo
    norm_num at htwo

/-- No H^1-null exception can remove the failure of the binary conclusion. -/
theorem univ_not_nullExceptionalBinaryDensity :
    ¬ NullExceptionalBinaryDensity (univ : Set ℝ) := by
  rintro ⟨N, hN, hgood⟩
  have hNuniv : N = univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact univ_has_no_binary_density x (hgood x ⟨mem_univ x, hx⟩)
  rw [hNuniv, normalizedHausdorff1_univ] at hN
  exact ENNReal.top_ne_zero hN

theorem not_borelDensityClause : ¬ BorelDensityClause := by
  intro h
  exact univ_not_nullExceptionalBinaryDensity (h univ MeasurableSet.univ)

theorem not_caratheodoryDensityClause : ¬ CaratheodoryDensityClause := by
  intro h
  exact not_borelDensityClause (caratheodoryDensityClause_implies_borelDensityClause h)

/-- Logical disproof bridge: a larger statement is false if it entails the
necessary clause. The argument does not define or reinterpret that statement. -/
theorem not_statement_implying_borelDensityClause (statement : Prop)
    (hnecessary : statement → BorelDensityClause) : ¬ statement := by
  intro hstatement
  exact not_borelDensityClause (hnecessary hstatement)

/-- Further conjunctive assertions cannot rescue the false necessary clause.
The remaining assertions are left uninterpreted, as the source omits details. -/
theorem not_borelDensityClause_and (remainingAssertions : Prop) :
    ¬ (BorelDensityClause ∧ remainingAssertions) := by
  exact not_statement_implying_borelDensityClause _ And.left

/-- A concrete witness with both measurability notions and no possible null exception. -/
theorem counterexample :
    MeasurableSet (univ : Set ℝ) ∧ HausdorffMeasurable (univ : Set ℝ) ∧
      (∀ x : ℝ, Tendsto (densityQuotient univ x) (𝓝[>] (0 : ℝ))
        (𝓝 (2 : ℝ≥0∞))) ∧ ¬ NullExceptionalBinaryDensity (univ : Set ℝ) := by
  exact ⟨MeasurableSet.univ, borel_is_HausdorffMeasurable MeasurableSet.univ,
    densityQuotient_univ_tendsto_two, univ_not_nullExceptionalBinaryDensity⟩

end Conjecture2531
