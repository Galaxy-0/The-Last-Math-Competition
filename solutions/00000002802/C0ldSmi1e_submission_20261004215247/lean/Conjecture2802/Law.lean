import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

/-!
The actual fair Bernoulli law on the real line, its arithmetic lattice support,
and its moment generating function. Ordinary support and convex support are
kept distinct.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Conjecture2802

/-- Equal point masses at zero and one. -/
def fairBernoulli : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1

/-- A probability law is arithmetic if it is concentrated on a translate of
an integer lattice with strictly positive spacing. -/
def LatticeLaw (μ : Measure ℝ) : Prop :=
  ∃ a h : ℝ, 0 < h ∧ ∀ᵐ x ∂μ, ∃ k : ℤ, x = a + h * (k : ℝ)

/-- The ordinary topological support: every open neighborhood has positive
measure, expressed equivalently as nonzero measure. -/
def topologicalSupport (μ : Measure ℝ) : Set ℝ :=
  {x | ∀ U : Set ℝ, IsOpen U → x ∈ U → μ U ≠ 0}

instance fairBernoulli_isProbabilityMeasure : IsProbabilityMeasure fairBernoulli where
  measure_univ := by simpa [fairBernoulli] using ENNReal.add_halves 1

theorem fairBernoulli_mass_zero : fairBernoulli {0} = (1 / 2 : ℝ≥0∞) := by
  norm_num [fairBernoulli, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]

theorem fairBernoulli_mass_one : fairBernoulli {1} = (1 / 2 : ℝ≥0∞) := by
  norm_num [fairBernoulli, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]

theorem ae_fairBernoulli_iff (P : ℝ → Prop) :
    (∀ᵐ x ∂fairBernoulli, P x) ↔ P 0 ∧ P 1 := by
  simp only [fairBernoulli, ae_add_measure_iff,
    Measure.ae_smul_measure_iff (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0),
    ae_dirac_eq, Filter.eventually_pure]

theorem fairBernoulli_lattice : LatticeLaw fairBernoulli := by
  refine ⟨0, 1, by norm_num, (ae_fairBernoulli_iff _).2 ?_⟩
  constructor
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩

theorem fairBernoulli_not_ae_constant (a : ℝ) :
    ¬ (∀ᵐ x ∂fairBernoulli, x = a) := by
  rw [ae_fairBernoulli_iff]
  rintro ⟨h0, h1⟩
  norm_num [← h0] at h1

/-- Every real function is integrable for this finite atomic measure. -/
theorem integrable_fairBernoulli (f : ℝ → ℝ) : Integrable f fairBernoulli := by
  exact (integrable_dirac.smul_measure (by norm_num)).add_measure
    (integrable_dirac.smul_measure (by norm_num))

theorem integrable_exp_fairBernoulli (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) fairBernoulli :=
  integrable_fairBernoulli _

theorem mgf_fairBernoulli (t : ℝ) :
    ProbabilityTheory.mgf id fairBernoulli t = (1 + Real.exp t) / 2 := by
  unfold fairBernoulli
  rw [ProbabilityTheory.mgf_add_measure
    (integrable_dirac.smul_measure (by norm_num))
    (integrable_dirac.smul_measure (by norm_num))]
  simp only [ProbabilityTheory.mgf_smul_measure, ProbabilityTheory.mgf_dirac', id_eq,
    mul_zero, Real.exp_zero, mul_one, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat]
  ring

theorem cgf_fairBernoulli (t : ℝ) :
    ProbabilityTheory.cgf id fairBernoulli t = Real.log ((1 + Real.exp t) / 2) := by
  rw [ProbabilityTheory.cgf, mgf_fairBernoulli]

theorem support_fairBernoulli :
    topologicalSupport fairBernoulli = ({0, 1} : Set ℝ) := by
  ext x
  constructor
  · intro hx
    by_contra hnot
    have hopen : IsOpen (({0, 1} : Set ℝ)ᶜ) :=
      (isClosed_singleton.union isClosed_singleton).isOpen_compl
    have hmass := hx _ hopen hnot
    apply hmass
    norm_num [fairBernoulli, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]
  · intro hx
    rcases hx with (rfl | rfl)
    · intro U _ h0 hzero
      have hle : fairBernoulli {0} ≤ fairBernoulli U :=
        measure_mono (singleton_subset_iff.mpr h0)
      rw [fairBernoulli_mass_zero, hzero] at hle
      norm_num at hle
    · intro U _ h1 hzero
      have hle : fairBernoulli {1} ≤ fairBernoulli U :=
        measure_mono (singleton_subset_iff.mpr h1)
      rw [fairBernoulli_mass_one, hzero] at hle
      norm_num at hle

theorem interior_support_fairBernoulli :
    interior (topologicalSupport fairBernoulli) = ∅ := by
  rw [support_fairBernoulli]
  change interior (({0} : Set ℝ) ∪ {1}) = ∅
  rw [interior_union_isClosed_of_interior_empty isClosed_singleton
    (interior_singleton (1 : ℝ)), interior_singleton]

theorem convexHull_support_fairBernoulli :
    convexHull ℝ (topologicalSupport fairBernoulli) = Set.Icc 0 1 := by
  rw [support_fairBernoulli, convexHull_pair, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]

theorem interior_convexHull_support_fairBernoulli :
    interior (convexHull ℝ (topologicalSupport fairBernoulli)) = Set.Ioo 0 1 := by
  rw [convexHull_support_fairBernoulli, interior_Icc]

end Conjecture2802
