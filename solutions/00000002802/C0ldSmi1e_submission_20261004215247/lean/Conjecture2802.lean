import Conjecture2802.Transform
import Conjecture2802.Regularity

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace Conjecture2802

/-- An exact smooth real representative of the actual convex dual on a nonempty interval. -/
theorem fairBernoulli_rate_smooth :
    ∃ f : ℝ → ℝ, ContDiffOn ℝ ∞ f (Ioo 0 1) ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, cramerRate fairBernoulli x = (f x : EReal) := by
  refine ⟨binaryRate, binaryRate_contDiffOn, ?_⟩
  intro x hx
  exact cramerRate_fairBernoulli x hx.1 hx.2

theorem fairBernoulli_rate_c2_interval :
    RateC2On (cramerRate fairBernoulli) (Ioo 0 1) := by
  apply rateC2On_of_eq_binaryRate
  intro x hx
  exact cramerRate_fairBernoulli x hx.1 hx.2

/-- The literal ordinary-support interior is empty; this certificate is separately vacuous. -/
theorem fairBernoulli_rate_c2_support :
    RateC2On (cramerRate fairBernoulli) (interior (topologicalSupport fairBernoulli)) := by
  rw [interior_support_fairBernoulli]
  exact rateC2On_empty _

/-- Convex support has the nonempty interior on which the computed rate is smooth. -/
theorem fairBernoulli_rate_c2_convexSupport :
    RateC2On (cramerRate fairBernoulli)
      (interior (convexHull ℝ (topologicalSupport fairBernoulli))) := by
  rw [interior_convexHull_support_fairBernoulli]
  exact fairBernoulli_rate_c2_interval

/-- The effective-domain reading gives the same nonempty differentiability region. -/
theorem fairBernoulli_rate_c2_effectiveDomain :
    RateC2On (cramerRate fairBernoulli) (interior (effectiveDomain fairBernoulli)) := by
  rw [interior_effectiveDomain_fairBernoulli]
  exact fairBernoulli_rate_c2_interval

theorem fairBernoulli_rate_twice_support :
    RateTwiceDifferentiableOn (cramerRate fairBernoulli)
      (interior (topologicalSupport fairBernoulli)) :=
  fairBernoulli_rate_c2_support.twiceDifferentiableOn isOpen_interior

theorem fairBernoulli_rate_twice_convexSupport :
    RateTwiceDifferentiableOn (cramerRate fairBernoulli)
      (interior (convexHull ℝ (topologicalSupport fairBernoulli))) :=
  fairBernoulli_rate_c2_convexSupport.twiceDifferentiableOn isOpen_interior

theorem fairBernoulli_rate_twice_effectiveDomain :
    RateTwiceDifferentiableOn (cramerRate fairBernoulli)
      (interior (effectiveDomain fairBernoulli)) :=
  fairBernoulli_rate_c2_effectiveDomain.twiceDifferentiableOn isOpen_interior

theorem fairBernoulli_convexSupport_interior_nonempty :
    (interior (convexHull ℝ (topologicalSupport fairBernoulli))).Nonempty := by
  rw [interior_convexHull_support_fairBernoulli]
  exact ⟨1 / 2, by norm_num⟩

theorem fairBernoulli_effectiveDomain_interior_nonempty :
    (interior (effectiveDomain fairBernoulli)).Nonempty := by
  rw [interior_effectiveDomain_fairBernoulli]
  exact ⟨1 / 2, by norm_num⟩

/-- A necessary consequence of the asserted criterion, restricted even to nondegenerate
probability laws having every exponential moment. No converse or variance clause is asserted. -/
def NonlatticeNecessaryOn (region : Measure ℝ → Set ℝ) : Prop :=
  ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
    (∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * x)) μ) →
    (∀ a : ℝ, ¬ (∀ᵐ x ∂μ, x = a)) →
    RateTwiceDifferentiableOn (cramerRate μ) (region μ) → ¬ LatticeLaw μ

def OrdinarySupportNecessaryClaim : Prop :=
  NonlatticeNecessaryOn (fun μ => interior (topologicalSupport μ))

def ConvexSupportNecessaryClaim : Prop :=
  NonlatticeNecessaryOn (fun μ => interior (convexHull ℝ (topologicalSupport μ)))

def EffectiveDomainNecessaryClaim : Prop :=
  NonlatticeNecessaryOn (fun μ => interior (effectiveDomain μ))

theorem not_nonlatticeNecessaryOn_of_fairBernoulli
    (region : Measure ℝ → Set ℝ)
    (hreg : RateTwiceDifferentiableOn (cramerRate fairBernoulli) (region fairBernoulli)) :
    ¬ NonlatticeNecessaryOn region := by
  intro h
  exact h fairBernoulli inferInstance integrable_exp_fairBernoulli
    fairBernoulli_not_ae_constant hreg fairBernoulli_lattice

theorem not_ordinarySupportNecessaryClaim : ¬ OrdinarySupportNecessaryClaim :=
  not_nonlatticeNecessaryOn_of_fairBernoulli _ fairBernoulli_rate_twice_support

theorem not_convexSupportNecessaryClaim : ¬ ConvexSupportNecessaryClaim :=
  not_nonlatticeNecessaryOn_of_fairBernoulli _ fairBernoulli_rate_twice_convexSupport

theorem not_effectiveDomainNecessaryClaim : ¬ EffectiveDomainNecessaryClaim :=
  not_nonlatticeNecessaryOn_of_fairBernoulli _ fairBernoulli_rate_twice_effectiveDomain

/-- All three explicit interior readings fail the source's necessary implication. -/
theorem necessary_criterion_fails_all_three_readings :
    ¬ OrdinarySupportNecessaryClaim ∧ ¬ ConvexSupportNecessaryClaim ∧
      ¬ EffectiveDomainNecessaryClaim :=
  ⟨not_ordinarySupportNecessaryClaim, not_convexSupportNecessaryClaim,
    not_effectiveDomainNecessaryClaim⟩

/-- An actual nondegenerate lattice probability law with all exponential moments and
an exact smooth finite convex-dual formula on the substantive interior. -/
theorem explicit_counterexample :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      (∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * x)) μ) ∧
      (∀ a : ℝ, ¬ (∀ᵐ x ∂μ, x = a)) ∧ LatticeLaw μ ∧
      interior (topologicalSupport μ) = ∅ ∧
      interior (convexHull ℝ (topologicalSupport μ)) = Ioo 0 1 ∧
      interior (effectiveDomain μ) = Ioo 0 1 ∧
      (Ioo (0 : ℝ) 1).Nonempty ∧
      ∃ f : ℝ → ℝ, ContDiffOn ℝ ∞ f (Ioo 0 1) ∧
        ∀ x ∈ Ioo (0 : ℝ) 1, cramerRate μ x = (f x : EReal) := by
  refine ⟨fairBernoulli, inferInstance, integrable_exp_fairBernoulli,
    fairBernoulli_not_ae_constant, fairBernoulli_lattice, interior_support_fairBernoulli,
    interior_convexHull_support_fairBernoulli, interior_effectiveDomain_fairBernoulli,
    ⟨1 / 2, by norm_num⟩, fairBernoulli_rate_smooth⟩

end Conjecture2802
