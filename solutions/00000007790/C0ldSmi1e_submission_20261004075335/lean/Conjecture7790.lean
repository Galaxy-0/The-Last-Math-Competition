import Conjecture7790.Law
import Conjecture7790.LogConcavity
import Conjecture7790.Moments
import Conjecture7790.Tail

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
namespace Conjecture7790

/-- A real probability law with a measurable log-concave density and isotropic moments. -/
def IsAdmissibleLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ IsIsotropic μ ∧
  ∃ f : ℝ → ℝ, Measurable f ∧ IsLogConcaveDensity f ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (f x))

theorem density_measurable : Measurable density := by
  unfold density
  exact Measurable.ite measurableSet_Ici
    ((measurable_id.add_const 1).neg.exp) measurable_const

theorem centeredExponential_admissible : IsAdmissibleLaw centeredExponential :=
  ⟨inferInstance, centeredExponential_isIsotropic,
    density, density_measurable, density_logConcave, centeredExponential_eq_withDensity⟩

/-- The one-dimensional consequence of the first conjectured concentration assertion.
Separate positive threshold and decay constants, and an arbitrary starting threshold,
make this weaker than the stated universal bound; disproving it suffices. -/
def OneDimensionalGaussianClaim : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ c : ℝ, 0 < c ∧ ∃ T : ℝ,
    ∀ μ : Measure ℝ, IsAdmissibleLaw μ →
      ∀ t : ℝ, 1 ≤ t → T ≤ t →
        μ.real {x : ℝ | A * t ≤ |x|} ≤ Real.exp (-c * t ^ 2)

/-- An explicit qualifying law defeats every choice of constants, even eventually.
This is a counterexample in dimension one, where sqrt(n)=1 and the norm is abs. -/
theorem conjecture7790_counterexample :
    IsAdmissibleLaw centeredExponential ∧
    ∀ A c T : ℝ, 0 < A → 0 < c →
      ∃ t : ℝ, 1 ≤ t ∧ T ≤ t ∧
        Real.exp (-c * t ^ 2) <
          centeredExponential.real {x : ℝ | A * t ≤ |x|} :=
  ⟨centeredExponential_admissible, gaussian_bound_fails⟩

theorem conjecture7790_disproof : ¬OneDimensionalGaussianClaim := by
  rintro ⟨A, hA, c, hc, T, hbound⟩
  obtain ⟨t, ht1, htT, hfail⟩ := gaussian_bound_fails A c T hA hc
  exact (not_lt_of_ge (hbound centeredExponential centeredExponential_admissible t ht1 htT)) hfail

end Conjecture7790
