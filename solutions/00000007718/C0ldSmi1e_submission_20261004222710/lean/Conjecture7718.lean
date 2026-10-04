import Conjecture7718.Tiling
import Conjecture7718.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Disproof of the explicit positive-minimum clause of conjecture 00000007718.
The quantified class is a subclass of primitive three-letter substitutions:
genuine interval substitutions with full-rank matrices and simple positive
real spectrum. Refuting a universal lower bound on this subclass suffices.
-/

noncomputable section
open Polynomial Set

namespace Conjecture7718

/-- Ordered spectral data, tied to the actual complex characteristic polynomial
and to the largest and second-largest moduli in the actual complex spectrum. -/
def OrderedSpectralData (σ : Substitution) (p s t : ℝ) : Prop :=
  0 < t ∧ t < s ∧ s < p ∧
  (incidenceMatrix σ).charpoly = (X - C (p : ℂ)) * (X - C (s : ℂ)) * (X - C (t : ℂ)) ∧
  IsGreatest ((fun z : ℂ => ‖z‖) '' spectrum ℂ (incidenceMatrix σ)) p ∧
  IsGreatest ((fun z : ℂ => ‖z‖) '' (spectrum ℂ (incidenceMatrix σ) \ {(p : ℂ)})) s

theorem substitution_orderedSpectralData (m : ℕ) (hm : 1 ≤ m) :
    OrderedSpectralData (substitution m) (perronValue m) 3 1 := by
  exact ⟨by norm_num, by norm_num, perronValue_gt_three m hm,
    by simpa using incidence_charpoly m, perron_isGreatest m hm, second_isGreatest m hm⟩

/-- Actual positive spectral ratios of a certified subclass of primitive
three-letter geometric substitutions; full matrix rank is three as well. -/
def AdmissibleRatio (ρ : ℝ) : Prop :=
  ∃ (σ : Substitution) (q p s t : ℝ),
    PrimitiveSubstitution σ ∧ (∀ j, σ j ≠ []) ∧ UnitIntervalSubstitution σ q ∧
    (incidenceMatrix σ).rank = 3 ∧ OrderedSpectralData σ p s t ∧ ρ = s / p

def spectralRatio (m : ℕ) : ℝ := 3 / perronValue m

theorem spectralRatio_eq (m : ℕ) : spectralRatio m = 1 / ((m : ℝ) + 1) := by
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  dsimp [spectralRatio, perronValue]
  field_simp
  ring

theorem spectralRatio_pos (m : ℕ) : 0 < spectralRatio m := by
  rw [spectralRatio_eq]
  positivity

theorem spectralRatio_admissible (m : ℕ) (hm : 1 ≤ m) :
    AdmissibleRatio (spectralRatio m) := by
  exact ⟨substitution m, perronValue m, perronValue m, 3, 1,
    substitution_primitive m hm, substitution_nonempty m,
    substitution_unitInterval m, incidence_rank m,
    substitution_orderedSpectralData m hm, rfl⟩

def claimedMinimum : ℝ := (3 - Real.sqrt 5) / 2

theorem spectralRatio_two : spectralRatio 2 = 1 / 3 := by
  norm_num [spectralRatio_eq]

theorem one_third_lt_claimedMinimum : (1 : ℝ) / 3 < claimedMinimum := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  dsimp [claimedMinimum]
  nlinarith

theorem counterexample : ∃ ρ : ℝ, AdmissibleRatio ρ ∧ 0 < ρ ∧ ρ < claimedMinimum := by
  refine ⟨spectralRatio 2, spectralRatio_admissible 2 (by norm_num), spectralRatio_pos 2, ?_⟩
  rw [spectralRatio_two]
  exact one_third_lt_claimedMinimum

/-- A necessary consequence of the source's claimed minimum, restricted to
the certified subclass; this does not redefine its other conjuncts. -/
def ConjecturedPositiveLowerBound : Prop :=
  ∀ ρ : ℝ, AdmissibleRatio ρ → 0 < ρ → claimedMinimum ≤ ρ

theorem conjecture_00000007718_false : ¬ ConjecturedPositiveLowerBound := by
  intro h
  obtain ⟨ρ, ha, hp, hl⟩ := counterexample
  exact (not_le_of_gt hl) (h ρ ha hp)

/-- The stronger family result is exact and uses no numerical approximation. -/
theorem arbitrarily_small_positive_ratios (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ 0 < spectralRatio m ∧ spectralRatio m < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  refine ⟨n + 1, by omega, spectralRatio_pos _, ?_⟩
  rw [spectralRatio_eq]
  have hprod : 1 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
  apply (div_lt_iff₀ (by positivity : 0 < ((n + 1 : ℕ) : ℝ) + 1)).mpr
  push_cast
  nlinarith

theorem no_positive_universal_lower_bound (c : ℝ) (hc : 0 < c) :
    ∃ ρ : ℝ, AdmissibleRatio ρ ∧ 0 < ρ ∧ ρ < c := by
  obtain ⟨m, hm, hp, hl⟩ := arbitrarily_small_positive_ratios c hc
  exact ⟨spectralRatio m, spectralRatio_admissible m hm, hp, hl⟩

theorem no_least_positive_admissible_ratio :
    ¬ ∃ c : ℝ, AdmissibleRatio c ∧ 0 < c ∧
      ∀ ρ : ℝ, AdmissibleRatio ρ → 0 < ρ → c ≤ ρ := by
  rintro ⟨c, _, hc, hleast⟩
  obtain ⟨ρ, ha, hp, hl⟩ := no_positive_universal_lower_bound c hc
  exact (not_le_of_gt hl) (hleast ρ ha hp)

end Conjecture7718
