import Conjecture5960.Eigenvectors
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.NormNum

open MeasureTheory
open scoped ENNReal Classical

namespace Conjecture5960

noncomputable section

instance matrixMeasurableSpace : MeasurableSpace Mat2 :=
  inferInstanceAs (MeasurableSpace (Fin 2 → Fin 2 → ℝ))

instance matrixBorelSpace : BorelSpace Mat2 :=
  inferInstanceAs (BorelSpace (Fin 2 → Fin 2 → ℝ))

/-- A fair two-point sample space. -/
def fairPMF : PMF (Fin 2) := PMF.uniformOfFintype (Fin 2)

@[simp] theorem fairPMF_apply (i : Fin 2) : fairPMF i = (1 / 2 : ℝ≥0∞) := by
  norm_num [fairPMF, PMF.uniformOfFintype_apply]

/-- The genuine probability law obtained by choosing either value fairly. -/
def twoPointLaw {α : Type*} (x y : α) : PMF α :=
  fairPMF.map (fun i => if i = 0 then x else y)

theorem twoPointLaw_apply {α : Type*} (x y z : α) :
    twoPointLaw x y z =
      (if z = x then (1 / 2 : ℝ≥0∞) else 0) +
      (if z = y then (1 / 2 : ℝ≥0∞) else 0) := by
  classical
  simp [twoPointLaw, PMF.map_apply, tsum_fintype, Fin.sum_univ_two]

theorem map_twoPointLaw {α β : Type*} (f : α → β) (x y : α) :
    (twoPointLaw x y).map f = twoPointLaw (f x) (f y) := by
  classical
  rw [twoPointLaw, PMF.map_comp]
  congr 1
  funext i
  simp only [Function.comp_apply]
  split_ifs <;> rfl

@[simp] theorem twoPointLaw_self {α : Type*} (x : α) :
    twoPointLaw x x = PMF.pure x := by
  simp only [twoPointLaw, ite_self]
  exact PMF.map_const fairPMF x

theorem twoPointLaw_ne_pure {α : Type*} {x y : α} (hxy : x ≠ y) (z : α) :
    twoPointLaw x y ≠ PMF.pure z := by
  classical
  intro h
  have hv := congrArg (fun p : PMF α => p x) h
  change twoPointLaw x y x = PMF.pure z x at hv
  have hxmass : twoPointLaw x y x = (1 / 2 : ℝ≥0∞) := by
    simp [twoPointLaw_apply, hxy]
  rw [hxmass, PMF.pure_apply] at hv
  by_cases hxz : x = z <;> norm_num [hxz] at hv

theorem twoPointLaw_toMeasure_not_dirac {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {x y : α} (hxy : x ≠ y) (z : α) :
    (twoPointLaw x y).toMeasure ≠ Measure.dirac z := by
  intro h
  apply twoPointLaw_ne_pure hxy z
  apply PMF.toMeasure_injective
  simpa only [PMF.toMeasure_pure] using h

theorem twoPointLaw_measure_map {α : Type*} [MeasurableSpace α] (x y : α) :
    fairPMF.toMeasure.map (fun i : Fin 2 => if i = 0 then x else y) =
      (twoPointLaw x y).toMeasure := by
  exact PMF.toMeasure_map _ fairPMF (measurable_of_finite _)

/-- The first random matrix, on the common fair sample space. -/
def randomMatrixA (i : Fin 2) : Mat2 :=
  if i = 0 then matrixFamily 0 else matrixFamily 1

/-- The second random matrix, with two distinct tilted eigendirections. -/
def randomMatrixB (i : Fin 2) : Mat2 :=
  if i = 0 then matrixFamily (1 / 2) else matrixFamily (-1 / 2)

/-- The actual law of the first matrix ensemble. -/
def ensembleA : PMF Mat2 := twoPointLaw (matrixFamily 0) (matrixFamily 1)

/-- The actual law of the second matrix ensemble. -/
def ensembleB : PMF Mat2 :=
  twoPointLaw (matrixFamily (1 / 2)) (matrixFamily (-1 / 2))

theorem ensembleA_eq_map : ensembleA = fairPMF.map randomMatrixA := rfl

theorem ensembleB_eq_map : ensembleB = fairPMF.map randomMatrixB := rfl

theorem matrixFamily_zero_ne_one : matrixFamily 0 ≠ matrixFamily 1 := by
  intro h
  have he := congrArg (fun A : Mat2 => A 0 0) h
  norm_num [matrixFamily_explicit, cosine, sine] at he

theorem matrixFamily_half_ne_neg_half : matrixFamily (1 / 2) ≠ matrixFamily (-1 / 2) := by
  intro h
  have he := congrArg (fun A : Mat2 => A 0 1) h
  norm_num [matrixFamily_explicit, cosine, sine] at he

theorem ensembleA_ne_pure (A : Mat2) : ensembleA ≠ PMF.pure A :=
  twoPointLaw_ne_pure matrixFamily_zero_ne_one A

theorem ensembleB_ne_pure (A : Mat2) : ensembleB ≠ PMF.pure A :=
  twoPointLaw_ne_pure matrixFamily_half_ne_neg_half A

theorem randomMatrixA_not_constant : ¬ ∃ A : Mat2, ∀ i, randomMatrixA i = A := by
  rintro ⟨A, h⟩
  have hh := (h 0).trans (h 1).symm
  apply matrixFamily_zero_ne_one
  simpa [randomMatrixA] using hh

theorem randomMatrixB_not_constant : ¬ ∃ A : Mat2, ∀ i, randomMatrixB i = A := by
  rintro ⟨A, h⟩
  have hh := (h 0).trans (h 1).symm
  apply matrixFamily_half_ne_neg_half
  simpa [randomMatrixB] using hh

theorem ensembleA_charpoly_law :
    ensembleA.map Matrix.charpoly =
      PMF.pure ((Polynomial.X - Polynomial.C (1 : ℝ)) *
        (Polynomial.X - Polynomial.C (3 : ℝ))) := by
  simp only [ensembleA, map_twoPointLaw, charpoly_matrixFamily, twoPointLaw_self]

theorem ensembleB_charpoly_law :
    ensembleB.map Matrix.charpoly =
      PMF.pure ((Polynomial.X - Polynomial.C (1 : ℝ)) *
        (Polynomial.X - Polynomial.C (3 : ℝ))) := by
  simp only [ensembleB, map_twoPointLaw, charpoly_matrixFamily, twoPointLaw_self]

theorem ensembleA_spectrum_law :
    ensembleA.map (spectrum ℝ) = PMF.pure ({1, 3} : Set ℝ) := by
  simp only [ensembleA, map_twoPointLaw, spectrum_matrixFamily, twoPointLaw_self]

theorem ensembleB_spectrum_law :
    ensembleB.map (spectrum ℝ) = PMF.pure ({1, 3} : Set ℝ) := by
  simp only [ensembleB, map_twoPointLaw, spectrum_matrixFamily, twoPointLaw_self]

theorem ensembles_same_spectrum_law :
    ensembleA.map (spectrum ℝ) = ensembleB.map (spectrum ℝ) := by
  rw [ensembleA_spectrum_law, ensembleB_spectrum_law]

theorem ensembles_same_charpoly_law :
    ensembleA.map Matrix.charpoly = ensembleB.map Matrix.charpoly := by
  rw [ensembleA_charpoly_law, ensembleB_charpoly_law]

theorem randomMatrixA_measurable : Measurable randomMatrixA := measurable_of_finite _

theorem randomMatrixB_measurable : Measurable randomMatrixB := measurable_of_finite _

theorem ensembleA_measure_map : fairPMF.toMeasure.map randomMatrixA = ensembleA.toMeasure :=
  twoPointLaw_measure_map _ _

theorem ensembleB_measure_map : fairPMF.toMeasure.map randomMatrixB = ensembleB.toMeasure :=
  twoPointLaw_measure_map _ _

theorem ensembleA_measure_not_dirac (A : Mat2) : ensembleA.toMeasure ≠ Measure.dirac A :=
  twoPointLaw_toMeasure_not_dirac matrixFamily_zero_ne_one A

theorem ensembleB_measure_not_dirac (A : Mat2) : ensembleB.toMeasure ≠ Measure.dirac A :=
  twoPointLaw_toMeasure_not_dirac matrixFamily_half_ne_neg_half A

/-- Exact law of the intrinsic squared projection in the first ensemble. -/
theorem ensembleA_statistic_law :
    ensembleA.map statistic = twoPointLaw (1 : ℝ) 0 := by
  rw [ensembleA, map_twoPointLaw, statistic_matrixFamily, statistic_matrixFamily]
  norm_num [cosine]

/-- Exact law of the intrinsic squared projection in the second ensemble. -/
theorem ensembleB_statistic_law :
    ensembleB.map statistic = PMF.pure (9 / 25 : ℝ) := by
  rw [ensembleB, map_twoPointLaw, statistic_matrixFamily, statistic_matrixFamily]
  norm_num [cosine]

/-- The first eigenline is perpendicular to the first axis with probability one half. -/
theorem ensembleA_statistic_zero : (ensembleA.map statistic) 0 = (1 / 2 : ℝ≥0∞) := by
  rw [ensembleA_statistic_law]
  norm_num [twoPointLaw_apply]

/-- That event never occurs in the second ensemble. -/
theorem ensembleB_statistic_zero : (ensembleB.map statistic) 0 = 0 := by
  rw [ensembleB_statistic_law]
  norm_num [PMF.pure_apply]

theorem ensembles_different_statistic_laws :
    ensembleA.map statistic ≠ ensembleB.map statistic := by
  intro h
  have hz := congrArg (fun p : PMF ℝ => p 0) h
  change (ensembleA.map statistic) 0 = (ensembleB.map statistic) 0 at hz
  rw [ensembleA_statistic_zero, ensembleB_statistic_zero] at hz
  norm_num at hz

theorem ensembles_distinct : ensembleA ≠ ensembleB := by
  intro h
  apply ensembles_different_statistic_laws
  rw [h]

theorem statistic_randomMatrixA_measurable : Measurable (statistic ∘ randomMatrixA) :=
  measurable_of_finite _

theorem statistic_randomMatrixB_measurable : Measurable (statistic ∘ randomMatrixB) :=
  measurable_of_finite _

/-- The PMF calculation is the actual observable law on the fair sample space. -/
theorem ensembleA_statistic_measure_map :
    fairPMF.toMeasure.map (statistic ∘ randomMatrixA) =
      (ensembleA.map statistic).toMeasure := by
  rw [PMF.toMeasure_map _ fairPMF statistic_randomMatrixA_measurable]
  rw [ensembleA_eq_map, PMF.map_comp]

theorem ensembleB_statistic_measure_map :
    fairPMF.toMeasure.map (statistic ∘ randomMatrixB) =
      (ensembleB.map statistic).toMeasure := by
  rw [PMF.toMeasure_map _ fairPMF statistic_randomMatrixB_measurable]
  rw [ensembleB_eq_map, PMF.map_comp]

theorem ensembles_different_statistic_measures :
    (ensembleA.map statistic).toMeasure ≠ (ensembleB.map statistic).toMeasure := by
  intro h
  exact ensembles_different_statistic_laws (PMF.toMeasure_injective h)

theorem different_actual_statistic_pushforwards :
    fairPMF.toMeasure.map (statistic ∘ randomMatrixA) ≠
      fairPMF.toMeasure.map (statistic ∘ randomMatrixB) := by
  rw [ensembleA_statistic_measure_map, ensembleB_statistic_measure_map]
  exact ensembles_different_statistic_measures

end

end Conjecture5960
