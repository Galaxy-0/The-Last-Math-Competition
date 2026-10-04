import Conjecture5960.Ensembles

noncomputable section
namespace Conjecture5960

def parameterA (i : Fin 2) : ℝ := if i = 0 then 0 else 1
def parameterB (i : Fin 2) : ℝ := if i = 0 then 1 / 2 else -1 / 2

theorem randomMatrixA_eq_parameter : randomMatrixA = matrixFamily ∘ parameterA := by
  funext i
  simp only [randomMatrixA, parameterA, Function.comp_apply]
  split_ifs <;> rfl

theorem randomMatrixB_eq_parameter : randomMatrixB = matrixFamily ∘ parameterB := by
  funext i
  simp only [randomMatrixB, parameterB, Function.comp_apply]
  split_ifs <;> rfl

/-- A concrete strengthened form of the source's full existential claim.
The parameter is continuous, genuinely varies on an interval, preserves the complete
spectrum at every real value, and realizes two non-Dirac ensembles whose actual
eigenvector-statistic pushforward measures differ. -/
def ParametricSeparation (F : ℝ → Mat2) (a b : Fin 2 → ℝ) : Prop :=
  Continuous F ∧
  Set.InjOn F (Set.Icc (0 : ℝ) 1) ∧
  (∀ t, (F t).IsSymm ∧
    (F t).charpoly = (Polynomial.X - Polynomial.C (1 : ℝ)) *
      (Polynomial.X - Polynomial.C (3 : ℝ)) ∧ spectrum ℝ (F t) = {1, 3}) ∧
  (∀ N : Mat2, (fairPMF.map (F ∘ a)).toMeasure ≠ MeasureTheory.Measure.dirac N) ∧
  (∀ N : Mat2, (fairPMF.map (F ∘ b)).toMeasure ≠ MeasureTheory.Measure.dirac N) ∧
  (fairPMF.map (F ∘ a)).map Matrix.charpoly = (fairPMF.map (F ∘ b)).map Matrix.charpoly ∧
  (fairPMF.map (F ∘ a)).map (spectrum ℝ) = (fairPMF.map (F ∘ b)).map (spectrum ℝ) ∧
  fairPMF.toMeasure.map (statistic ∘ (F ∘ a)) ≠
    fairPMF.toMeasure.map (statistic ∘ (F ∘ b))

theorem explicit_parametric_separation :
    ParametricSeparation matrixFamily parameterA parameterB := by
  unfold ParametricSeparation
  rw [← randomMatrixA_eq_parameter, ← randomMatrixB_eq_parameter,
    ← ensembleA_eq_map, ← ensembleB_eq_map]
  refine ⟨continuous_matrixFamily, matrixFamily_injOn_unitInterval, ?_,
    ensembleA_measure_not_dirac, ensembleB_measure_not_dirac,
    ensembles_same_charpoly_law, ensembles_same_spectrum_law,
    different_actual_statistic_pushforwards⟩
  intro t
  exact ⟨matrixFamily_isSymm t, charpoly_matrixFamily t, spectrum_matrixFamily t⟩

/-- Full existence, with both ensembles explicitly parametrized inside the same family. -/
theorem conjecture_5960 : ∃ (F : ℝ → Mat2) (a b : Fin 2 → ℝ), ParametricSeparation F a b :=
  ⟨matrixFamily, parameterA, parameterB, explicit_parametric_separation⟩

end Conjecture5960
