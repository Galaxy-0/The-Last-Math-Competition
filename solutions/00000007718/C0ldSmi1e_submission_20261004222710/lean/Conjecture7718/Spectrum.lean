import Conjecture7718.Substitution
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Matrix.Rank
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.Complex.Basic

/-! Complete complex spectra of the actual word-count matrices. -/

noncomputable section
open Matrix Polynomial Set

namespace Conjecture7718

def perronValue (m : ℕ) : ℝ := 3 * (m : ℝ) + 3

theorem perronValue_gt_three (m : ℕ) (hm : 1 ≤ m) : 3 < perronValue m := by
  have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  dsimp [perronValue]
  linarith

theorem incidence_charpoly (m : ℕ) :
    (incidenceMatrix (substitution m)).charpoly =
      (X - C (perronValue m : ℂ)) * (X - C 3) * (X - C 1) := by
  rw [incidenceMatrix_substitution]
  norm_num [Matrix.charpoly, Matrix.det_fin_three, Matrix.charmatrix_apply,
    Matrix.cons_val_two, Matrix.diagonal, Fin.ext_iff, perronValue]
  simp only [map_ofNat]
  ring

theorem incidence_resolvent_det (m : ℕ) (z : ℂ) :
    (algebraMap ℂ (Matrix Letter Letter ℂ) z - incidenceMatrix (substitution m)).det =
      (z - (perronValue m : ℂ)) * (z - 3) * (z - 1) := by
  rw [incidenceMatrix_substitution]
  norm_num [Matrix.det_fin_three, Matrix.algebraMap_matrix_apply,
    Matrix.sub_apply, Matrix.cons_val_two, Fin.ext_iff, perronValue]
  ring

theorem incidence_mem_spectrum_iff (m : ℕ) (z : ℂ) :
    z ∈ spectrum ℂ (incidenceMatrix (substitution m)) ↔
      z = (perronValue m : ℂ) ∨ z = 3 ∨ z = 1 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_not, incidence_resolvent_det]
  simp only [mul_eq_zero, sub_eq_zero]
  tauto

theorem incidence_det (m : ℕ) :
    (incidenceMatrix (substitution m)).det = 3 * (perronValue m : ℂ) := by
  rw [incidenceMatrix_substitution]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, perronValue]
  ring

theorem incidence_rank (m : ℕ) : (incidenceMatrix (substitution m)).rank = 3 := by
  have hp : 0 < perronValue m := by
    dsimp [perronValue]
    positivity
  have hn : (perronValue m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  have hu : IsUnit (incidenceMatrix (substitution m)) := by
    rw [Matrix.isUnit_iff_isUnit_det, incidence_det, isUnit_iff_ne_zero]
    exact mul_ne_zero (by norm_num) hn
  simpa [Letter] using Matrix.rank_of_isUnit (incidenceMatrix (substitution m)) hu

/-- A strictly positive vector is an actual Perron eigenvector. -/
theorem incidence_mulVec_one (m : ℕ) :
    incidenceMatrix (substitution m) *ᵥ (fun _ : Letter => (1 : ℂ)) =
      (perronValue m : ℂ) • (fun _ : Letter => (1 : ℂ)) := by
  rw [incidenceMatrix_substitution]
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, perronValue] <;> ring

theorem incidence_positive_eigenvector (m : ℕ) :
    ∃ v : Letter → ℝ, (∀ i, 0 < v i) ∧
      incidenceMatrix (substitution m) *ᵥ (fun i => (v i : ℂ)) =
        (perronValue m : ℂ) • (fun i => (v i : ℂ)) := by
  exact ⟨fun _ => 1, by intro i; norm_num, incidence_mulVec_one m⟩

/-- The largest modulus in the actual complex spectrum is the Perron value. -/
theorem perron_isGreatest (m : ℕ) (hm : 1 ≤ m) :
    IsGreatest ((fun z : ℂ => ‖z‖) '' spectrum ℂ (incidenceMatrix (substitution m)))
      (perronValue m) := by
  have hp := perronValue_gt_three m hm
  constructor
  · refine ⟨(perronValue m : ℂ), (incidence_mem_spectrum_iff m _).mpr (Or.inl rfl), ?_⟩
    simp [abs_of_pos (by linarith : 0 < perronValue m)]
  · rintro r ⟨z, hz, rfl⟩
    rcases (incidence_mem_spectrum_iff m z).mp hz with rfl | rfl | rfl
    · simp [abs_of_pos (by linarith : 0 < perronValue m)]
    · norm_num
      linarith
    · norm_num
      linarith

/-- After removing the Perron eigenvalue, the largest remaining modulus is three. -/
theorem second_isGreatest (m : ℕ) (hm : 1 ≤ m) :
    IsGreatest ((fun z : ℂ => ‖z‖) ''
      (spectrum ℂ (incidenceMatrix (substitution m)) \ {(perronValue m : ℂ)})) 3 := by
  have hp := perronValue_gt_three m hm
  have hneq : (3 : ℂ) ≠ (perronValue m : ℂ) := by
    intro he
    have : (3 : ℝ) = perronValue m := by exact_mod_cast he
    linarith
  constructor
  · refine ⟨3, ⟨(incidence_mem_spectrum_iff m _).mpr (Or.inr (Or.inl rfl)), ?_⟩, ?_⟩
    · simpa using hneq
    · norm_num
  · rintro r ⟨z, ⟨hz, hn⟩, rfl⟩
    rcases (incidence_mem_spectrum_iff m z).mp hz with rfl | rfl | rfl
    · exact False.elim (hn (by simp))
    · norm_num
    · norm_num

end Conjecture7718
