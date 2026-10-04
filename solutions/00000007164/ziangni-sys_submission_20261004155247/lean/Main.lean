import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Data.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Classical
noncomputable section
namespace GraphRadius

def star : SimpleGraph (Fin 3) where
  Adj u v := u ≠ v ∧ (u = 0 ∨ v = 0)
  symm := by
    intro u v h
    exact ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩
  loopless := by intro u h; exact h.1 rfl
instance : DecidableRel star.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (u = 0 ∨ v = 0)))
def triangle : SimpleGraph (Fin 3) := ⊤
instance : DecidableRel triangle.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v))

theorem star_connected : star.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact SimpleGraph.Adj.reachable (by decide)

theorem triangle_connected : triangle.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact SimpleGraph.Adj.reachable (by decide)

def edges (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)

theorem edge_counts : (edges star).card = 2 ∧ (edges triangle).card = 3 := by decide

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

theorem spectrum_det (M : Mat) (z : ℂ) :
    z ∈ spectrum ℂ M ↔ (algebraMap ℂ Mat z - M).det = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  simp

theorem star_determinant (z : ℂ) :
    (algebraMap ℂ Mat z - star.adjMatrix ℂ).det = z*(z^2-2) := by
  simp [Matrix.det_fin_three, Matrix.algebraMap_matrix_apply,
    SimpleGraph.adjMatrix, star]
  ring

theorem triangle_determinant (z : ℂ) :
    (algebraMap ℂ Mat z - triangle.adjMatrix ℂ).det = (z-2)*(z+1)^2 := by
  simp [Matrix.det_fin_three, Matrix.algebraMap_matrix_apply,
    SimpleGraph.adjMatrix, triangle]
  ring

theorem sqrt_two_square : (Real.sqrt 2 : ℂ)^2 = 2 := by
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))

theorem star_spectrum :
    spectrum ℂ (star.adjMatrix ℂ) = {0, (Real.sqrt 2 : ℂ), -(Real.sqrt 2 : ℂ)} := by
  ext z
  rw [spectrum_det, star_determinant]
  have hf : z^2-2 = (z-(Real.sqrt 2 : ℂ))*(z+(Real.sqrt 2 : ℂ)) := by
    calc
      z^2-2 = z^2-(Real.sqrt 2 : ℂ)^2 := by rw [sqrt_two_square]
      _ = _ := by ring
  rw [hf]
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg, Set.mem_insert_iff,
    Set.mem_singleton_iff]

theorem triangle_spectrum :
    spectrum ℂ (triangle.adjMatrix ℂ) = {(2 : ℂ), (-1 : ℂ)} := by
  ext z
  rw [spectrum_det, triangle_determinant]
  simp only [pow_two, mul_eq_zero, or_self, sub_eq_zero, add_eq_zero_iff_eq_neg,
    Set.mem_insert_iff, Set.mem_singleton_iff]

-- Standard finite-dimensional spectral radius: supremum of moduli of actual spectrum.
def radius (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] : ℝ :=
  sSup ((fun z : ℂ => ‖z‖) '' spectrum ℂ (G.adjMatrix ℂ))

theorem star_radius : radius star = Real.sqrt 2 := by
  rw [radius, star_spectrum]
  simp [Set.image_insert_eq, Complex.norm_real, Real.sqrt_nonneg, max_eq_right,
    csSup_insert, csSup_singleton]

theorem triangle_radius : radius triangle = 2 := by
  rw [radius, triangle_spectrum]
  simp only [Set.image_insert_eq, Set.image_singleton, norm_neg, norm_one, Complex.norm_two]
  norm_num [csSup_insert, csSup_singleton]
  change ‖(1 : ℂ)‖ ≤ (2 : ℝ)
  rw [show ‖(1 : ℂ)‖ = (1 : ℝ) from Complex.norm_of_nonneg (by norm_num)]
  norm_num

theorem radius_strict : radius star < radius triangle := by
  rw [star_radius, triangle_radius]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

def MaximizesOnThreeVertices (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] : Prop :=
  ∀ (H : SimpleGraph (Fin 3)) (hH : DecidableRel H.Adj), @radius H hH ≤ radius G

theorem star_not_maximal : ¬ MaximizesOnThreeVertices star := by
  intro h
  have hh := h triangle inferInstance
  exact (not_le_of_gt radius_strict) hh

theorem counterexample :
    star.Connected ∧ triangle.Connected ∧
    ((edges star).card = 2 ∧ (edges triangle).card = 3) ∧
    spectrum ℂ (star.adjMatrix ℂ) = {0, (Real.sqrt 2 : ℂ), -(Real.sqrt 2 : ℂ)} ∧
    spectrum ℂ (triangle.adjMatrix ℂ) = {(2 : ℂ), (-1 : ℂ)} ∧
    radius star < radius triangle ∧ ¬ MaximizesOnThreeVertices star :=
  ⟨star_connected, triangle_connected, edge_counts, star_spectrum,
    triangle_spectrum, radius_strict, star_not_maximal⟩

#print axioms star_connected
#print axioms edge_counts
#print axioms spectrum_det
#print axioms star_spectrum
#print axioms triangle_spectrum
#print axioms star_radius
#print axioms triangle_radius
#print axioms counterexample
end GraphRadius
