import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

noncomputable section
open Set
namespace Besicovitch
abbrev E := EuclideanSpace ℝ (Fin 2)

def center (i : Fin 4) : E := ![!₂[1,0], !₂[0,1], !₂[-1,0], !₂[0,-1]] i
def radius : ℝ := 11 / 10
def ball (i : Fin 4) : Set E := Metric.ball (center i) radius

def CoversCenters (I : Finset (Fin 4)) : Prop :=
  ∀ i, ∃ j ∈ I, center i ∈ ball j

noncomputable def multiplicity (I : Finset (Fin 4)) (z : E) : ℕ := by
  classical
  exact (I.filter (fun i => z ∈ ball i)).card

theorem dimension : Module.finrank ℝ E = 2 := by simp [E]

theorem radius_pos : 0 < radius := by norm_num [radius]

theorem distance_squared (x y : E) : dist x y ^ 2 =
    (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
  rw [dist_eq_norm, PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem center_norm (i : Fin 4) : dist (center i) 0 = 1 := by
  have hs : dist (center i) 0 ^ 2 = 1 := by
    rw [distance_squared]
    fin_cases i <;> norm_num [center]
  nlinarith [dist_nonneg (x := center i) (y := (0 : E))]

theorem separated (i j : Fin 4) (h : i ≠ j) : 2 ≤ dist (center i) (center j) ^ 2 := by
  rw [distance_squared]
  fin_cases i <;> fin_cases j <;> norm_num [center] at h ⊢

theorem common_point (i : Fin 4) : (0 : E) ∈ ball i := by
  change dist (0 : E) (center i) < radius
  rw [dist_comm, center_norm]
  norm_num [radius]

theorem center_membership (i j : Fin 4) : center i ∈ ball j ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    have hs := separated i j hij
    have hd : dist (center i) (center j) < (11 / 10 : ℝ) := h
    have hsq := (sq_lt_sq₀ (dist_nonneg (x := center i) (y := center j))
      (show (0 : ℝ) ≤ 11 / 10 by norm_num)).2 hd
    norm_num at hsq
    linarith
  · rintro rfl
    exact Metric.mem_ball_self radius_pos

theorem full_cover : CoversCenters Finset.univ := by
  intro i
  exact ⟨i, Finset.mem_univ _, (center_membership i i).2 rfl⟩

theorem only_full_subcover (I : Finset (Fin 4)) (h : CoversCenters I) : I = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  obtain ⟨j, hj, hmem⟩ := h i
  have he := (center_membership i j).1 hmem
  simpa [he] using hj

theorem overlap_four (I : Finset (Fin 4)) (h : CoversCenters I) :
    multiplicity I 0 = 4 := by
  classical
  rw [only_full_subcover I h]
  simp [multiplicity, common_point]

theorem bound_fails (I : Finset (Fin 4)) (h : CoversCenters I) :
    Module.finrank ℝ E + 1 < multiplicity I 0 := by
  rw [dimension, overlap_four I h]
  norm_num

theorem no_bounded_subcover : ¬ ∃ I : Finset (Fin 4), CoversCenters I ∧
    ∀ z : E, multiplicity I z ≤ Module.finrank ℝ E + 1 := by
  rintro ⟨I, hI, hbound⟩
  exact (not_le_of_gt (bound_fails I hI)) (hbound 0)

#print axioms dimension
#print axioms distance_squared
#print axioms center_norm
#print axioms separated
#print axioms common_point
#print axioms center_membership
#print axioms full_cover
#print axioms only_full_subcover
#print axioms overlap_four
#print axioms no_bounded_subcover
end Besicovitch
