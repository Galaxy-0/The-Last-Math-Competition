import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Set MeasureTheory
open scoped Pointwise
noncomputable section
namespace MixedAreaCounterexample
abbrev Plane := Fin 2 → ℝ
abbrev EPlane := EuclideanSpace ℝ (Fin 2)
def square (a : ℝ) : Set Plane := Icc 0 (fun _ => a)
def area (A : Set Plane) : ℝ := (volume A).toReal
def combination (s t : ℝ) (A B : Set Plane) : Set Plane :=
  {z | ∃ x ∈ A, ∃ y ∈ B, z = s • x + t • y}
def mixedArea (A B : Set Plane) : ℝ :=
  (area (combination 1 1 A B) - area A - area B) / 2

theorem square_compact (a : ℝ) : IsCompact (square a) := isCompact_Icc
theorem square_convex (a : ℝ) : Convex ℝ (square a) := convex_Icc _ _
theorem square_interior (a : ℝ) (ha : 0 < a) : (interior (square a)).Nonempty := by
  let U : Set Plane := ⋂ i : Fin 2, {x | 0 < x i ∧ x i < a}
  have hu : IsOpen U := isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)
  have hs : U ⊆ square a := by
    intro x hx
    simp only [U, mem_iInter, mem_setOf_eq] at hx
    exact ⟨fun i => (hx i).1.le, fun i => (hx i).2.le⟩
  refine ⟨fun _ => a / 2, interior_mono hs ?_⟩
  rw [hu.interior_eq]
  simp only [U, mem_iInter, mem_setOf_eq]
  intro i
  constructor <;> linarith

theorem area_square (a : ℝ) (ha : 0 ≤ a) : area (square a) = a ^ 2 := by
  change (volume (Icc (fun _ : Fin 2 => (0 : ℝ)) (fun _ => a))).toReal = a^2
  rw [Real.volume_Icc_pi_toReal (fun _ => ha)]
  simp [Fin.prod_univ_two, pow_two]

theorem combination_squares (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    combination s t (square 1) (square 2) = square (s + 2*t) := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    constructor <;> intro i
    · exact add_nonneg (mul_nonneg hs (hx.1 i)) (mul_nonneg ht (hy.1 i))
    · change s * x i + t * y i ≤ s + 2*t
      have h1 := mul_le_mul_of_nonneg_left (hx.2 i) hs
      have h2 := mul_le_mul_of_nonneg_left (hy.2 i) ht
      dsimp at h1 h2
      nlinarith
  · intro hz
    by_cases hzero : s + 2*t = 0
    · have hsz : s = 0 := by linarith
      have htz : t = 0 := by linarith
      have hz0 : z = 0 := by
        ext i
        change z i = 0
        have h1 := hz.1 i
        have h2 := hz.2 i
        dsimp at h1 h2
        linarith
      subst s; subst t; subst z
      exact ⟨0, by simp [square, Pi.le_def], 0, by simp [square, Pi.le_def], by simp⟩
    · have hd : 0 < s + 2*t := lt_of_le_of_ne (by positivity) (Ne.symm hzero)
      let x : Plane := fun i => z i / (s + 2*t)
      let y : Plane := fun i => 2 * (z i / (s + 2*t))
      have hx : x ∈ square 1 := by
        constructor <;> intro i
        · exact div_nonneg (hz.1 i) hd.le
        · change z i / (s + 2*t) ≤ 1
          exact (div_le_one hd).2 (hz.2 i)
      have hy : y ∈ square 2 := by
        constructor <;> intro i
        · exact mul_nonneg (by norm_num) (hx.1 i)
        · change 2 * x i ≤ 2
          have hi := hx.2 i
          dsimp at hi
          linarith
      refine ⟨x, hx, y, hy, ?_⟩
      ext i
      change z i = s * (z i / (s + 2*t)) + t * (2 * (z i / (s + 2*t)))
      field_simp
      ring

theorem volume_polynomial (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    area (combination s t (square 1) (square 2)) = s^2 + 2*s*t*2 + t^2*4 := by
  rw [combination_squares s t hs ht, area_square _ (by positivity)]
  ring

theorem mixed_values : area (square 1) = 1 ∧ mixedArea (square 1) (square 2) = 2 ∧
    area (square 2) = 4 := by
  norm_num [mixedArea, volume_polynomial, area_square]

theorem af_equality : mixedArea (square 1) (square 2)^2 =
    area (square 1) * area (square 2) := by
  rw [mixed_values.1, mixed_values.2.1, mixed_values.2.2]
  norm_num

def euclideanSquare (a : ℝ) : Set EPlane := {x | (fun i => x i) ∈ square a}
def coordinates : EPlane ≃L[ℝ] Plane := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)

theorem euclidean_square_compact (a : ℝ) : IsCompact (euclideanSquare a) :=
  coordinates.toHomeomorph.isCompact_preimage.mpr (square_compact a)

theorem euclidean_square_convex (a : ℝ) : Convex ℝ (euclideanSquare a) :=
  (square_convex a).linear_preimage coordinates.toLinearMap

theorem euclidean_square_interior (a : ℝ) (ha : 0 < a) :
    (interior (euclideanSquare a)).Nonempty := by
  change (interior (coordinates.toHomeomorph ⁻¹' square a)).Nonempty
  rw [← coordinates.toHomeomorph.preimage_interior]
  obtain ⟨x, hx⟩ := square_interior a ha
  exact ⟨coordinates.symm x, by simpa using hx⟩

theorem euclidean_volume (a : ℝ) : volume (euclideanSquare a) = volume (square a) :=
  (PiLp.volume_preserving_equiv (Fin 2)).measure_preimage measurableSet_Icc.nullMeasurableSet
def Congruent (A B : Set EPlane) : Prop := ∃ F : EPlane ≃ᵢ EPlane, F '' A = B

theorem dist_sq (x y : EPlane) : dist x y ^ 2 =
    (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem square_one_dist_bound (x y : EPlane) (hx : x ∈ euclideanSquare 1)
    (hy : y ∈ euclideanSquare 1) : dist x y ^ 2 ≤ 2 := by
  rw [dist_sq]
  have h0 : (x 0 - y 0)^2 ≤ 1 := by
    have hx0 := hx.1 0; have hx1 := hx.2 0
    have hy0 := hy.1 0; have hy1 := hy.2 0
    dsimp at hx0 hx1 hy0 hy1
    nlinarith [sq_nonneg (x 0 - y 0 - 1), mul_nonneg (sub_nonneg.mpr (show x 0 - y 0 ≤ 1 by linarith)) (show 0 ≤ x 0 - y 0 + 1 by linarith)]
  have h1 : (x 1 - y 1)^2 ≤ 1 := by
    have hx0 := hx.1 1; have hx1 := hx.2 1
    have hy0 := hy.1 1; have hy1 := hy.2 1
    dsimp at hx0 hx1 hy0 hy1
    nlinarith [mul_nonneg (sub_nonneg.mpr (show x 1 - y 1 ≤ 1 by linarith)) (show 0 ≤ x 1 - y 1 + 1 by linarith)]
  linarith

theorem not_congruent : ¬ Congruent (euclideanSquare 1) (euclideanSquare 2) := by
  rintro ⟨F, hF⟩
  let p : EPlane := 0
  let q : EPlane := (WithLp.equiv 2 Plane).symm (fun _ : Fin 2 => (2 : ℝ))
  have hp : p ∈ euclideanSquare 2 := by simp [p, euclideanSquare, square, Pi.le_def]
  have hq : q ∈ euclideanSquare 2 := by simp [q, euclideanSquare, square, Pi.le_def]
  rw [← hF] at hp hq
  obtain ⟨x, hx, hxp⟩ := hp
  obtain ⟨y, hy, hyq⟩ := hq
  have hb := square_one_dist_bound x y hx hy
  have he : dist p q = dist x y := by rw [← hxp, ← hyq, F.dist_eq]
  have hv : dist p q ^ 2 = 8 := by rw [dist_sq]; norm_num [p, q]
  rw [he] at hv
  linarith

#print axioms square_compact
#print axioms square_convex
#print axioms square_interior
#print axioms volume_polynomial
#print axioms mixed_values
#print axioms af_equality
#print axioms euclidean_square_compact
#print axioms euclidean_square_convex
#print axioms euclidean_square_interior
#print axioms euclidean_volume
#print axioms dist_sq
#print axioms not_congruent
end MixedAreaCounterexample
