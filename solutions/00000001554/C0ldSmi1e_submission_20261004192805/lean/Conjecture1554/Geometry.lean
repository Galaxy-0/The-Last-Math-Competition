import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
namespace Conjecture1554

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- All three side lengths are actual distances in the Euclidean plane. -/
def unitEquilateral (p q r : Plane) : Prop :=
  dist p q = 1 ∧ dist q r = 1 ∧ dist r p = 1

def height (p : Plane) : ℝ := p 1

def stripWidth : ℝ := Real.sqrt 3 / 2

theorem stripWidth_pos : 0 < stripWidth := by
  unfold stripWidth
  positivity

theorem stripWidth_sq : stripWidth ^ 2 = (3 / 4 : ℝ) := by
  unfold stripWidth
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- Coordinate expansion of the genuine Euclidean distance. -/
theorem dist_sq_coordinates (p q : Plane) :
    dist p q ^ 2 = (p 0 - q 0)^2 + (p 1 - q 1)^2 := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs]
  exact Real.sq_sqrt (by positivity)

/-- The heights of a unit equilateral triangle satisfy a rotation-independent identity. -/
theorem height_identity {p q r : Plane} (h : unitEquilateral p q r) :
    (height q-height p)^2 - (height q-height p)*(height r-height p) +
      (height r-height p)^2 = (3 / 4 : ℝ) := by
  obtain ⟨hpq, hqr, hrp⟩ := h
  have h₁ := dist_sq_coordinates p q
  have h₂ := dist_sq_coordinates q r
  have h₃ := dist_sq_coordinates r p
  rw [hpq] at h₁
  rw [hqr] at h₂
  rw [hrp] at h₃
  let x := q 0 - p 0
  let y := q 1 - p 1
  let z := r 0 - p 0
  let t := r 1 - p 1
  have hu : x^2 + y^2 = 1 := by dsimp [x, y]; nlinarith only [h₁]
  have hv : z^2 + t^2 = 1 := by dsimp [z, t]; nlinarith only [h₃]
  have huv : x*z + y*t = 1/2 := by dsimp [x, y, z, t]; nlinarith only [h₁, h₂, h₃]
  have hprod : (x*z)^2 = x^2*z^2 := by ring
  have hx : x^2 = 1-y^2 := by linarith only [hu]
  have hz : z^2 = 1-t^2 := by linarith only [hv]
  have hxz : x*z = 1/2-y*t := by linarith only [huv]
  rw [hxz, hx, hz] at hprod
  change y^2-y*t+t^2 = _
  nlinarith only [hprod]

/-- The height gaps of a vertically ordered triangle satisfy the positive-term identity. -/
theorem ordered_height_identity {p q r : Plane} (h : unitEquilateral p q r) :
    (height q-height p)^2 + (height q-height p)*(height r-height q) +
      (height r-height q)^2 = (3 / 4 : ℝ) := by
  have hh := height_identity h
  nlinarith only [hh]

/-- Both adjacent height gaps are at most one strip width; the total span is at least one. -/
theorem ordered_height_bounds {p q r : Plane} (h : unitEquilateral p q r)
    (hpq : height p ≤ height q) (hqr : height q ≤ height r) :
    height q-height p ≤ stripWidth ∧ height r-height q ≤ stripWidth ∧
      stripWidth ≤ height r-height p := by
  have hh := ordered_height_identity h
  have hw := stripWidth_sq
  have hwpos := stripWidth_pos
  have ha : 0 ≤ height q-height p := sub_nonneg.mpr hpq
  have hb : 0 ≤ height r-height q := sub_nonneg.mpr hqr
  have hab := mul_nonneg ha hb
  constructor
  · nlinarith [sq_nonneg (height r-height q)]
  constructor
  · nlinarith [sq_nonneg (height q-height p)]
  · nlinarith

end Conjecture1554
