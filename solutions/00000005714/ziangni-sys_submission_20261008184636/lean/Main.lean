import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

noncomputable section
open MeasureTheory Real
open scoped Topology
namespace AlmgrenLinear

/-- The complex plane is the standard Euclidean real plane. -/
def u (z : ℂ) : ℝ := z.re
def polynomial : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0

theorem polynomial_representation (z : ℂ) :
    MvPolynomial.eval (fun i : Fin 2 => if i=0 then z.re else z.im) polynomial=u z := by
  simp [polynomial,u]

def gradientSquared (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  (deriv (fun x : ℝ => f ⟨x,z.im⟩) z.re)^2+
  (deriv (fun y : ℝ => f ⟨z.re,y⟩) z.im)^2

def laplacian (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  deriv (fun x => deriv (fun y : ℝ => f ⟨y,z.im⟩) x) z.re+
  deriv (fun x => deriv (fun y : ℝ => f ⟨z.re,y⟩) x) z.im

theorem gradient_squared_one (z : ℂ) : gradientSquared u z=1 := by
  simp [gradientSquared,u]
theorem harmonic (z : ℂ) : laplacian u z=0 := by
  simp [laplacian,u]

/-- Actual Dirichlet energy on the Euclidean disk, with Lebesgue area. -/
def energy (r : ℝ) : ℝ := ∫ z in Metric.ball (0 : ℂ) r, gradientSquared u z

def circle (r theta : ℝ) : ℂ := ⟨r*cos theta,r*sin theta⟩
def tangent (r theta : ℝ) : ℂ := ⟨-r*sin theta,r*cos theta⟩

theorem circle_derivative (r theta : ℝ) : HasDerivAt (circle r) (tangent r theta) theta := by
  convert (((hasDerivAt_cos theta).const_mul r).ofReal_comp).add
    ((((hasDerivAt_sin theta).const_mul r).ofReal_comp).mul_const Complex.I) using 1
  · funext x
    apply Complex.ext <;> simp only [circle,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
    <;> ring
  · apply Complex.ext <;> simp only [tangent,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
    <;> ring

theorem circle_norm_squared (r theta : ℝ) : ‖circle r theta‖^2=r^2 := by
  rw [Complex.sq_norm]
  simp only [circle,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  nlinarith [mul_self_nonneg r, cos_sq_add_sin_sq theta,
    congrArg (fun x : ℝ => r^2*x) (cos_sq_add_sin_sq theta)]

theorem tangent_norm (r theta : ℝ) (hr : 0<r) : ‖tangent r theta‖=r := by
  have hs : ‖tangent r theta‖^2=r^2 := by
    rw [Complex.sq_norm]
    simp only [tangent,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    nlinarith [congrArg (fun x : ℝ => r^2*x) (cos_sq_add_sin_sq theta)]
  nlinarith [norm_nonneg (tangent r theta)]

theorem circle_on_boundary (r theta : ℝ) (hr : 0<r) :
    circle r theta ∈ Metric.sphere (0 : ℂ) r := by
  simp only [Metric.mem_sphere,dist_zero_right]
  nlinarith [circle_norm_squared r theta,norm_nonneg (circle r theta)]

/-- The actual boundary L2 integral in angular coordinates with arclength density r. -/
def boundaryMass (r : ℝ) : ℝ := ∫ theta in (0 : ℝ)..2*Real.pi, (u (circle r theta))^2*r
def frequency (r : ℝ) : ℝ := r*energy r/boundaryMass r

theorem energy_exact (r : ℝ) (hr : 0<r) : energy r=Real.pi*r^2 := by
  simp [energy,gradient_squared_one,Measure.real,Complex.volume_ball,hr.le,mul_comm]

theorem boundary_exact (r : ℝ) : boundaryMass r=Real.pi*r^3 := by
  have hfun : (fun theta : ℝ => (u (circle r theta))^2*r)=
      (fun theta : ℝ => r^3*(cos theta)^2) := by
    funext theta
    dsimp [u,circle]
    ring
  rw [boundaryMass,hfun,intervalIntegral.integral_const_mul,integral_cos_sq]
  simp [sin_two_pi]
  ring

theorem boundary_positive (r : ℝ) (hr : 0<r) : 0<boundaryMass r := by
  rw [boundary_exact]
  positivity

theorem frequency_one (r : ℝ) (hr : 0<r) : frequency r=1 := by
  rw [frequency,energy_exact r hr,boundary_exact]
  field_simp [ne_of_gt hr,Real.pi_ne_zero]
  <;> ring

theorem frequency_derivative_zero (r : ℝ) (hr : 0<r) : deriv frequency r=0 := by
  have he : frequency =ᶠ[𝓝 r] (fun _ : ℝ => 1) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact frequency_one x hx
  rw [he.deriv_eq]
  simp

def Radial (f : ℂ → ℝ) : Prop := ∀ z w, ‖z‖=‖w‖ → f z=f w

theorem not_radial : ¬ Radial u := by
  intro h
  have he := h 1 Complex.I (by simp)
  norm_num [u] at he

theorem nonradial_at_every_radius (r : ℝ) (hr : 0<r) :
    ‖(r : ℂ)‖=‖(r : ℂ)*Complex.I‖ ∧ u r≠u ((r : ℂ)*Complex.I) := by
  constructor
  · simp [norm_mul]
  · simpa [u] using (ne_of_gt hr)

theorem not_strictly_increasing : ¬ StrictMonoOn frequency (Set.Ioi 0) := by
  intro h
  have he := h (by norm_num : (1:ℝ)∈Set.Ioi 0)
    (by norm_num : (2:ℝ)∈Set.Ioi 0) (by norm_num : (1:ℝ)<2)
  rw [frequency_one 1 (by norm_num),frequency_one 2 (by norm_num)] at he
  exact (lt_irrefl _ he)

theorem counterexample : (∀ z, laplacian u z=0) ∧
    (∀ r>0, boundaryMass r>0 ∧ frequency r=1 ∧ deriv frequency r=0) ∧ ¬ Radial u := by
  exact ⟨harmonic,fun r hr => ⟨boundary_positive r hr,frequency_one r hr,
    frequency_derivative_zero r hr⟩,not_radial⟩

#print axioms polynomial_representation
#print axioms harmonic
#print axioms gradient_squared_one
#print axioms circle_on_boundary
#print axioms circle_derivative
#print axioms tangent_norm
#print axioms energy_exact
#print axioms boundary_exact
#print axioms frequency_one
#print axioms frequency_derivative_zero
#print axioms not_radial
#print axioms nonradial_at_every_radius
#print axioms not_strictly_increasing
#print axioms counterexample
end AlmgrenLinear
