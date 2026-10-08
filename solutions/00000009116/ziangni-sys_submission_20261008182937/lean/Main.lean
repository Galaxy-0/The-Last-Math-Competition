import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

noncomputable section
open MeasureTheory
namespace RadonEven

abbrev Plane := ℝ × ℝ
def gaussian (x : Plane) : ℝ := Real.exp (-(x.1^2+x.2^2))

/-- Unit-speed coordinates on the line with normal (cos theta,sin theta)
and signed offset s. Lebesgue measure in t is Euclidean arclength. -/
def linePoint (theta s t : ℝ) : Plane :=
  (s*Real.cos theta-t*Real.sin theta, s*Real.sin theta+t*Real.cos theta)

/-- The genuine planar hyperplane Radon integral, in normal-angle coordinates. -/
def radon (f : Plane → ℝ) (theta s : ℝ) : ℝ := ∫ t : ℝ, f (linePoint theta s t)

theorem normal_unit (theta : ℝ) : Real.cos theta^2+Real.sin theta^2=1 :=
  Real.cos_sq_add_sin_sq theta

theorem point_on_line (theta s t : ℝ) :
    (linePoint theta s t).1*Real.cos theta+
      (linePoint theta s t).2*Real.sin theta=s := by
  dsimp [linePoint]
  calc
    _ = s*(Real.cos theta^2+Real.sin theta^2) := by ring
    _ = s := by rw [normal_unit]; ring

theorem line_speed_one (theta : ℝ) : (-Real.sin theta)^2+Real.cos theta^2=1 := by
  nlinarith [normal_unit theta]

theorem line_squared_radius (theta s t : ℝ) :
    (linePoint theta s t).1^2+(linePoint theta s t).2^2=s^2+t^2 := by
  dsimp [linePoint]
  calc
    _ = (s^2+t^2)*(Real.cos theta^2+Real.sin theta^2) := by ring
    _ = s^2+t^2 := by rw [normal_unit]; ring

theorem gaussian_on_line (theta s t : ℝ) :
    gaussian (linePoint theta s t)=Real.exp (-s^2)*Real.exp (-t^2) := by
  rw [gaussian, line_squared_radius, neg_add, Real.exp_add]

theorem slice_integrable (theta s : ℝ) : Integrable (fun t => gaussian (linePoint theta s t)) := by
  have h : Integrable (fun t : ℝ => Real.exp (-t^2)) := by
    simpa using (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ)<1))
  simpa only [gaussian_on_line] using h.const_mul (Real.exp (-s^2))

theorem radon_gaussian (theta s : ℝ) :
    radon gaussian theta s=Real.exp (-s^2)*Real.sqrt Real.pi := by
  unfold radon
  simp_rw [gaussian_on_line]
  rw [integral_const_mul]
  have h : (∫ t : ℝ, Real.exp (-t^2))=Real.sqrt Real.pi := by
    simpa using integral_gaussian (1 : ℝ)
  rw [h]

theorem radon_positive (theta s : ℝ) : 0 < radon gaussian theta s := by
  rw [radon_gaussian]
  exact mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 Real.pi_pos)

/-- The actual constant polynomial generating the degree-zero spherical harmonic. -/
def harmonicPolynomial : MvPolynomial (Fin 2) ℝ := 1
def harmonicFunction (x : Plane) : ℝ :=
  MvPolynomial.eval (fun i : Fin 2 => if i=0 then x.1 else x.2) harmonicPolynomial

theorem harmonic_value (x : Plane) : harmonicFunction x=1 := by
  simp [harmonicFunction, harmonicPolynomial]

theorem polynomial_degree_zero : harmonicPolynomial.totalDegree=0 := by
  simp [harmonicPolynomial]

theorem homogeneous_degree_zero (r : ℝ) (x : Plane) :
    harmonicFunction (r*x.1,r*x.2)=r^0*harmonicFunction x := by
  simp [harmonic_value]

/-- The actual two-dimensional Laplacian, computed by second partial derivatives. -/
def laplacian (f : Plane → ℝ) (x : Plane) : ℝ :=
  deriv (fun u => deriv (fun v => f (v,x.2)) u) x.1 +
  deriv (fun u => deriv (fun v => f (x.1,v)) u) x.2

theorem polynomial_harmonic (x : Plane) : laplacian harmonicFunction x=0 := by
  simp [laplacian, harmonic_value]

theorem angular_factor (theta : ℝ) :
    harmonicFunction (Real.cos theta,Real.sin theta)=1 := harmonic_value _

/-- The Gaussian is a pure degree-zero angular mode with radial profile exp(-r^2). -/
theorem gaussian_degree_zero_mode (r theta : ℝ) :
    gaussian (r*Real.cos theta,r*Real.sin theta)=
      Real.exp (-r^2)*harmonicFunction (Real.cos theta,Real.sin theta) := by
  rw [harmonic_value, mul_one]
  unfold gaussian
  dsimp
  congr 1
  calc
    _ = -(r^2*(Real.cos theta^2+Real.sin theta^2)) := by ring
    _ = -r^2 := by rw [normal_unit]; ring

theorem output_degree_zero (theta s : ℝ) : radon gaussian theta s=radon gaussian 0 s := by
  rw [radon_gaussian, radon_gaussian]

theorem even_degree_survives : Even harmonicPolynomial.totalDegree ∧
    (∀ x, laplacian harmonicFunction x=0) ∧
    (∀ r theta, gaussian (r*Real.cos theta,r*Real.sin theta)=
      Real.exp (-r^2)*harmonicFunction (Real.cos theta,Real.sin theta)) ∧
    (∀ theta s, 0 < radon gaussian theta s) := by
  exact ⟨by simp [polynomial_degree_zero], polynomial_harmonic,
    gaussian_degree_zero_mode, radon_positive⟩

theorem radon_not_zero : ¬ (∀ theta s, radon gaussian theta s=0) := by
  intro h
  exact (ne_of_gt (radon_positive 0 0)) (h 0 0)

#print axioms point_on_line
#print axioms line_speed_one
#print axioms slice_integrable
#print axioms radon_gaussian
#print axioms radon_positive
#print axioms polynomial_degree_zero
#print axioms homogeneous_degree_zero
#print axioms polynomial_harmonic
#print axioms gaussian_degree_zero_mode
#print axioms output_degree_zero
#print axioms even_degree_survives
#print axioms radon_not_zero
end RadonEven
