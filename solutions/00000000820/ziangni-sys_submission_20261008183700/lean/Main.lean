import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace TorusZero
abbrev Torus := Real.Angle × Real.Angle
noncomputable def eigenfunction (p : Torus) : ℝ := p.1.sin * p.2.sin
noncomputable def lift (x y : ℝ) : ℝ := eigenfunction ((x : Real.Angle), (y : Real.Angle))
@[simp] theorem lift_formula (x y : ℝ) : lift x y = Real.sin x * Real.sin y := rfl

theorem smooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => lift p.1 p.2) := by
  simp only [lift_formula]
  exact contDiff_fst.sin.mul contDiff_snd.sin

theorem continuous_on_torus : Continuous eigenfunction := by
  unfold eigenfunction
  exact (Real.Angle.continuous_sin.comp continuous_fst).mul
    (Real.Angle.continuous_sin.comp continuous_snd)

noncomputable def dx (x y : ℝ) : ℝ := deriv (fun t => lift t y) x
noncomputable def dy (x y : ℝ) : ℝ := deriv (fun t => lift x t) y
@[simp] theorem dx_formula (x y : ℝ) : dx x y = Real.cos x * Real.sin y := by
  exact ((Real.hasDerivAt_sin x).mul_const (Real.sin y)).deriv
@[simp] theorem dy_formula (x y : ℝ) : dy x y = Real.sin x * Real.cos y := by
  exact ((Real.hasDerivAt_sin y).const_mul (Real.sin x)).deriv
noncomputable def dxx (x y : ℝ) : ℝ := deriv (fun t => dx t y) x
noncomputable def dyy (x y : ℝ) : ℝ := deriv (fun t => dy x t) y
noncomputable def dxy (x y : ℝ) : ℝ := deriv (fun t => dx x t) y
noncomputable def dyx (x y : ℝ) : ℝ := deriv (fun t => dy t y) x
@[simp] theorem dxx_formula (x y : ℝ) : dxx x y = -Real.sin x * Real.sin y := by
  unfold dxx
  simp only [dx_formula]
  exact ((Real.hasDerivAt_cos x).mul_const (Real.sin y)).deriv
@[simp] theorem dyy_formula (x y : ℝ) : dyy x y = Real.sin x * -Real.sin y := by
  unfold dyy
  simp only [dy_formula]
  exact ((Real.hasDerivAt_cos y).const_mul (Real.sin x)).deriv
@[simp] theorem dxy_formula (x y : ℝ) : dxy x y = Real.cos x * Real.cos y := by
  unfold dxy
  simp only [dx_formula]
  exact ((Real.hasDerivAt_sin y).const_mul (Real.cos x)).deriv
@[simp] theorem dyx_formula (x y : ℝ) : dyx x y = Real.cos x * Real.cos y := by
  unfold dyx
  simp only [dy_formula]
  exact ((Real.hasDerivAt_sin x).mul_const (Real.cos y)).deriv

theorem laplacian_eigenvalue (x y : ℝ) : -(dxx x y + dyy x y) = 2 * lift x y := by
  simp only [dxx_formula, dyy_formula, lift_formula]
  ring

theorem zero_first_jet : lift 0 0 = 0 ∧ dx 0 0 = 0 ∧ dy 0 0 = 0 := by simp

-- The actual Taylor polynomial through degree two, built from the actual partial derivatives.
noncomputable def taylorTwo (u v : ℝ) : ℝ := lift 0 0 + dx 0 0*u + dy 0 0*v +
  (dxx 0 0*u^2 + (dxy 0 0+dyx 0 0)*u*v + dyy 0 0*v^2)/2

theorem quadratic_leading_part (u v : ℝ) : taylorTwo u v = u*v := by
  simp [taylorTwo]
  ring

theorem nonzero_second_jet : dxy 0 0 = 1 ∧ taylorTwo 1 1 ≠ 0 := by
  simp [quadratic_leading_part]

theorem index_outside_exception : Nat.gcd 1 1 ≠ 2 ∧ 1^2+1^2=2 ∧
    ¬ ∃ n : ℕ, n*(n+1)=2*2 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · rintro ⟨n,hn⟩
    have hle : n ≤ 2 := by nlinarith
    interval_cases n <;> norm_num at hn

-- A zero of order at most one must have a nonzero first derivative in some coordinate.
def SimpleZero (x y : ℝ) : Prop := lift x y = 0 ∧ (dx x y ≠ 0 ∨ dy x y ≠ 0)

theorem conjecture_false : ¬ SimpleZero 0 0 := by
  simp [SimpleZero]

#print axioms smooth
#print axioms continuous_on_torus
#print axioms laplacian_eigenvalue
#print axioms zero_first_jet
#print axioms quadratic_leading_part
#print axioms nonzero_second_jet
#print axioms index_outside_exception
#print axioms conjecture_false
end TorusZero
