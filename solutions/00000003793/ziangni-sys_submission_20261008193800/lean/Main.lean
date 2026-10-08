import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

open Filter
open scoped Topology
namespace ProjectedQuartic
noncomputable def f (x : ℝ) : ℝ := x^2/2+x^4/4
noncomputable def gradient (x : ℝ) : ℝ := x+x^3

theorem derivative (x : ℝ) : HasDerivAt f (gradient x) x := by
  convert (((hasDerivAt_id x).pow 2).div_const 2).add (((hasDerivAt_id x).pow 4).div_const 4) using 1 <;>
    simp [f,gradient] <;> ring

theorem strong_curvature (x y : ℝ) : f x+gradient x*(y-x)+(y-x)^2/2 ≤ f y := by
  have hr : f y-(f x+gradient x*(y-x)+(y-x)^2/2) =
      (y-x)^2*((x+y)^2+2*x^2)/4 := by unfold f gradient; ring
  have hp : 0 ≤ (y-x)^2*((x+y)^2+2*x^2)/4 := by positivity
  linarith

-- Full 1-strong-convex Jensen inequality, not an assumed curvature certificate.
theorem strong_jensen (x y a b : ℝ) (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    f (a*x+b*y)+a*b/2*(x-y)^2 ≤ a*f x+b*f y := by
  let z := a*x+b*y
  have h1 := mul_le_mul_of_nonneg_left (strong_curvature z x) ha
  have h2 := mul_le_mul_of_nonneg_left (strong_curvature z y) hb
  have h := add_le_add h1 h2
  have hi : a*(f z+gradient z*(x-z)+(x-z)^2/2)+
      b*(f z+gradient z*(y-z)+(y-z)^2/2) = f z+a*b/2*(x-y)^2 := by
    have hb' : b=1-a := by linarith
    dsimp [z]; rw [hb']; unfold f gradient; ring
  rw [hi] at h
  exact h

theorem unique_minimizer : f 0=0 ∧ (∀ x, f 0≤f x) ∧ (∀ x, f x=f 0 ↔ x=0) := by
  constructor
  · norm_num [f]
  constructor
  · intro x; simp [f]; positivity
  · intro x; constructor
    · intro h; have hp := sq_nonneg x; have h4 := pow_nonneg (sq_nonneg x) 2
      simp [f] at h
      nlinarith [sq_nonneg (x^2)]
    · rintro rfl; rfl

noncomputable def projection (x : ℝ) : ℝ := x
-- This is the genuine unique nearest-point metric projection onto the closed convex full line.
theorem projection_nearest (x : ℝ) : projection x ∈ (Set.univ : Set ℝ) ∧
    (∀ y ∈ (Set.univ : Set ℝ), dist x (projection x) ≤ dist x y) ∧
    (∀ y : ℝ, dist x y = dist x (projection x) ↔ y=projection x) := by
  simp [projection, dist_eq_zero, eq_comm]
  intro y; exact dist_nonneg
noncomputable def step (α x : ℝ) : ℝ := projection (x-α*gradient x)
noncomputable def orbit (α R : ℝ) (n : ℕ) : ℝ := (step α)^[n] R

-- For every fixed positive step, sufficiently large points increase in magnitude.
theorem step_growth (α R x : ℝ) (hα : 0<α) (hR : 0<R)
    (hscale : 3≤α*R^2) (hx : R≤|x|) : 2*|x| ≤ |step α x| := by
  have hs : R^2≤x^2 := (sq_le_sq).mpr (by simpa [abs_of_pos hR] using hx)
  have hc : 2≤α*x^2+α-1 := by nlinarith
  have hi : step α x = -x*(α*x^2+α-1) := by unfold step projection gradient; ring
  rw [hi,abs_mul,abs_neg,abs_of_nonneg (by linarith : 0≤α*x^2+α-1)]
  nlinarith [abs_nonneg x]

theorem orbit_growth (α R : ℝ) (hα : 0<α) (hR : 0<R) (hs : 3≤α*R^2) (n : ℕ) :
    R≤|orbit α R n| ∧ R+(n:ℝ)*R≤|orbit α R n| ∧ (2:ℝ)^n*R≤|orbit α R n| := by
  induction n with
  | zero => simp [orbit,abs_of_pos hR]
  | succ n ih =>
    have hg := step_growth α R (orbit α R n) hα hR hs ih.1
    have hi : orbit α R (n+1)=step α (orbit α R n) := Function.iterate_succ_apply' (step α) n R
    rw [hi]
    simp only [Nat.cast_add,Nat.cast_one,pow_succ]
    constructor
    · nlinarith
    constructor <;> nlinarith

theorem magnitude_diverges (α R : ℝ) (hα : 0<α) (hR : 0<R) (hs : 3≤α*R^2) :
    Tendsto (fun n => |orbit α R n|) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨N,hN⟩ := exists_nat_gt (B/R)
  have hm : B<(N:ℝ)*R := (div_lt_iff₀ hR).mp hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N:ℝ)≤n := by exact_mod_cast hn
  have hg := (orbit_growth α R hα hR hs n).2.1
  nlinarith

theorem not_convergent_to_minimizer (α R : ℝ) (hα : 0<α) (hR : 0<R) (hs : 3≤α*R^2) :
    ¬Tendsto (orbit α R) atTop (𝓝 0) := by
  intro h
  have hn : Tendsto (fun n => |orbit α R n|) atTop (𝓝 0) := by simpa using h.abs
  have hc : R≤(0:ℝ) := ge_of_tendsto hn (Eventually.of_forall fun n => (orbit_growth α R hα hR hs n).1)
  linarith

theorem every_positive_step_has_divergent_orbit (α : ℝ) (hα : 0<α) :
    ∃ R : ℝ, 0<R ∧ Tendsto (fun n => |orbit α R n|) atTop atTop ∧
      ¬Tendsto (orbit α R) atTop (𝓝 0) := by
  let R := Real.sqrt (3/α)
  have hq : 0<(3:ℝ)/α := div_pos (by norm_num) hα
  have hR : 0<R := Real.sqrt_pos.2 hq
  have hs : R^2=3/α := Real.sq_sqrt hq.le
  have hc : 3≤α*R^2 := by rw [hs]; field_simp
  exact ⟨R,hR,magnitude_diverges α R hα hR hc,not_convergent_to_minimizer α R hα hR hc⟩

#print axioms derivative
#print axioms strong_curvature
#print axioms strong_jensen
#print axioms unique_minimizer
#print axioms projection_nearest
#print axioms step_growth
#print axioms orbit_growth
#print axioms magnitude_diverges
#print axioms not_convergent_to_minimizer
#print axioms every_positive_step_has_divergent_orbit
end ProjectedQuartic
