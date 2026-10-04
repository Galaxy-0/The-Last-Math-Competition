import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

noncomputable section
namespace ActiveSetCounterexample
open Filter
open scoped Topology

def C : Set ℝ := Set.Ici 0
def f (x : ℝ) : ℝ := x^2/2
def constraint (_ : Fin 1) (x : ℝ) : ℝ := -x
def active (x : ℝ) : Set (Fin 1) := {i | constraint i x=0}

theorem actual_feasibility (x : ℝ) : x∈C ↔ ∀ i : Fin 1, constraint i x≤0 := by
  simp [C, constraint]

theorem C_closed_convex : IsClosed C ∧ Convex ℝ C := ⟨isClosed_Ici, convex_Ici 0⟩

theorem actual_gradient (x : ℝ) : gradient f x=x := by
  convert (((hasDerivAt_id x).pow 2).div_const 2).hasGradientAt'.gradient using 1 <;> norm_num [f]

theorem gradient_lipschitz : LipschitzWith 1 (gradient f) := by
  intro x y
  simp [actual_gradient]

theorem strong_quadratic_identity (x y : ℝ) :
    f y = f x + gradient f x*(y-x) + ‖y-x‖^2/2 := by
  rw [actual_gradient]
  simp [f, Real.norm_eq_abs, sq_abs]
  ring

theorem f_convex : ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hid : a*f x+b*f y-f (a*x+b*y) = a*b*(x-y)^2/2 := by
    have hb' : b=1-a := by linarith
    rw [hb']
    unfold f
    ring
  have hp : 0 ≤ a*b*(x-y)^2/2 := by positivity
  change f (a*x+b*y) ≤ a*f x+b*f y
  linarith

theorem f_closed_epigraph : IsClosed {p : ℝ×ℝ | f p.1≤p.2} := by
  exact isClosed_le ((continuous_fst.pow 2).div_const 2) continuous_snd

theorem unique_minimum (x : ℝ) : (x∈C ∧ ∀ y∈C, f x≤f y) ↔ x=0 := by
  constructor
  · rintro ⟨hx, h⟩
    have hh := h 0 (by simp [C])
    simp [f] at hh
    nlinarith [sq_nonneg x]
  · rintro rfl
    refine ⟨by simp [C], ?_⟩
    intro y hy
    unfold f
    nlinarith [sq_nonneg y]

def projection (y : ℝ) : ℝ := max 0 y
def Nearest (y p : ℝ) : Prop := p∈C ∧ ∀ z∈C, dist y p≤dist y z

theorem genuine_projection (y : ℝ) : Nearest y (projection y) := by
  refine ⟨by simp [C, projection], ?_⟩
  intro z hz
  change 0≤z at hz
  by_cases hy : 0≤y
  · simpa [projection, max_eq_right hy] using (dist_nonneg : 0 ≤ dist y z)
  · rw [projection, max_eq_left (le_of_not_ge hy)]
    apply nonneg_le_nonneg_of_sq_le_sq (dist_nonneg)
    rw [← pow_two, ← pow_two]
    simp only [Real.dist_eq, sq_abs]
    nlinarith [sq_nonneg z, mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hy) hz]

def step (x : ℝ) : ℝ := projection (x-(1/2:ℝ)*gradient f x)

theorem safe_step : (0:ℝ)<1/2 ∧ (1/2:ℝ)<2/1 := by norm_num

theorem step_feasible_formula (x : ℝ) (hx : 0≤x) : step x=x/2 := by
  rw [step, actual_gradient]
  have he : x-(1/2:ℝ)*x=x/2 := by ring
  rw [he, projection, max_eq_right (by positivity)]

def trajectory (n : ℕ) : ℝ := step^[n] 1

theorem actual_iterates (n : ℕ) : trajectory n=(1/2:ℝ)^n := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    rw [trajectory, Function.iterate_succ_apply']
    change step (trajectory n)=(1/2:ℝ)^(n+1)
    rw [ih, step_feasible_formula _ (le_of_lt (pow_pos (by norm_num) n)), pow_succ]
    ring

theorem all_iterates_positive (n : ℕ) : 0<trajectory n := by
  rw [actual_iterates]
  positivity

theorem converges_to_solution : Tendsto trajectory atTop (𝓝 0) := by
  simp only [show trajectory=(fun n : ℕ => (1/2:ℝ)^n) from funext actual_iterates]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem active_at_solution : active 0=Set.univ := by ext i; simp [active, constraint]

theorem active_at_iterate (n : ℕ) : active (trajectory n)=∅ := by
  ext i
  have h := all_iterates_positive n
  simp [active, constraint, ne_of_gt h]

theorem never_identified (n : ℕ) : active (trajectory n)≠active 0 := by
  rw [active_at_iterate, active_at_solution]
  exact Set.empty_ne_univ

theorem no_finite_identification : ¬∃ N : ℕ, ∀ n≥N, active (trajectory n)=active 0 := by
  rintro ⟨N, hN⟩
  exact never_identified N (hN N le_rfl)
end ActiveSetCounterexample
end
#print axioms ActiveSetCounterexample.f_convex
#print axioms ActiveSetCounterexample.actual_gradient
#print axioms ActiveSetCounterexample.unique_minimum
#print axioms ActiveSetCounterexample.genuine_projection
#print axioms ActiveSetCounterexample.actual_iterates
#print axioms ActiveSetCounterexample.no_finite_identification
