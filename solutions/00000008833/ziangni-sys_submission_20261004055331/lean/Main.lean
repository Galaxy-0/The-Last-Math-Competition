import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
namespace ChambollePock

def energy (x : ℝ) : ℝ := x^2 / 2
def coupling : ℝ →L[ℝ] ℝ := (1 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ
def tau : ℝ := 2
def sigma : ℝ := 2
def theta : ℝ := 1

theorem coupling_apply (x : ℝ) : coupling x = x / 4 := by simp [coupling]; ring
theorem coupling_nonzero : coupling ≠ 0 := by
  intro h
  have := congrArg (fun K : ℝ →L[ℝ] ℝ => K 1) h
  norm_num [coupling] at this
theorem coupling_selfadjoint (x y : ℝ) :
    @inner ℝ ℝ _ (coupling x) y = @inner ℝ ℝ _ x (coupling y) := by
  simp only [coupling_apply, RCLike.inner_apply, conj_trivial]
  ring

theorem energy_continuous : Continuous energy := by unfold energy; fun_prop
theorem energy_convex : ConvexOn ℝ univ energy := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [energy, smul_eq_mul]
  have hs := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x-y))
  nlinarith [sq_nonneg (a*x+b*y), mul_self_nonneg (a+b-1)]

-- Exact Fenchel supremum: a universal bound with an attaining argument.
theorem conjugate_upper (y x : ℝ) : y*x - energy x ≤ energy y := by
  unfold energy
  nlinarith [sq_nonneg (x-y)]
theorem conjugate_attained (y : ℝ) : y*y - energy y = energy y := by unfold energy; ring
theorem fenchel_conjugate (y : ℝ) : sSup (range (fun x : ℝ => y*x - energy x)) = energy y := by
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro _ ⟨x, rfl⟩
    exact conjugate_upper y x
  · rw [← conjugate_attained y]
    apply le_csSup
    · exact ⟨energy y, by rintro _ ⟨x, rfl⟩; exact conjugate_upper y x⟩
    · exact mem_range_self y

def proxObjective (a x : ℝ) : ℝ := energy x + (x-a)^2 / (2*tau)
def Prox (a x : ℝ) : Prop := ∀ z, proxObjective a x ≤ proxObjective a z
def prox (a : ℝ) : ℝ := a / 3

theorem prox_exact (a x : ℝ) : Prox a x ↔ x = prox a := by
  constructor
  · intro h
    have hx := h (prox a)
    unfold proxObjective energy tau prox at hx
    unfold prox
    nlinarith [sq_nonneg (x-a/3)]
  · rintro rfl z
    unfold proxObjective energy tau prox
    nlinarith [sq_nonneg (z-a/3)]

def saddle (x y : ℝ) : ℝ := energy x + coupling x * y - energy y
theorem zero_saddle (x y : ℝ) : saddle 0 y ≤ saddle 0 0 ∧ saddle 0 0 ≤ saddle x 0 := by
  simp only [saddle, coupling_apply, energy]
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

abbrev State := ℝ × ℝ × ℝ
def step (s : State) : State :=
  let yn := prox (s.2.1 + sigma * coupling s.2.2)
  let xn := prox (s.1 - tau * coupling yn)
  (xn, yn, xn + theta * (xn-s.1))
def orbit (s : State) (n : ℕ) : State := step^[n] s
def size (s : State) : ℝ := max |s.1| (max |s.2.1| |s.2.2|)

theorem step_formula (x y z : ℝ) :
    step (x,y,z) = ((x-(y+z/2)/3/2)/3, (y+z/2)/3,
      2*((x-(y+z/2)/3/2)/3)-x) := by
  simp only [step, prox, sigma, tau, theta, coupling_apply]
  congr 1 <;> ring

theorem one_step (s : State) (M : ℝ) (hM : 0 ≤ M)
    (hx : |s.1| ≤ M) (hy : |s.2.1| ≤ M) (hz : |s.2.2| ≤ M) :
    |(step s).1| ≤ M/2 ∧ |(step s).2.1| ≤ M/2 ∧ |(step s).2.2| ≤ M/2 := by
  rcases s with ⟨x,y,z⟩
  rw [step_formula]
  simp only [Prod.fst, Prod.snd] at hx hy hz ⊢
  rcases abs_le.mp hx with ⟨hxl,hxu⟩
  rcases abs_le.mp hy with ⟨hyl,hyu⟩
  rcases abs_le.mp hz with ⟨hzl,hzu⟩
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith

theorem size_nonneg (s : State) : 0 ≤ size s := le_trans (abs_nonneg _) (le_max_left _ _)
theorem coordinates_le (s : State) : |s.1| ≤ size s ∧ |s.2.1| ≤ size s ∧ |s.2.2| ≤ size s :=
  ⟨le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
    le_trans (le_max_right _ _) (le_max_right _ _)⟩
theorem size_contracts (s : State) : size (step s) ≤ size s / 2 := by
  obtain ⟨hx,hy,hz⟩ := coordinates_le s
  obtain ⟨hx',hy',hz'⟩ := one_step s (size s) (size_nonneg s) hx hy hz
  exact max_le hx' (max_le hy' hz')

theorem orbit_bound (s : State) (n : ℕ) : size (orbit s n) ≤ (1/2 : ℝ)^n * size s := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    have hr : orbit s (n+1) = step (orbit s n) := by simp [orbit, Function.iterate_succ_apply']
    rw [hr]
    calc
      size (step (orbit s n)) ≤ size (orbit s n)/2 := size_contracts _
      _ ≤ ((1/2 : ℝ)^n * size s)/2 := by linarith
      _ = (1/2 : ℝ)^(n+1)*size s := by rw [pow_succ]; ring

theorem orbit_converges (s : State) : Tendsto (orbit s) atTop (𝓝 (0,0,0)) := by
  have hp : Tendsto (fun n : ℕ => (1/2 : ℝ)^n * size s) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).mul_const (size s)
  have hc (f : State → ℝ) (hf : ∀ t, |f t| ≤ size t) :
      Tendsto (fun n => f (orbit s n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm
    · intro n
      exact le_trans (hf _) (orbit_bound s n)
    · exact hp
  exact (hc Prod.fst (fun t => (coordinates_le t).1)).prodMk_nhds
    ((hc (fun t => t.2.1) (fun t => (coordinates_le t).2.1)).prodMk_nhds
      (hc (fun t => t.2.2) (fun t => (coordinates_le t).2.2)))

theorem product_bound_counterexample :
    0 < tau ∧ 0 < sigma ∧ 1 < tau*sigma ∧ coupling ≠ 0 ∧
    (∀ s : State, Tendsto (orbit s) atTop (𝓝 (0,0,0))) := by
  exact ⟨by norm_num [tau], by norm_num [sigma], by norm_num [tau,sigma],
    coupling_nonzero, orbit_converges⟩

#print axioms energy_convex
#print axioms fenchel_conjugate
#print axioms prox_exact
#print axioms zero_saddle
#print axioms orbit_bound
#print axioms product_bound_counterexample
end ChambollePock
