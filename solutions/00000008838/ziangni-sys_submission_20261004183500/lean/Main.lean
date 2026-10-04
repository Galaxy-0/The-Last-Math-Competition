import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

noncomputable section
namespace ADMMCounterexample
open Filter
open scoped Topology
abbrev E := EuclideanSpace ℝ (Fin 2)
def vec (x y : ℝ) : E := !₂[x,y]
def A : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight (vec 1 0)
def B : ℝ →L[ℝ] E := A
def c : E := vec 0 1
def f (x : ℝ) : ℝ := x^2/2

theorem coupling_apply (x : ℝ) : A x=vec x 0 ∧ B x=vec x 0 := by
  constructor <;> ext i <;> fin_cases i <;> simp [A,B,vec]

theorem nonzero_couplings : A≠0 ∧ B≠0 := by
  constructor <;> intro h
  · have hh := congrArg (fun L : ℝ →L[ℝ] E => L 1 0) h
    norm_num [A,vec] at hh
  · have hh := congrArg (fun L : ℝ →L[ℝ] E => L 1 0) h
    norm_num [B,A,vec] at hh

theorem infeasible : ¬∃ x y : ℝ, A x+B y=c := by
  rintro ⟨x,y,h⟩
  have hh := congrArg (fun z : E => z 1) h
  rw [(coupling_apply x).1,(coupling_apply y).2] at hh
  norm_num [c,vec] at hh

theorem actual_gradient (x : ℝ) : gradient f x=x := by
  convert (((hasDerivAt_id x).pow 2).div_const 2).hasGradientAt'.gradient using 1 <;> norm_num [f]

theorem strong_quadratic_identity (x y : ℝ) :
    f y=f x+gradient f x*(y-x)+‖y-x‖^2/2 := by
  rw [actual_gradient]
  simp [f,Real.norm_eq_abs,sq_abs]
  ring

theorem f_convex : ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  have hid : a*f x+b*f y-f (a*x+b*y)=a*b*(x-y)^2/2 := by
    have hb' : b=1-a := by linarith
    rw [hb']; unfold f; ring
  have hp : 0≤a*b*(x-y)^2/2 := by positivity
  change f (a*x+b*y)≤a*f x+b*f y
  linarith

theorem f_closed : IsClosed {p : ℝ×ℝ | f p.1≤p.2} :=
  isClosed_le ((continuous_fst.pow 2).div_const 2) continuous_snd

def augmented (x y : ℝ) (u : E) : ℝ :=
  f x+f y+‖A x+B y-c+u‖^2/2-‖u‖^2/2

theorem augmented_formula (x y : ℝ) (u : E) :
    augmented x y u = x^2/2+y^2/2+(x+y+u 0)^2/2+(u 1-1)^2/2-
      ((u 0)^2+(u 1)^2)/2 := by
  rw [augmented,(coupling_apply x).1,(coupling_apply y).2,
    PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  simp [f,vec,c,Fin.sum_univ_two,Real.norm_eq_abs,sq_abs]
  ring

def xUpdate (y : ℝ) (u : E) : ℝ := -(y+u 0)/2
def yUpdate (x : ℝ) (u : E) : ℝ := -(x+u 0)/2

theorem x_gap (y z : ℝ) (u : E) :
    augmented z y u-augmented (xUpdate y u) y u=(z-xUpdate y u)^2 := by
  rw [augmented_formula,augmented_formula]
  unfold xUpdate
  ring

theorem y_gap (x z : ℝ) (u : E) :
    augmented x z u-augmented x (yUpdate x u) u=(z-yUpdate x u)^2 := by
  rw [augmented_formula,augmented_formula]
  unfold yUpdate
  ring

def Minimizes (h : ℝ → ℝ) (x : ℝ) : Prop := ∀ z, h x≤h z

theorem unique_x_subproblem (y : ℝ) (u : E) :
    ∃! x, Minimizes (fun z => augmented z y u) x := by
  refine ⟨xUpdate y u,?_,?_⟩
  · intro z
    have h := x_gap y z u
    nlinarith [sq_nonneg (z-xUpdate y u)]
  · intro z hz
    have h := hz (xUpdate y u)
    have he := x_gap y z u
    nlinarith [sq_nonneg (z-xUpdate y u)]

theorem unique_y_subproblem (x : ℝ) (u : E) :
    ∃! y, Minimizes (fun z => augmented x z u) y := by
  refine ⟨yUpdate x u,?_,?_⟩
  · intro z
    have h := y_gap x z u
    nlinarith [sq_nonneg (z-yUpdate x u)]
  · intro z hz
    have h := hz (yUpdate x u)
    have he := y_gap x z u
    nlinarith [sq_nonneg (z-yUpdate x u)]

@[ext] structure State where
  x : ℝ
  y : ℝ
  u : E

def step (s : State) : State :=
  let x := xUpdate s.y s.u
  let y := yUpdate x s.u
  ⟨x,y,s.u+A x+B y-c⟩

def sample (n : ℕ) : State := ⟨0,0,vec 0 (-(n:ℝ))⟩
def trajectory (n : ℕ) : State := step^[n] (sample 0)

theorem sample_step (n : ℕ) : step (sample n)=sample (n+1) := by
  apply State.ext
  · simp [step,sample,xUpdate,vec]
  · simp [step,sample,xUpdate,yUpdate,vec]
  · ext i
    fin_cases i <;> simp [step,sample,xUpdate,yUpdate,A,B,c,vec] <;> push_cast <;> ring

theorem actual_iterates (n : ℕ) : trajectory n=sample n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [trajectory,Function.iterate_succ_apply']
    change step (trajectory n)=sample (n+1)
    rw [ih,sample_step]

theorem actual_residual (n : ℕ) :
    A (trajectory n).x+B (trajectory n).y-c=vec 0 (-1) := by
  rw [actual_iterates]
  ext i
  fin_cases i <;> simp [sample,A,B,c,vec]

def dualPath (n : ℕ) : E := (trajectory n).u

theorem coordinate_not_convergent (a : ℝ) :
    ¬Tendsto (fun n : ℕ => -(n:ℝ)) atTop (𝓝 a) := by
  intro h
  have hs := h.comp (tendsto_add_atTop_nat 1)
  have hd : Tendsto (fun _ : ℕ => (-1:ℝ)) atTop (𝓝 0) := by
    convert hs.sub h using 1 <;> norm_num

  have he : (-1:ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds hd
  norm_num at he

def secondCoordinate : E →L[ℝ] ℝ := PiLp.proj (p:=2) (β:=fun _ : Fin 2 => ℝ) (𝕜:=ℝ) 1

theorem dual_not_convergent (v : E) : ¬Tendsto dualPath atTop (𝓝 v) := by
  intro h
  have hh := (secondCoordinate.continuous.tendsto v).comp h
  apply coordinate_not_convergent (v 1)
  simpa [dualPath,actual_iterates,sample,vec,secondCoordinate,Function.comp_def] using hh

def WeakLimit (v : E) : Prop := ∀ L : E →L[ℝ] ℝ,
  Tendsto (fun n => L (dualPath n)) atTop (𝓝 (L v))

theorem dual_not_weak (v : E) : ¬WeakLimit v := by
  intro h
  apply coordinate_not_convergent (v 1)
  simpa [dualPath,actual_iterates,sample,vec,secondCoordinate] using h secondCoordinate
end ADMMCounterexample
end
#print axioms ADMMCounterexample.infeasible
#print axioms ADMMCounterexample.augmented_formula
#print axioms ADMMCounterexample.unique_x_subproblem
#print axioms ADMMCounterexample.unique_y_subproblem
#print axioms ADMMCounterexample.actual_iterates
#print axioms ADMMCounterexample.dual_not_convergent
#print axioms ADMMCounterexample.dual_not_weak
