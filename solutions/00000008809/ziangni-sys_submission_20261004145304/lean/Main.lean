import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic

open Filter
open scoped Topology
noncomputable section
namespace ADMMCounterexample

def f (x : ℝ) : ℝ := -x
def g (_ : ℝ) : ℝ := 0
def epigraph (φ : ℝ → ℝ) : Set (ℝ × ℝ) := {p | φ p.1 ≤ p.2}
/-- Standard properness of the finite-valued function lifted to the extended reals. -/
def ProperLift (φ : ℝ → ℝ) : Prop :=
  (∀ x, (φ x : EReal) ≠ ⊥) ∧ ∃ x, (φ x : EReal) ≠ ⊤
def ClosedProperConvex (φ : ℝ → ℝ) : Prop :=
  ConvexOn ℝ Set.univ φ ∧ IsClosed (epigraph φ) ∧ ProperLift φ
lemma f_closed_proper_convex : ClosedProperConvex f := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · exact convex_univ
    · intro x _ y _ a b _ _ _
      simp [f, smul_eq_mul]
  · exact isClosed_le continuous_fst.neg continuous_snd
  · constructor
    · intro x; simp
    · exact ⟨0, by simp⟩
lemma g_closed_proper_convex : ClosedProperConvex g := by
  refine ⟨convexOn_const 0 convex_univ, ?_, ?_⟩
  · exact isClosed_le continuous_const continuous_snd
  · constructor
    · intro x; simp
    · exact ⟨0, by simp⟩

def A : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
def B : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ
def residual (x z : ℝ) : ℝ := A x + B z
def augmented (x z u : ℝ) : ℝ := f x + g z + u * residual x z + (residual x z)^2/2
lemma residual_formula (x z : ℝ) : residual x z = x-z := by simp [residual, A, B, sub_eq_add_neg]
lemma feasible : residual 0 0 = 0 := by rw [residual_formula]; norm_num
def Solution (x z : ℝ) : Prop := residual x z = 0 ∧
  ∀ y w, residual y w = 0 → f x + g z ≤ f y + g w
lemma no_solution (x z : ℝ) : ¬ Solution x z := by
  rintro ⟨_, h⟩
  have hh := h (x+1) (x+1) (by simp [residual_formula])
  dsimp [f, g] at hh
  linarith

def UniqueMin (φ : ℝ → ℝ) (a : ℝ) : Prop :=
  (∀ y, φ a ≤ φ y) ∧ ∀ y, φ y ≤ φ a → y = a
lemma x_difference (z u y : ℝ) :
    augmented y z u - augmented (z-u+1) z u = (y-(z-u+1))^2/2 := by
  simp only [augmented, f, g, residual_formula]; ring
lemma z_difference (x u y : ℝ) :
    augmented x y u - augmented x (x+u) u = (y-(x+u))^2/2 := by
  simp only [augmented, f, g, residual_formula]; ring
lemma unique_x (z u : ℝ) : UniqueMin (fun y => augmented y z u) (z-u+1) := by
  constructor
  · intro y; have hd := x_difference z u y; nlinarith [sq_nonneg (y-(z-u+1))]
  · intro y hy
    have hd := x_difference z u y
    have hs : (y-(z-u+1))^2 = 0 := by nlinarith [sq_nonneg (y-(z-u+1))]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
lemma unique_z (x u : ℝ) : UniqueMin (fun y => augmented x y u) (x+u) := by
  constructor
  · intro y; have hd := z_difference x u y; nlinarith [sq_nonneg (y-(x+u))]
  · intro y hy
    have hd := z_difference x u y
    have hs : (y-(x+u))^2 = 0 := by nlinarith [sq_nonneg (y-(x+u))]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
structure State where
  x : ℝ
  z : ℝ
  u : ℝ
def step (s : State) : State :=
  let x := s.z-s.u+1
  let z := x+s.u
  ⟨x, z, s.u+residual x z⟩
lemma genuine_admm (s : State) :
    UniqueMin (fun y => augmented y s.z s.u) (step s).x ∧
    UniqueMin (fun y => augmented (step s).x y s.u) (step s).z ∧
    (step s).u = s.u + residual (step s).x (step s).z :=
  ⟨unique_x s.z s.u, unique_z (s.z-s.u+1) s.u, rfl⟩
def initial : State := ⟨0,0,0⟩
def trajectory (n : ℕ) : State := step^[n] initial
lemma iterate_formula (n : ℕ) : trajectory n = ⟨(n:ℝ), (n:ℝ), 0⟩ := by
  induction n with
  | zero => simp [trajectory, initial]
  | succ n ih =>
    have hs : trajectory (n+1) = step (trajectory n) := by
      exact Function.iterate_succ_apply' step n initial
    rw [hs, ih]
    simp [step, residual_formula, Nat.cast_add]
lemma zero_residual (n : ℕ) : residual (trajectory n).x (trajectory n).z = 0 := by
  rw [iterate_formula, residual_formula]; simp

def WeaklyConverges (v : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ L : ℝ →L[ℝ] ℝ, Tendsto (fun n => L (v n)) atTop (𝓝 (L a))
lemma no_weak_limit (a : ℝ) : ¬ WeaklyConverges (fun n => (trajectory n).x) a := by
  intro h
  have hi : Tendsto (fun n => (trajectory n).x) atTop (𝓝 a) := by
    simpa using h (ContinuousLinearMap.id ℝ ℝ)
  have hs := hi.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 (0:ℝ)) := by
    have he : (fun n => (trajectory (n+1)).x - (trajectory n).x) = fun _ => (1:ℝ) := by
      funext n; rw [iterate_formula, iterate_formula]; simp
    simpa [Function.comp_def, he] using hs.sub hi
  have he : (1:ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hdiff
  norm_num at he

theorem counterexample : ClosedProperConvex f ∧ ClosedProperConvex g ∧
    (∃ x z, residual x z = 0) ∧
    (∀ s, UniqueMin (fun y => augmented y s.z s.u) (step s).x ∧
      UniqueMin (fun y => augmented (step s).x y s.u) (step s).z ∧
      (step s).u = s.u + residual (step s).x (step s).z) ∧
    (∀ n, trajectory n = ⟨(n:ℝ),(n:ℝ),0⟩) ∧
    (∀ a, ¬ WeaklyConverges (fun n => (trajectory n).x) a) :=
  ⟨f_closed_proper_convex, g_closed_proper_convex, ⟨0,0,feasible⟩,
    genuine_admm, iterate_formula, no_weak_limit⟩
#print axioms f_closed_proper_convex
#print axioms g_closed_proper_convex
#print axioms no_solution
#print axioms genuine_admm
#print axioms iterate_formula
#print axioms no_weak_limit
#print axioms counterexample
end ADMMCounterexample
