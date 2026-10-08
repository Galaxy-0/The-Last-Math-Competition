import Mathlib.Tactic

namespace Conjecture1255

-- A binary cellular automaton on the one-site periodic ring.
def deterministicUpdate (s : Bool) : Bool := !s

theorem no_fixed_points : ¬ ∃ s, deterministicUpdate s = s := by decide

-- With probability 3/4 apply the flip, with probability 1/4 keep the bit.
noncomputable def transition (s t : Bool) : ℝ := if s = t then 1 / 4 else 3 / 4

theorem transition_positive (s t : Bool) : 0 < transition s t := by
  unfold transition
  split <;> norm_num

theorem transition_stochastic (s : Bool) :
    transition s false + transition s true = 1 := by
  cases s <;> norm_num [transition]

def Distribution (p : Bool → ℝ) : Prop :=
  0 ≤ p false ∧ 0 ≤ p true ∧ p false + p true = 1

def Stationary (p : Bool → ℝ) : Prop :=
  Distribution p ∧ ∀ t, p t = p false * transition false t + p true * transition true t

noncomputable def uniform : Bool → ℝ := fun _ => 1 / 2

theorem uniform_stationary : Stationary uniform := by
  constructor
  · norm_num [Distribution, uniform]
  · intro t
    cases t <;> norm_num [uniform, transition]

theorem stationary_unique {p : Bool → ℝ} (hp : Stationary p) : p = uniform := by
  have hsum := hp.1.2.2
  have hfalse := hp.2 false
  norm_num [transition] at hfalse
  funext t
  cases t <;> dsimp [uniform] <;> linarith

-- Standard extreme-point criterion in the convex set of stationary laws.
def ExtremeStationary (p : Bool → ℝ) : Prop :=
  Stationary p ∧ ∀ (a b : Bool → ℝ) (r : ℝ),
    Stationary a → Stationary b → 0 < r → r < 1 →
    (∀ t, p t = r * a t + (1 - r) * b t) → a = p ∧ b = p

theorem uniform_extreme : ExtremeStationary uniform := by
  refine ⟨uniform_stationary, ?_⟩
  intro a b r ha hb _ _ _
  exact ⟨stationary_unique ha, stationary_unique hb⟩

def dirac (s : Bool) : Bool → ℝ := fun t => if t = s then 1 else 0

theorem uniform_not_dirac (s : Bool) : uniform ≠ dirac s := by
  intro h
  have hs := congrFun h s
  norm_num [uniform, dirac] at hs

def ExtremePointsAreFixed : Prop :=
  ∀ p, ExtremeStationary p → ∃ s, deterministicUpdate s = s ∧ p = dirac s

theorem conjecture_false : ¬ ExtremePointsAreFixed := by
  intro h
  obtain ⟨s, hs, _⟩ := h uniform uniform_extreme
  exact no_fixed_points ⟨s, hs⟩

end Conjecture1255
