import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace SubgradientCounterexample

-- On the real line every linear dual functional is multiplication by v.
def Subgradient (f : ℝ → ℝ) (x v : ℝ) : Prop :=
  ∀ y : ℝ, f x + v * (y-x) ≤ f y

def subdifferential (f : ℝ → ℝ) (x : ℝ) : Set ℝ := {v | Subgradient f x v}

def epigraph (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p | f p.1 ≤ p.2}

def ClosedConvex (f : ℝ → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧ IsClosed (epigraph f)

def constant (c : ℝ) : ℝ → ℝ := fun _ => c

theorem constant_closed_convex (c : ℝ) : ClosedConvex (constant c) := by
  constructor
  · exact convexOn_const c convex_univ
  · change IsClosed {p : ℝ × ℝ | c ≤ p.2}
    exact isClosed_le continuous_const continuous_snd

theorem constant_subgradient (c x v : ℝ) :
    Subgradient (constant c) x v ↔ v = 0 := by
  constructor
  · intro h
    have hp := h (x+1)
    have hm := h (x-1)
    dsimp [constant] at hp hm
    nlinarith
  · rintro rfl
    intro y
    simp [constant]

theorem constant_subdifferential (c x : ℝ) :
    subdifferential (constant c) x = {0} := by
  ext v
  exact constant_subgradient c x v

-- General source of the nonuniqueness, using the actual global inequality.
theorem additive_constant_invariance (f : ℝ → ℝ) (c x : ℝ) :
    subdifferential (fun y => f y+c) x = subdifferential f x := by
  ext v
  constructor
  · intro h y
    have hh := h y
    dsimp at hh
    linarith
  · intro h y
    have hh := h y
    dsimp
    linarith

def zeroFunction : ℝ → ℝ := constant 0
def oneFunction : ℝ → ℝ := constant 1

theorem closed_convex_witnesses : ClosedConvex zeroFunction ∧ ClosedConvex oneFunction :=
  ⟨constant_closed_convex 0,constant_closed_convex 1⟩

theorem identical_subdifferentials :
    ∀ x : ℝ, subdifferential zeroFunction x = subdifferential oneFunction x := by
  intro x
  exact (constant_subdifferential 0 x).trans (constant_subdifferential 1 x).symm

theorem functions_distinct : zeroFunction ≠ oneFunction := by
  intro h
  have he := congrFun h 0
  norm_num [zeroFunction,oneFunction,constant] at he

def UniqueDetermination : Prop := ∀ f g : ℝ → ℝ,
  ClosedConvex f → ClosedConvex g →
  (∀ x, subdifferential f x = subdifferential g x) → f = g

theorem conjecture_00000008843_false : ¬ UniqueDetermination := by
  intro h
  exact functions_distinct (h zeroFunction oneFunction closed_convex_witnesses.1
    closed_convex_witnesses.2 identical_subdifferentials)

#print axioms constant_closed_convex
#print axioms constant_subgradient
#print axioms additive_constant_invariance
#print axioms conjecture_00000008843_false
end SubgradientCounterexample
