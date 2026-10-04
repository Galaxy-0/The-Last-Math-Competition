import Mathlib

/-!
# Conjecture 00000003631

The conjecture claims that the maximal number of invariant lines of a quadratic
system is four. We formalize the standard polynomial invariance criterion for
lines and give a homogeneous quadratic vector field with five distinct invariant
lines.
-/

namespace Submission00000003631

/-- Coefficients of a homogeneous quadratic planar vector field. -/
structure QuadraticSystem where
  pXX : ℝ
  pXY : ℝ
  pYY : ℝ
  qXX : ℝ
  qXY : ℝ
  qYY : ℝ

/-- The first component of the quadratic vector field. -/
def QuadraticSystem.p (s : QuadraticSystem) (x y : ℝ) : ℝ :=
  s.pXX * x * x + s.pXY * x * y + s.pYY * y * y

/-- The second component of the quadratic vector field. -/
def QuadraticSystem.q (s : QuadraticSystem) (x y : ℝ) : ℝ :=
  s.qXX * x * x + s.qXY * x * y + s.qYY * y * y

/-- The coefficient data are nonzero, so the homogeneous system has degree two. -/
def QuadraticSystem.IsExactQuadratic (s : QuadraticSystem) : Prop :=
  s.pXX ≠ 0 ∨ s.pXY ≠ 0 ∨ s.pYY ≠ 0 ∨
  s.qXX ≠ 0 ∨ s.qXY ≠ 0 ∨ s.qYY ≠ 0

/-- A line through the origin, represented by the nonzero linear form `a*x+b*y`. -/
structure Line where
  a : ℝ
  b : ℝ
  nonzero : a ≠ 0 ∨ b ≠ 0

/-- Two coefficient pairs represent distinct geometric lines iff they are not
proportional, expressed by their nonzero determinant. -/
def Line.distinct (l₁ l₂ : Line) : Prop :=
  l₁.a * l₂.b - l₁.b * l₂.a ≠ 0

/-- The polynomial vector field leaves the line invariant when its derivative
on the defining linear form is divisible by that form. For a quadratic field,
the cofactor is a linear form `u*x+v*y`. -/
def IsInvariantLine (s : QuadraticSystem) (l : Line) : Prop :=
  ∃ u v : ℝ, ∀ x y : ℝ,
    l.a * s.p x y + l.b * s.q x y =
      (l.a * x + l.b * y) * (u * x + v * y)

/-- Having at most four invariant lines means that no five pairwise distinct
lines are all invariant. -/
def HasAtMostFourInvariantLines (s : QuadraticSystem) : Prop :=
  ∀ ls : Fin 5 → Line,
    (∀ i j, i ≠ j → (ls i).distinct (ls j)) →
    (∀ i, IsInvariantLine s (ls i)) → False

/-- The numerical upper-bound assertion from the conjecture. -/
def ConjecturedBound : Prop :=
  ∀ s : QuadraticSystem, s.IsExactQuadratic → HasAtMostFourInvariantLines s

/-- The exact homogeneous quadratic field P=x^2, Q=xy. -/
def starSystem : QuadraticSystem :=
  ⟨1, 0, 0, 0, 1, 0⟩

theorem starSystem_exact : starSystem.IsExactQuadratic := by
  simp [QuadraticSystem.IsExactQuadratic, starSystem]

/-- Five lines through the origin: x=0, y=0, x+y=0, x+2y=0, x-y=0. -/
def fiveLines : Fin 5 → Line := fun i =>
  match i.val with
  | 0 => ⟨1, 0, Or.inl (by norm_num)⟩
  | 1 => ⟨0, 1, Or.inr (by norm_num)⟩
  | 2 => ⟨1, 1, Or.inl (by norm_num)⟩
  | 3 => ⟨1, 2, Or.inl (by norm_num)⟩
  | _ => ⟨1, -1, Or.inl (by norm_num)⟩

theorem fiveLines_pairwise_distinct :
    ∀ i j, i ≠ j → (fiveLines i).distinct (fiveLines j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [fiveLines, Line.distinct] at *

theorem fiveLines_are_invariant :
    ∀ i, IsInvariantLine starSystem (fiveLines i) := by
  intro i
  refine ⟨1, 0, ?_⟩
  intro x y
  fin_cases i <;> norm_num [IsInvariantLine, fiveLines, starSystem,
    QuadraticSystem.p, QuadraticSystem.q] <;> ring

theorem conjecture_00000003631_false : ¬ ConjecturedBound := by
  intro h
  have hfour := h starSystem starSystem_exact
  exact hfour fiveLines fiveLines_pairwise_distinct fiveLines_are_invariant

#print axioms conjecture_00000003631_false

end Submission00000003631
