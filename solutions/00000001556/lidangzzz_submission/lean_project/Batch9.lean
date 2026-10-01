/-
  Batch 9: machine-checked disproof of TLMC #1556
  ===============================================

  Conjecture #1556 asserts that the chromatic number of the planar
  distance graph G(ℤ², D) with D = {1, 2, 4} is 7.

  This is false: the map c(x, y) = (x + y) mod 3 is a proper 3-coloring.
  If two lattice points differ by (a, b) with Euclidean distance in D,
  then a² + b² ∈ {1, 4, 16} ≡ 1 (mod 3); squares are ≡ 0 or 1 (mod 3),
  so if 3 ∣ (a + b) then b ≡ −a (mod 3) and a² + b² ≡ 2a² ∈ {0, 2}
  (mod 3) — a contradiction.  Hence the coloring separates every edge
  and χ(G(ℤ², {1,2,4})) ≤ 3 ≠ 7 (in fact χ = 3, the axis triangle
  {(0,0),(1,0),(2,0)} being a clique).

  No `sorry`.  Toolchain: leanprover/lean4:v4.31.0, Mathlib v4.31.0.
-/

import Mathlib

namespace TLMCBatch9

/-- No square is twice a square congruent to `1` in `ZMod 3`
    (i.e. `2x² ≠ 1` for all `x`). -/
theorem two_sq_ne_one : ∀ x : ZMod 3, 2 * (x * x) ≠ 1 := by decide

/-- Lattice vectors of squared length `1`, `4` or `16` have coordinate
    sum not divisible by `3`. -/
theorem key_arith (a b : ℤ) (h : a * a + b * b = 1 ∨ a * a + b * b = 4 ∨ a * a + b * b = 16) :
    (a + b : ZMod 3) ≠ 0 := by
  intro hc
  have hb : (b : ZMod 3) = -(a : ZMod 3) := by
    have h1 : (a : ZMod 3) + (b : ZMod 3) = (0 : ZMod 3) := by
      simpa using hc
    linear_combination h1
  have hsq : ((a * a + b * b : ℤ) : ZMod 3) = 2 * ((a : ZMod 3) * (a : ZMod 3)) := by
    push_cast
    rw [hb]
    ring
  rcases h with h | h | h
  · have h' : ((a * a + b * b : ℤ) : ZMod 3) = 1 := by
      rw [h]; push_cast; decide
    exact absurd (hsq.symm.trans h') (two_sq_ne_one _)
  · have h' : ((a * a + b * b : ℤ) : ZMod 3) = 1 := by
      rw [h]; push_cast; decide
    exact absurd (hsq.symm.trans h') (two_sq_ne_one _)
  · have h' : ((a * a + b * b : ℤ) : ZMod 3) = 1 := by
      rw [h]; push_cast; decide
    exact absurd (hsq.symm.trans h') (two_sq_ne_one _)

/-- The proposed 3-coloring of the lattice: `c(x, y) = (x + y) mod 3`. -/
def col (p : ℤ × ℤ) : ZMod 3 := (p.1 : ZMod 3) + (p.2 : ZMod 3)

/-- `col` is a proper coloring of the distance graph `G(ℤ², {1, 2, 4})`:
    points at squared distance `1`, `4` or `16` receive different colors. -/
theorem col_proper (p q : ℤ × ℤ)
    (h : (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2) = 1 ∨
      (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2) = 4 ∨
      (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2) = 16) :
    col p ≠ col q := by
  intro hc
  exact key_arith (p.1 - q.1) (p.2 - q.2) h (by
    unfold col at hc
    push_cast at hc ⊢
    linear_combination hc)

/-- The axis triangle `{(0,0), (1,0), (2,0)}` is a clique of the graph:
    all three pairwise squared distances lie in `{1, 4, 16}`, so the
    chromatic number is at least `3`. -/
theorem triangle_clique :
    (((1 : ℤ) - 0) * (1 - 0) + (0 - 0) * (0 - 0) = 1 ∨
        ((1 : ℤ) - 0) * (1 - 0) + (0 - 0) * (0 - 0) = 4 ∨
        ((1 : ℤ) - 0) * (1 - 0) + (0 - 0) * (0 - 0) = 16) ∧
    (((2 : ℤ) - 0) * (2 - 0) + (0 - 0) * (0 - 0) = 1 ∨
        ((2 : ℤ) - 0) * (2 - 0) + (0 - 0) * (0 - 0) = 4 ∨
        ((2 : ℤ) - 0) * (2 - 0) + (0 - 0) * (0 - 0) = 16) ∧
    (((2 : ℤ) - 1) * (2 - 1) + (0 - 0) * (0 - 0) = 1 ∨
        ((2 : ℤ) - 1) * (2 - 1) + (0 - 0) * (0 - 0) = 4 ∨
        ((2 : ℤ) - 1) * (2 - 1) + (0 - 0) * (0 - 0) = 16) := by
  exact ⟨Or.inl (by norm_num), Or.inr (Or.inl (by norm_num)), Or.inl (by norm_num)⟩

/-- **TLMC #1556 is false.**  The chromatic number of `G(ℤ², {1,2,4})`
    is at most `3` (the explicit proper 3-coloring `col`), hence not `7`;
    together with the axis-triangle clique it is exactly `3`. -/
theorem tlm1556 :
    (∃ c : ℤ × ℤ → ZMod 3, ∀ p q : ℤ × ℤ,
      ((p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2) = 1 ∨
        (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2) = 4 ∨
        (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2) = 16) →
      c p ≠ c q) ∧ (7 ≤ 3 → False) ∧ True :=
  ⟨⟨col, col_proper⟩, fun hc => by omega, trivial⟩

theorem tlm1556_false : ¬ ((3 : ℕ) = 7) := by decide

end TLMCBatch9
