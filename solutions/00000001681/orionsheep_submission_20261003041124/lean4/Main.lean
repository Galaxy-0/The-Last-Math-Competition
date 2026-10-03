/-
  Disproof of TLMC conjecture 00000001681.

  Conjecture: "The number of rainbow C4's in rainbow-triangle-free
  colorings of K_n is at least (1/24)*n^2; the extremal configuration
  is attained by recursive constructions from balanced 4-partite
  colorings, and the constant 1/24 is optimal."

  Refutation: the class of rainbow-triangle-free colorings CONTAINS
  every 2-coloring (a triangle whose three edges use at most two
  colors is never rainbow, by the pigeonhole principle).  In a
  2-coloring no C4 is rainbow either (its four cycle edges use at most
  two colors; a rainbow C4 needs four pairwise-distinct edge colors).
  Hence the rainbow-C4 count is identically 0 on this whole subfamily,
  while (1/24)*n^2 > 0 for every n >= 1: the claimed universal lower
  bound fails for every member with n >= 1.

  Kernel-certified below: the 3- and 4-edge pigeonholes for 2 colors;
  the resulting absence of rainbow triangles and of rainbow C4s in a
  concrete member of the class exhibited for every n (the constant
  2-coloring, with its symmetry); and the arithmetic failure
  24 * 0 < n * n for n >= 1 (i.e. 0 < (1/24)*n^2).  All computations
  are closed in the kernel; the audit reports zero axioms.
-/

namespace Tlmc1681

/-! ## Pigeonhole for two colors. -/

/-- Any three 2-colored edges contain two of the same color (8 cases). -/
theorem pigeon3 : ∀ f1 f2 f3 : Bool,
    f1 = f2 ∨ f1 = f3 ∨ f2 = f3 := by
  decide

/-- Any four 2-colored edges contain two of the same color (16 cases). -/
theorem pigeon4 : ∀ f1 f2 f3 f4 : Bool,
    f1 = f2 ∨ f1 = f3 ∨ f1 = f4 ∨ f2 = f3 ∨ f2 = f4 ∨ f3 = f4 := by
  decide

/-- Hence no triangle of a 2-coloring is rainbow: a rainbow triangle
    needs its 3 edges pairwise distinctly colored. -/
theorem no_rainbow3 : ∀ f1 f2 f3 : Bool,
    ¬ (f1 ≠ f2 ∧ f1 ≠ f3 ∧ f2 ≠ f3) := by
  intro f1 f2 f3 h
  rcases pigeon3 f1 f2 f3 with h' | h' | h'
  · exact absurd h' h.1
  · exact absurd h' h.2.1
  · exact absurd h' h.2.2

/-- Hence no four 2-colored edges are pairwise distinctly colored:
    a C4 in a 2-coloring is never rainbow. -/
theorem no_rainbow4 : ∀ f1 f2 f3 f4 : Bool,
    ¬ (f1 ≠ f2 ∧ f1 ≠ f3 ∧ f1 ≠ f4 ∧ f2 ≠ f3 ∧ f2 ≠ f4 ∧ f3 ≠ f4) := by
  intro f1 f2 f3 f4 h
  rcases pigeon4 f1 f2 f3 f4 with h' | h' | h' | h' | h' | h'
  · exact absurd h' h.1
  · exact absurd h' h.2.1
  · exact absurd h' h.2.2.1
  · exact absurd h' h.2.2.2.1
  · exact absurd h' h.2.2.2.2.1
  · exact absurd h' h.2.2.2.2.2

/-! ## The concrete member: the constant 2-coloring of K_n. -/

/-- The constant 2-coloring: every edge gets color `false`. -/
def cc (a b : Nat) : Bool := false

theorem cc_symm (a b : Nat) : cc a b = cc b a := rfl

/-- No rainbow triangle in the constant coloring, so it is a member of
    the rainbow-triangle-free class. -/
theorem cc_no_rainbow_triangle (v1 v2 v3 : Nat) :
    ¬ (cc v1 v2 ≠ cc v2 v3 ∧ cc v1 v2 ≠ cc v1 v3 ∧ cc v2 v3 ≠ cc v1 v3) :=
  no_rainbow3 (cc v1 v2) (cc v2 v3) (cc v1 v3)

/-- No rainbow C4 (four distinct vertices, cycle edges v1v2, v2v3,
    v3v4, v4v1) in the constant coloring. -/
theorem cc_no_rainbow_c4 (v1 v2 v3 v4 : Nat) :
    ¬ (cc v1 v2 ≠ cc v2 v3 ∧ cc v1 v2 ≠ cc v3 v4 ∧ cc v1 v2 ≠ cc v4 v1 ∧
       cc v2 v3 ≠ cc v3 v4 ∧ cc v2 v3 ≠ cc v4 v1 ∧ cc v3 v4 ≠ cc v4 v1) :=
  no_rainbow4 (cc v1 v2) (cc v2 v3) (cc v3 v4) (cc v4 v1)

/-! ## The claimed bound (1/24)*n^2 is positive for every n >= 1. -/

/-- For every n >= 1: n * n > 0, hence (1/24)*n^2 > 0. -/
theorem bound_fails : ∀ n : Nat, 1 ≤ n → (0:Nat) < n * n := by
  intro n hn
  cases n with
  | zero => exact absurd hn (by decide)
  | succ m => exact Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos m)

/-- THE REFUTATION: for every n >= 1 there is a rainbow-triangle-free
    edge coloring (the constant 2-coloring: symmetric, no rainbow
    triangle) in which NO C4 on four distinct vertices is rainbow --
    so its rainbow-C4 count is 0 -- while the claimed bound (1/24)*n^2
    is positive (encoded by clearing denominators as 24 * count < n^2,
    here 24 * 0 < n * n).  The claimed universal lower bound fails for
    this member, for every n >= 1. -/
theorem conjecture_refuted : ∀ n : Nat, 1 ≤ n →
    ∃ col : Nat → Nat → Bool,
      (∀ a b, col a b = col b a) ∧
      (∀ v1 v2 v3, ¬ (col v1 v2 ≠ col v2 v3 ∧ col v1 v2 ≠ col v1 v3 ∧
                      col v2 v3 ≠ col v1 v3)) ∧
      (∀ v1 v2 v3 v4, v1 ≠ v2 → v1 ≠ v3 → v1 ≠ v4 → v2 ≠ v3 → v2 ≠ v4 → v3 ≠ v4 →
        ¬ (col v1 v2 ≠ col v2 v3 ∧ col v1 v2 ≠ col v3 v4 ∧ col v1 v2 ≠ col v4 v1 ∧
           col v2 v3 ≠ col v3 v4 ∧ col v2 v3 ≠ col v4 v1 ∧ col v3 v4 ≠ col v4 v1)) ∧
      ¬ ((24:Nat) * 0 ≥ n * n) := by
  intro n hn
  refine ⟨cc, cc_symm, cc_no_rainbow_triangle,
    fun v1 v2 v3 v4 _ _ _ _ _ _ => cc_no_rainbow_c4 v1 v2 v3 v4, ?_⟩
  intro h
  rw [Nat.mul_zero] at h
  cases n with
  | zero => exact absurd hn (by decide)
  | succ m =>
      have h0 : Nat.succ m * Nat.succ m ≤ 0 := h
      rcases Nat.mul_eq_zero.mp (Nat.le_zero.mp h0) with hz | hz
      · exact Nat.noConfusion hz
      · exact Nat.noConfusion hz

end Tlmc1681
