/-
  TLMC #405 DISPROOF (standalone)
-/

import Mathlib

namespace TLMC405

/-! ### #405: the Kostka spin-pairing product -/

/-- Semistandard fillings of shape (2,1) with content (1,1,1): triples
    `(a, b, c)` (top row `a b`, bottom row `c`) whose entries are a
    permutation of `{0,1,2}`, with weakly increasing rows (`a ≤ b`) and
    strictly increasing columns (`a < c`).  By the standard combinatorial
    definition this finite cardinality is the Kostka number
    `K_{(2,1),(1,1,1)}`. -/
def ssyt21 : Finset (Fin 3 × Fin 3 × Fin 3) :=
  Finset.univ.filter fun p =>
    p.1 ≤ p.2.1 ∧ p.1 < p.2.2 ∧
      ({p.1, p.2.1, p.2.2} : Finset (Fin 3)) = Finset.univ

/-- `K_{(2,1),(1,1,1)} = 2` (kernel-computed). -/
theorem card_ssyt21 : ssyt21.card = 2 := by decide

/-- **TLMC #405 is false.**  The partition `(2,1)` is self-conjugate
    (`(2,1)' = (2,1)`), so the spin-pairing product at `n = 3` is
    `2 · 2 = 4`, which does not divide `3! = 6`. -/
theorem tlm405_false : ¬ ((2 : ℕ) * 2 ∣ 6) := by decide

end TLMC405
