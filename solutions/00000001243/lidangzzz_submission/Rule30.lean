/-
  Batch 4: machine-checked disproof of TLMC #1243
  ==============================================

  Conjecture #1243 claims of the central column of Wolfram's rule 30
  (started from a single live cell) that

    "among its factors of length < 2^k none contains a square:
     the central column is square-free over all prefixes of length 2^k".

  In the standard sense of combinatorics on words, a *square* is a word of
  the form u ++ u with u nonempty.  The central column begins

    1, 1, 0, 1, 1, 1, 0, 0, 1, ...

  so the prefix of length 2^2 = 4 is [1, 1, 0, 1], which contains the
  factor [1, 1] = [1] ++ [1], a square.  Hence the conjecture, as stated,
  is false.  (The computation below is by `decide`, i.e. kernel-verified
  evaluation of the defining recursion of rule 30.)

  No `sorry`.  Toolchain: leanprover/lean4:v4.31.0, Mathlib v4.31.0.
-/

import Mathlib

namespace TLMCBatch4

/-- Rule 30 started from a single live cell at the origin: rows are
    functions `ℤ → Bool` and `new p = old (p-1) XOR (old p OR old (p+1))`. -/
def zrow : ℕ → (ℤ → Bool)
  | 0 => fun p => p == 0
  | t + 1 => fun p => (zrow t (p - 1)) ^^ ((zrow t p) || (zrow t (p + 1)))

/-- The central column of rule 30. -/
def zcol (t : ℕ) : Bool := zrow t 0

/-- The prefix of the first `n` values of the central column. -/
def colPrefix (n : ℕ) : List Bool := (List.range n).map zcol

/-- A word contains a *square* if some nonempty word `u` has `u ++ u`
    as an infix (the standard definition from combinatorics on words). -/
def HasSquare (l : List Bool) : Prop :=
  ∃ u : List Bool, u ≠ [] ∧ (u ++ u).IsInfix l

/-- The first eight values of the central column (kernel-computed). -/
theorem colPrefix_8 :
    colPrefix 8 = [true, true, false, true, true, true, false, false] := by
  decide

/-- In particular the first four values are `1, 1, 0, 1`. -/
theorem colPrefix_4 : colPrefix 4 = [true, true, false, true] := by
  decide

/-- The prefix of length `2^2 = 4` contains the square `11 = 1 ++ 1`;
    the square has length `2 < 2^2`, so the "factors of length < 2^k"
    clause fails at `k = 2` as well. -/
theorem prefix4_has_square : HasSquare (colPrefix 4) ∧
    ([true] ++ [true]).length < 2 ^ 2 := by
  refine ⟨⟨[true], by simp, ?_⟩, by decide⟩
  show ([true] ++ [true]).IsInfix (colPrefix 4)
  rw [colPrefix_4]
  decide

/-- **TLMC #1243 is false.**  The central column is *not* square-free over
    the prefixes of length `2^k`: for `k = 2` the prefix `1101` contains
    the square `11`. -/
theorem tlm1243_false : ¬ ∀ k : ℕ, 1 ≤ k → ¬ HasSquare (colPrefix (2 ^ k)) := by
  intro h
  exact h 2 (by norm_num) prefix4_has_square.1

end TLMCBatch4
