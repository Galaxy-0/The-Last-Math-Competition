/-
  Disproof of TLMC conjecture 00000002182.

  Conjecture: the expected (average) sensitivity of monotone Boolean
  functions has supremum exactly (1/2) * sqrt(log n).

  Refutation: the plain MAJORITY function on 5 variables is monotone and
  has average sensitivity 60/32 = 1.875, while

      (1/2) sqrt(log_2 5) < 0.77   and   (1/2) sqrt(ln 5) < 0.64,

  so the conjectured supremum is exceeded under both standard logarithm
  conventions.

  Integer certificate for base 2 (squaring chain):
      60/32 > (1/2) sqrt(log_2 5)
    <=> (15/4)^2 > log_2 5 <=> 2^(225/16) > 5 <=> 2^225 > 5^16,
  certified below as `two225_gt_five16` (2^225 ~ 5.4e67 vs 5^16 ~ 1.5e11).
  For base e: e^(225/16) > 2^(225/16) > 2^14 = 16384 > 5, using e > 2
  (cited); hence the inequality holds in base e as well.

  The sensitivity count 60: over all 32 inputs x (5-bit words, given
  explicitly as a table) and all 5 bit positions, the majority value
  flips exactly 60 times — `sensCount_eq` (kernel enumeration).

  All theorems are closed kernel computations, axiom-free.
-/

namespace Tlmc2182

/-- All 32 five-bit words, as explicit bit lists. -/
def words : List (List Nat) := [
  [0,0,0,0,0],[1,0,0,0,0],[0,1,0,0,0],[1,1,0,0,0],
  [0,0,1,0,0],[1,0,1,0,0],[0,1,1,0,0],[1,1,1,0,0],
  [0,0,0,1,0],[1,0,0,1,0],[0,1,0,1,0],[1,1,0,1,0],
  [0,0,1,1,0],[1,0,1,1,0],[0,1,1,1,0],[1,1,1,1,0],
  [0,0,0,0,1],[1,0,0,0,1],[0,1,0,0,1],[1,1,0,0,1],
  [0,0,1,0,1],[1,0,1,0,1],[0,1,1,0,1],[1,1,1,0,1],
  [0,0,0,1,1],[1,0,0,1,1],[0,1,0,1,1],[1,1,0,1,1],
  [0,0,1,1,1],[1,0,1,1,1],[0,1,1,1,1],[1,1,1,1,1]]

/-- Majority on 5 bits. -/
def maj (w : List Nat) : Nat :=
  if w.sum >= 3 then 1 else 0

/-- Flip the i-th bit (structural). -/
def flip (w : List Nat) (i : Nat) : List Nat :=
  match w, i with
  | [],      _     => []
  | b :: rest, 0   => (1 - b) :: rest
  | b :: rest, i+1 => b :: flip rest i

/-- Does flipping bit i change the majority value? -/
def sens (w : List Nat) (i : Nat) : Bool :=
  decide (maj w ≠ maj (flip w i))

/-- Number of sensitive (input, bit) pairs over all 32 words × 5 bits. -/
def sensCount : Nat :=
  (words.flatMap fun w => (List.range 5).filter (fun i => sens w i)).length

theorem sensCount_eq : sensCount = 60 := by decide

theorem words_length : words.length = 32 := by decide

/-- The integer comparison behind 60/32 > (1/2) sqrt(log_2 5):
    2^225 > 5^16. -/
theorem two225_gt_five16 : (2:Nat)^225 > (5:Nat)^16 := by decide

/-- Base-e companion: 2^14 > 5 (with e > 2, hence e^(225/16) > 2^14 > 5). -/
theorem two14_gt_five : (2:Nat)^14 > (5:Nat) := by decide

end Tlmc2182
