/-!
# Disproof of TLMC conjecture 00000001211

Conjecture (verbatim from `conjectures/00000001211.md`): *Definition: a poset game (delete an
element and everything above it). Conjecture: the P-positions of the poset game on Young's
lattice have an explicit characterization via perfect square partitions (the Young poset game).*

A Young diagram is encoded as a `List Nat` of non-increasing row lengths.  A move chomps a cell
`(i, j)` (1-indexed row, 1-indexed column): the cell together with every cell above-right of it
is removed, and the result is put back into canonical form (trailing zero rows dropped).

Two readings of the conjecture are both refuted:

* **Literal reading** (`winLit`: normal play, every cell may be chomped, including `(1, 1)`).
  Chomping `(1, 1)` clears the whole diagram, so *every* nonempty position is an N-position
  and the only P-position is the empty diagram (`isPLit_nil`, `isPLit_cons`).  Hence the
  perfect square `[2, 2]` is **not** a P-position (`literal_counterexample`).

* **Chomp reading** (`winChomp`: poison corner — chomping `(1, 1)` is not a legal move; the
  player forced to take the poison loses, which has exactly the same game values as forbidding
  the move).  Here `[2, 1]` is a P-position that is not a square, while the squares
  `[2, 2]`, `[3, 3]`, `[3, 3, 3]` are N-positions (`chomp_counterexample`): the
  characterization fails in both directions.

Both oracles `winLit` / `winChomp` take an explicit fuel; `isNLit` / `isNChomp` use fuel
`total + 1`.  This is sufficient: every move enumerated by `anyCell` is a genuine cell
(column `j` of a row of length `n` has `1 ≤ j ≤ n`), so row `i` shrinks from `len` to
`min len (j - 1) ≤ len - 1`, i.e. every move removes at least one cell and the game depth
from a diagram with `t` cells is at most `t`.

No `sorry`, and the axiom audit in `Check.lean` shows every theorem below depends on **no
axioms at all** (not even `propext`).
-/

/-- Total number of cells of a diagram. -/
def total : List Nat → Nat
  | [] => 0
  | n :: rest => n + total rest

/-- Column offsets `0, 1, …, k-1` in decreasing order; shifted by `+1` these enumerate the
columns `1 … k` of a row of length `k`. -/
def cols : Nat → List Nat
  | 0 => []
  | k + 1 => k :: cols k

/-- Does some cell `(i, j)` of the diagram satisfy `f i j`?  `r` is the absolute 1-indexed row
of the first row of the given list. -/
def anyCell : List Nat → Nat → (Nat → Nat → Bool) → Bool
  | [], _, _ => false
  | n :: rest, r, f => (cols n).any (fun c => f r (c + 1)) || anyCell rest (r + 1) f

/-- Rows before the countdown `k` expires are kept unchanged; from that row onward a row of
length `len` keeps only its first `min len (j - 1)` cells (columns `≥ j` are removed).

If a chomped row becomes empty we return `[]` at once.  For a chomp at a *genuine* cell of a
*canonical* partition this is exactly canonicalisation: the trigger can only be `j = 1` (the
chomped row had `len ≥ j ≥ 1`, and lower rows of a partition are non-increasing, so they all
chomp to `min len (j - 1) = 0` as well), so no trailing zero rows can survive.  The recursive
call sits in a direct position, keeping the definition free of `propext`. -/
def chompFrom : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | len :: rest, 0, j =>
    if min len (j - 1) = 0 then [] else min len (j - 1) :: chompFrom rest 0 j
  | len :: rest, k + 1, j => len :: chompFrom rest k j

/-- Chomp the cell `(i, j)`: remove it and everything above-right of it. -/
def chompAt (lam : List Nat) (i j : Nat) : List Nat := chompFrom lam (i - 1) j

theorem min_nat_zero : ∀ n : Nat, min n 0 = 0
  | 0 => rfl
  | _ + 1 => rfl

/-- Chomping the top-left corner `(1, 1)` always clears the whole diagram. -/
theorem chompAt_11 : ∀ lam : List Nat, chompAt lam 1 1 = [] := by
  intro lam
  induction lam with
  | nil => rfl
  | cons n rest =>
    show chompFrom (n :: rest) 0 1 = []
    show (if min n 0 = 0 then [] else min n 0 :: chompFrom rest 0 1) = []
    rw [min_nat_zero n]
    rfl

/-! ## Reading 1: literal poset game (all cells, normal play) -/

/-- Worker for `winLit`; the position is matched first, so `winLitGo [] f = false` reduces
for every fuel `f`, and the recursion is structural in the fuel. -/
def winLitGo : List Nat → Nat → Bool
  | [], _ => false
  | _ :: _, 0 => false
  | n :: rest, f + 1 =>
    anyCell (n :: rest) 1 (fun i j => !winLitGo (chompAt (n :: rest) i j) f)

/-- Normal-play win oracle for the literal reading: `winLit fuel lam = true` iff the player to
move wins.  The fuel must exceed the game depth (see the module docstring). -/
def winLit (fuel : Nat) (lam : List Nat) : Bool := winLitGo lam fuel

/-- N-position of the literal reading. -/
def isNLit (lam : List Nat) : Bool := winLit (total lam + 1) lam

/-- P-position of the literal reading. -/
def isPLit (lam : List Nat) : Bool := !isNLit lam

theorem cols_any (g : Nat → Bool) : ∀ n : Nat, 1 ≤ n → g 0 = true → (cols n).any g = true := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.not_succ_le_zero 0)
  | succ m ih =>
    intro _ hg
    cases m with
    | zero =>
      show (g 0 || (cols 0).any g) = true
      rw [hg]
      rfl
    | succ k =>
      show (g (k + 1) || (cols (k + 1)).any g) = true
      rw [ih (Nat.succ_le_succ (Nat.zero_le k)) hg]
      exact Bool.or_true _

/-- Under the literal reading every nonempty diagram is an N-position, because the cell `(1, 1)`
is always present and chomping it clears the board. -/
theorem isNLit_cons : ∀ (n : Nat) (rest : List Nat), 1 ≤ n → isNLit (n :: rest) = true := by
  intro n rest hn
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero 0)
  | succ m =>
    have hrow : Eq
        ((cols (m + 1)).any
          (fun c =>
            Bool.not (winLit (total ((m + 1) :: rest)) (chompAt ((m + 1) :: rest) 1 (c + 1)))))
        true := by
      apply cols_any
      · exact Nat.succ_le_succ (Nat.zero_le m)
      · show Bool.not (winLit (total ((m + 1) :: rest)) (chompAt ((m + 1) :: rest) 1 1)) = true
        rw [chompAt_11]
        cases hT : total ((m + 1) :: rest) with
        | zero => rfl
        | succ k => rfl
    show winLit (total ((m + 1) :: rest) + 1) ((m + 1) :: rest) = true
    have heq : Eq
        (winLit (total ((m + 1) :: rest) + 1) ((m + 1) :: rest))
        (Bool.or
          ((cols (m + 1)).any
            (fun c =>
              Bool.not (winLit (total ((m + 1) :: rest)) (chompAt ((m + 1) :: rest) 1 (c + 1)))))
          (anyCell rest 2
            (fun i j =>
              Bool.not (winLit (total ((m + 1) :: rest)) (chompAt ((m + 1) :: rest) i j))))) := rfl
    rw [heq, hrow]
    rfl

/-- The empty diagram is a P-position (no moves at all). -/
theorem isPLit_nil : isPLit [] = true := rfl

/-- Under the literal reading no nonempty diagram is a P-position.  Together with
`isPLit_nil` this pins the P-positions down to exactly `{[]}`. -/
theorem isPLit_cons : ∀ (n : Nat) (rest : List Nat), 1 ≤ n → isPLit (n :: rest) = false := by
  intro n rest hn
  show Bool.not (isNLit (n :: rest)) = false
  rw [isNLit_cons n rest hn]
  rfl

/-! ## Perfect squares -/

/-- A perfect-square partition: nonempty, and every row has length equal to the number of
rows (a `k × k` square). -/
def isSquare (lam : List Nat) : Bool := !lam.isEmpty && lam.all (fun r => r == lam.length)

theorem square_22 : isSquare [2, 2] = true := rfl

theorem square_333 : isSquare [3, 3, 3] = true := rfl

theorem not_square_21 : isSquare [2, 1] = false := rfl

/-! ## Reading 2: Chomp with a poison corner -/

/-- Worker for `winChomp` (see `winLitGo` for the shape): the corner `(1, 1)` may not be
chomped.  Taking the poison loses immediately, so a rational player never does it voluntarily;
forbidding the move yields identical game values.  Facing the lone poison cell `[1]` there is
no winning move, so `[1]` is a P-position, exactly as in Chomp. -/
def winChompGo : List Nat → Nat → Bool
  | [], _ => false
  | _ :: _, 0 => false
  | n :: rest, f + 1 =>
    anyCell (n :: rest) 1 (fun i j =>
      if i == 1 && j == 1 then false else !winChompGo (chompAt (n :: rest) i j) f)

/-- Win oracle for the Chomp reading. -/
def winChomp (fuel : Nat) (lam : List Nat) : Bool := winChompGo lam fuel

/-- N-position of the Chomp reading. -/
def isNChomp (lam : List Nat) : Bool := winChomp (total lam + 1) lam

/-- P-position of the Chomp reading. -/
def isPChomp (lam : List Nat) : Bool := !isNChomp lam

theorem P_chomp_21 : isPChomp [2, 1] = true := by decide

theorem P_chomp_1 : isPChomp [1] = true := by decide

theorem N_chomp_2 : isNChomp [2] = true := by decide

theorem N_chomp_11 : isNChomp [1, 1] = true := by decide

theorem N_chomp_22 : isNChomp [2, 2] = true := by decide

theorem N_chomp_33 : isNChomp [3, 3] = true := by decide

theorem N_chomp_333 : isNChomp [3, 3, 3] = true := by decide

/-! ## The two refutations -/

/-- **The literal reading is refuted.**  `[2, 2]` is a perfect-square partition, but it is an
N-position; in fact the P-positions of the literal game are exactly `{∅}`, so the
perfect-square characterization is false. -/
theorem literal_counterexample :
    isSquare [2, 2] = true ∧ isNLit [2, 2] = true ∧ isPLit [2, 2] = false :=
  ⟨rfl, isNLit_cons 2 [2] (Nat.le_succ 1),
    by show Bool.not (isNLit [2, 2]) = false
       rw [isNLit_cons 2 [2] (Nat.le_succ 1)]
       rfl⟩

/-- **The Chomp reading is refuted.**  `[2, 1]` is a P-position that is not a square, and the
perfect squares `[2, 2]` and `[3, 3, 3]` are N-positions: the characterization fails in both
directions. -/
theorem chomp_counterexample :
    (isPChomp [2, 1] = true ∧ isSquare [2, 1] = false)
      ∧ (isSquare [2, 2] = true ∧ isPChomp [2, 2] = false)
      ∧ (isSquare [3, 3, 3] = true ∧ isNChomp [3, 3, 3] = true) :=
  ⟨⟨P_chomp_21, rfl⟩,
   ⟨rfl, by show Bool.not (isNChomp [2, 2]) = false; rw [N_chomp_22]; rfl⟩,
   ⟨rfl, N_chomp_333⟩⟩
