/-!
# Disproof of TLMC conjecture 00000000477

**Conjecture (00000000477).** For promotion on the set `LE(P)` of linear
extensions of a poset `P`, the lcm of the promotion orbit lengths divides
`#LE(P)`.

**Counterexample.** The Ferrers poset of the Young diagram of shape `(3, 2)`.
Its linear extensions are exactly the standard Young tableaux of shape `(3, 2)`
and there are 5 of them.  Schutzenberger promotion (jeu de taquin) permutes
these 5 tableaux in two orbits, of lengths 3 and 2.  `Nat.lcm 3 2 = 6`, and
6 does not divide 5.

Everything below is pure core Lean 4: only `decide`/`rfl` on explicit data.
There is no `sorry` and, as `Check.lean` audits, no axiom is used
(no `propext`, no `Quot.sound`, no `Classical.choice`).

## Encoding

A tableau of shape `(3, 2)` is the row-major tuple `(a, b, c, d, e)`:

```
        row 0:  a  b  c
        row 1:  d  e
```

so `a` is cell `(0,0)`, `b` is `(0,1)`, `c` is `(0,2)`, `d` is `(1,0)`,
`e` is `(1,1)`.  A linear extension of the Ferrers poset corresponds to the
tableau whose entry in a cell is the position of that cell in the extension,
so enumerating standard tableaux is enumerating linear extensions.
-/

/-- A tableau of shape `(3,2)` as the row-major tuple `(a, b, c, d, e)`:
row 0 is `a b c`, row 1 is `d e`. -/
abbrev Tab := Nat × Nat × Nat × Nat × Nat

/-- Standard-tableau condition for shape `(3,2)`: rows and columns of the
Ferrers diagram strictly increase. -/
def IsStd : Tab → Prop
  | (a, b, c, d, e) => a < b ∧ b < c ∧ d < e ∧ a < d ∧ b < e

/-- Boolean mirror of `IsStd` plus full injectivity of the entries, used for
brute-force enumeration over all tuples with entries in `{1,2,3,4,5}`. -/
def isStdB : Tab → Bool
  | (a, b, c, d, e) =>
    (a < b) && (b < c) && (d < e) && (a < d) && (b < e)
      && (a != b) && (a != c) && (a != d) && (a != e)
      && (b != c) && (b != d) && (b != e)
      && (c != d) && (c != e) && (d != e)

/-- Schutzenberger promotion on tableaux of shape `(3,2)` with 5 cells:
remove the corner entry, jeu-de-taquin slide the hole to an outer corner,
write `6` into the hole, then decrease every entry by 1.

For this shape the hole makes at most two slides, so the algorithm is a fully
explicit case split.  Step 1: hole at `(0,0)`; slide up the smaller of the
right neighbour `b` and the lower neighbour `d`.
* If `b` moved, the hole is at `(0,1)` and the only remaining neighbours are
  `c` (right) and `e` (lower): slide the smaller.
* If `d` moved, the hole is at `(1,0)` and the only remaining neighbour is
  `e` (right): slide it.

The outer corners are `(0,2)` and `(1,1)`; the hole always ends at one of
them.  Nat subtraction is safe on actual tableaux (every slid entry is >= 2).
The removed corner entry is discarded, hence the wildcard `_a`. -/
def pr : Tab → Tab
  | (_a, b, c, d, e) =>
    if b ≤ d then
      if c ≤ e then (b - 1, c - 1, 5, d - 1, e - 1)
      else          (b - 1, e - 1, c - 1, d - 1, 5)
    else
      (d - 1, b - 1, c - 1, e - 1, 5)

/-- Iterate a function `n` times (core Lean 4 has no `Function.iterate`;
the `f^[n]` notation belongs to Mathlib). -/
def iter : (Tab → Tab) → Nat → Tab → Tab
  | _, 0, t => t
  | f, n + 1, t => f (iter f n t)

/-- The five standard tableaux of shape `(3,2)`. -/
def t1 : Tab := (1, 2, 3, 4, 5)
def t2 : Tab := (1, 2, 4, 3, 5)
def t3 : Tab := (1, 2, 5, 3, 4)
def t4 : Tab := (1, 3, 4, 2, 5)
def t5 : Tab := (1, 3, 5, 2, 4)

theorem std1 : IsStd t1 := ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩⟩
theorem std2 : IsStd t2 := ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩⟩
theorem std3 : IsStd t3 := ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩⟩
theorem std4 : IsStd t4 := ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩⟩
theorem std5 : IsStd t5 := ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩⟩

/-- The digit pool for enumeration. -/
def digits : List Nat := [1, 2, 3, 4, 5]

/-- All tuples with entries in `{1,2,3,4,5}`: `5^5 = 3125` candidates.
Every standard tableau of shape `(3,2)` occurs because its entries are
exactly `{1,...,5}` and the coordinates are read row-major. -/
def allTuples : List Tab :=
  digits.flatMap fun a =>
    digits.flatMap fun b =>
      digits.flatMap fun c =>
        digits.flatMap fun d => digits.map fun e => (a, b, c, d, e)

/-- Brute-force enumeration of the standard tableaux of shape `(3,2)`. -/
def syts : List Tab := allTuples.filter isStdB

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- Exhaustive check: the standard tableaux of shape `(3,2)` are exactly
`t1, t2, t3, t4, t5` (in enumeration order). -/
theorem syts_eq : syts = [t1, t2, t3, t4, t5] := by decide

/-- `#LE` of the Ferrers poset of shape `(3,2)` equals `5`. -/
theorem card_LE : syts.length = 5 := by rw [syts_eq]; rfl

/-- Promotion sends `t1` to `t3`. -/
theorem pr_t1 : pr t1 = t3 := by decide
/-- Promotion sends `t2` to `t5`. -/
theorem pr_t2 : pr t2 = t5 := by decide
/-- Promotion sends `t3` to `t4`. -/
theorem pr_t3 : pr t3 = t4 := by decide
/-- Promotion sends `t4` back to `t1`: orbit `{t1, t3, t4}` closes. -/
theorem pr_t4 : pr t4 = t1 := by decide
/-- Promotion sends `t5` back to `t2`: orbit `{t2, t5}` closes. -/
theorem pr_t5 : pr t5 = t2 := by decide

/-- Orbit of `t1` has exactly length 3: `{t1 → t3 → t4 → t1}`. -/
theorem orbit_A :
    iter pr 3 t1 = t1 ∧ pr t1 ≠ t1 ∧ iter pr 2 t1 ≠ t1 := by decide

/-- Orbit of `t2` has exactly length 2: `{t2 → t5 → t2}`. -/
theorem orbit_B :
    iter pr 2 t2 = t2 ∧ pr t2 ≠ t2 := by decide

/-- The lcm of the two orbit lengths `3` and `2` is `6`. -/
theorem lcm_eq : Nat.lcm 3 2 = 6 := by decide

/-- `6` does not divide `5`. -/
theorem not_divides : ¬ (5 % 6 = 0) := by decide

set_option maxHeartbeats 1000000 in
/-- **The attack, concretised.**  The Ferrers poset of shape `(3,2)` satisfies:

* `#LE = 5` (`card_LE`, via `syts_eq`);
* promotion splits its 5 linear extensions into two orbits, of lengths
  3 (`orbit_A`) and 2 (`orbit_B`), covering all 5 elements
  (`syts_eq` + `pr_t1..pr_t5`);
* `lcm(3,2) = 6` and `6 ∤ 5` (`lcm_eq`, `not_divides`).

Hence the conjecture "the lcm of promotion orbit lengths divides `#LE(P)`"
is **false**. -/
theorem counterexample_00000000477 :
    syts.length = 5 ∧
    IsStd t1 ∧ IsStd t2 ∧ IsStd t3 ∧ IsStd t4 ∧ IsStd t5 ∧
    pr t1 = t3 ∧ pr t2 = t5 ∧ pr t3 = t4 ∧ pr t4 = t1 ∧ pr t5 = t2 ∧
    (iter pr 3 t1 = t1 ∧ pr t1 ≠ t1 ∧ iter pr 2 t1 ≠ t1) ∧
    (iter pr 2 t2 = t2 ∧ pr t2 ≠ t2) ∧
    Nat.lcm 3 2 = 6 ∧ ¬ (5 % 6 = 0) :=
  ⟨card_LE, std1, std2, std3, std4, std5,
   pr_t1, pr_t2, pr_t3, pr_t4, pr_t5,
   orbit_A, orbit_B, lcm_eq, not_divides⟩
