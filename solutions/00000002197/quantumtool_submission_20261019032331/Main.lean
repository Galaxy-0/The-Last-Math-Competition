import Std

/-!
A finite formalization of the partition lattice on four points.
Partitions are represented by their restricted-growth strings.  The table
contains the 15 such strings, one for each set partition of {0,1,2,3}.
-/

abbrev Point := Fin 4
abbrev Part := Fin 15

private def labels : List (List Nat) :=
  [ [0, 0, 0, 0] -- one block
  , [0, 0, 0, 1] -- 012 | 3
  , [0, 0, 1, 0] -- 013 | 2
  , [0, 0, 1, 1] -- 01 | 23
  , [0, 0, 1, 2] -- 01 | 2 | 3
  , [0, 1, 0, 0] -- 023 | 1
  , [0, 1, 0, 1] -- 02 | 13
  , [0, 1, 0, 2] -- 02 | 1 | 3
  , [0, 1, 1, 0] -- 03 | 12
  , [0, 1, 1, 1] -- 123 | 0
  , [0, 1, 1, 2] -- 12 | 0 | 3
  , [0, 1, 2, 0] -- 03 | 1 | 2
  , [0, 1, 2, 1] -- 13 | 0 | 2
  , [0, 1, 2, 2] -- 23 | 0 | 1
  , [0, 1, 2, 3] -- four singleton blocks
  ]

def blockLabel (p : Part) (x : Point) : Nat :=
  ((labels.getD p.val []).getD x.val 99)

def partRel (p : Part) (x y : Point) : Bool :=
  decide (blockLabel p x = blockLabel p y)

abbrev IsEquivRel (r : Point → Point → Bool) : Prop :=
  (∀ x, r x x = true) ∧
  (∀ x y, r x y = r y x) ∧
  (∀ x y z, r x y = true → r y z = true → r x z = true)

/-- An unordered pair in {0,1,2,3}, indexed as 01,02,03,12,13,23. -/
def edgeIndex (x y : Point) : Nat :=
  let a := min x.val y.val
  let b := max x.val y.val
  if a = 0 then b - 1 else if a = 1 then b + 1 else 5

def edgeBit (a b c d e f : Bool) (i : Nat) : Bool :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c else
  if i = 3 then d else if i = 4 then e else f

def relationFromBits (a b c d e f : Bool) (x y : Point) : Bool :=
  if x = y then true else edgeBit a b c d e f (edgeIndex x y)

abbrev finer (p q : Part) : Prop :=
  ∀ x y, partRel p x y = true → partRel q x y = true

abbrev IsAntichain (A : List Part) : Prop :=
  ∀ p, p ∈ A → ∀ q, q ∈ A → p ≠ q → ¬ finer p q ∧ ¬ finer q p

/-- An antichain is inclusion-maximal when each outside element is comparable
with one of its members, so cannot be added to it. -/
abbrev IsMaximalAntichain (A : List Part) : Prop :=
  IsAntichain A ∧ ∀ q, q ∉ A → ∃ p, p ∈ A ∧ (finer p q ∨ finer q p)

/-- Every listed row defines an equivalence relation. -/
theorem partition_table_rows_valid :
    ∀ p : Part, IsEquivRel (partRel p) := by
  decide

/-- Every equivalence pattern on four points is represented by one of the rows.
The six booleans are the values on pairs 01,02,03,12,13,23.  This finite
classification reduces the enumeration to 64 edge patterns. -/
theorem partition_table_complete_bits :
    ∀ a b c d e f : Bool,
      IsEquivRel (relationFromBits a b c d e f) →
      ∃ p : Part, ∀ x y, partRel p x y = relationFromBits a b c d e f x y := by
  decide

/-- The singleton containing the discrete partition is inclusion-maximal. -/
theorem singleton_bottom_maximal : IsMaximalAntichain [(14 : Part)] := by
  constructor
  · decide
  · decide

/-- The six atoms (partitions merging one pair) form a second maximal antichain. -/
theorem atoms_maximal :
    IsMaximalAntichain [(4 : Part), 7, 10, 11, 12, 13] := by
  constructor
  · decide
  · decide

/-- These two maximal antichains are different. -/
theorem maximal_antichains_not_unique :
    [(14 : Part)] ≠ [(4 : Part), 7, 10, 11, 12, 13] := by
  decide

/-- Under the standard order-theoretic meaning of maximal, uniqueness fails in Π₄. -/
theorem disproof_00000002197 :
    ∃ A B : List Part, IsMaximalAntichain A ∧ IsMaximalAntichain B ∧ A ≠ B := by
  exact ⟨[(14 : Part)], [(4 : Part), 7, 10, 11, 12, 13],
    singleton_bottom_maximal, atoms_maximal, maximal_antichains_not_unique⟩
