/-!
# Disproof of TLMC conjecture 00000001136

Conjecture 00000001136: `BS(s1,…,sk)` is Gorenstein **if and only if** every letter
of the word `s1…sk` occurs equally often.

Counterexample: the reduced word `s1 s2 s1 = w0 ∈ S3` has letter counts `(2, 1)`
(unequal), yet every Bott–Samelson variety built from a reduced word is an iterated
`ℙ¹`-bundle (Demazure 1974), hence smooth projective, and smoothness implies the
Gorenstein property.  So `BS(s1,s2,s1)` is Gorenstein although the letters do not
occur equally often: the "only if" direction fails.

Formalization notes (bare Lean 4 core, no `Mathlib`):
* letters are `Nat` (`1` encodes `s1`, `2` encodes `s2`);
* simple reflections and `w0 ∈ S3` are concrete functions `Nat → Nat`;
* the geometric side is an abstract predicate `G` together with the classical
  hypothesis `∀ w, G w` (every Bott–Samelson variety is Gorenstein, a consequence
  of smoothness); the theorem then refutes the "iff" for **any** such `G`.
* All proofs below are axiom-free (checked by `#print axioms` in `Check.lean`):
  no `sorry`, no `Classical.choice`, no `propext`, no `Quot.sound`.
-/

/-- Letter count of the letter `a` in the word `w` (`a = 1` encodes `s1`,
`a = 2` encodes `s2`). -/
def cnt (w : List Nat) (a : Nat) : Nat :=
  w.foldr (fun b acc => if b == a then acc + 1 else acc) 0

/-- The conjecture's right-hand side: every letter occurring in the word
occurs equally often (for a two-letter word: equal numbers of `s1` and `s2`). -/
def EqualCounts (w : List Nat) : Prop := cnt w 1 = cnt w 2

/-- The counterexample word `s1 s2 s1` (the longest element `w0` of `S3`). -/
def w121 : List Nat := [1, 2, 1]

theorem counts_s1 : cnt w121 1 = 2 := by decide

theorem counts_s2 : cnt w121 2 = 1 := by decide

/-- The word `s1s2s1` does NOT have equally often occurring letters. -/
theorem counts_not_equal : ¬ EqualCounts w121 := by
  intro h
  have h' : cnt w121 1 = cnt w121 2 := h
  rw [counts_s1, counts_s2] at h'
  exact absurd h' (by decide : (2 : Nat) ≠ 1)

/-! ### The word `s1s2s1` is a genuine reduced expression of `w0 ∈ S3` -/

/-- Simple reflection `s1` of `S3` (swaps 1 and 2; fixes 3). -/
def s1 : Nat → Nat := fun x => if x = 1 then 2 else if x = 2 then 1 else x

/-- Simple reflection `s2` of `S3` (swaps 2 and 3; fixes 1). -/
def s2 : Nat → Nat := fun x => if x = 2 then 3 else if x = 3 then 2 else x

/-- The longest element `w0 ∈ S3`: `1 ↦ 3`, `2 ↦ 2`, `3 ↦ 1`. -/
def w0 : Nat → Nat := fun x => if x = 1 then 3 else if x = 2 then 2 else 1

/-- Reading the word left to right (leftmost letter applied first), the product
`s1 s2 s1` acts on `{1,2,3}` exactly as `w0`. -/
theorem word_eval_w0 :
    s1 (s2 (s1 1)) = 3 ∧ s1 (s2 (s1 2)) = 2 ∧ s1 (s2 (s1 3)) = 1 := by decide

/-- Number of inversions of `w0` on `{1,2,3}`, i.e. its Coxeter length. -/
def invw0 : Nat :=
  (if (w0 1 : Nat) > w0 2 then 1 else 0) +
  (if (w0 1 : Nat) > w0 3 then 1 else 0) +
  (if (w0 2 : Nat) > w0 3 then 1 else 0)

/-- The word `s1s2s1` is REDUCED: its length `3` equals the Coxeter length of
`w0` (the number of inversions of `w0` on `{1,2,3}`). -/
theorem word_reduced : w121.length = 3 ∧ invw0 = 3 ∧ w121.length = invw0 := by decide

/-! ### The conjecture is false -/

/-- The conjecture's "iff" fails.  Hypotheses:
* `G w` : the Bott–Samelson variety `BS(w)` is Gorenstein;
* `hG` : **every** Bott–Samelson variety is Gorenstein — a classical theorem,
  since `BS(w)` for a reduced word is an iterated `ℙ¹`-bundle (Demazure 1974),
  hence smooth projective, and smoothness implies Gorenstein.

Conclusion: it is NOT the case that `BS(w)` is Gorenstein iff each letter occurs
equally often.  Witness: `w = s1s2s1 = w0 ∈ S3`, a reduced word with letter
counts `(2, 1)`. -/
theorem conjecture_1136_false (G : List Nat → Prop) (hG : ∀ w, G w) :
    ¬ (∀ w, G w ↔ EqualCounts w) := by
  intro H
  have hGeq : EqualCounts w121 := (H w121).1 (hG w121)
  exact counts_not_equal hGeq
