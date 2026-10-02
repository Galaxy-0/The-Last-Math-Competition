/-
# Disproof of TLMC conjecture 00000001068

Conjecture: the maximal sum-free subsets of `F_p` are exactly the intervals
`((p+1)/3, 2(p-1)/3)`, uniquely up to dilation.

Counterexample `p = 11`: `A = {4,5,6,7}` is a maximal sum-free subset of
`F_11` of size `4`, while the conjectured interval is `I = {5,6}` of size `2`:

* `I` is strictly contained in the sum-free set `A`, so `I` is not maximal;
  likewise every nonzero dilate of `I` sits strictly inside a sum-free dilate
  of `A`, so the conjectured family contains no maximal sum-free set at all.
* `A` is maximal (every `x ∉ A` is a sum of two elements of `A`) and
  `|A| = 4 ≠ 2 = |I|`, so `A` is a maximal sum-free set outside the family.

Everything is a closed computation over `F_11`; all proofs are `rfl` on `Bool`
values, so the development depends on no axioms (verified in `Check.lean`).
-/

namespace TLMC1068

/-- Membership in the attack set `A = {4,5,6,7} ⊆ F_11`. -/
def inA (x : Nat) : Bool := x == 4 || x == 5 || x == 6 || x == 7

/-- The 16 ordered pairs of elements of `A`. -/
def pairsA : List (Nat × Nat) :=
  (List.range 4).flatMap fun i => (List.range 4).map fun j => (4 + i, 4 + j)

/-- Sum-free test for `A` in `F_11`: no sum `a + b (mod 11)` with `a, b ∈ A`
lands in `A`. -/
def sumFreeA : Bool := pairsA.all fun p => !inA ((p.1 + p.2) % 11)

/-- Witnesses that every element of `F_11 \ A` is a sum of two elements of
`A`: each entry is `(x, a, b)` with `x ∉ A` and `a + b ≡ x (mod 11)`. -/
def witnessesMaxA : List (Nat × Nat × Nat) :=
  [(0, 5, 6), (1, 5, 7), (2, 6, 7), (3, 7, 7), (8, 4, 4), (9, 4, 5), (10, 4, 6)]

/-- `A` is maximal: nothing outside `A` can be added. -/
def maximalA : Bool :=
  witnessesMaxA.all fun w =>
    !inA w.1 && inA w.2.1 && inA w.2.2 && (w.2.1 + w.2.2) % 11 == w.1

/-- The conjectured interval `((p+1)/3, 2(p-1)/3)` for `p = 11`, with exact
rational bounds: `x ∈ I ⟺ 3·x > 12 ∧ 3·x < 20`. -/
def interval (x : Nat) : Bool := 3 * x > 12 && 3 * x < 20

/-- The conjectured interval, enumerated inside `F_11`. -/
def intervalSet : List Nat := (List.range 11).filter interval

/-- Size of the conjectured interval. -/
def intervalSize : Nat := intervalSet.length

/-- Size of the attack set inside `F_11`. -/
def sizeA : Nat := (List.range 11).filter inA |>.length

/-- Membership in the dilate `d·A = {d·a (mod 11) : a ∈ A}`. -/
def inDilateA (d y : Nat) : Bool :=
  y == (4 * d) % 11 || y == (5 * d) % 11 || y == (6 * d) % 11 || y == (7 * d) % 11

/-- Membership in the dilate `d·I = {5·d, 6·d (mod 11)}`. -/
def inDilateI (d y : Nat) : Bool := y == (5 * d) % 11 || y == (6 * d) % 11

/-- Sum-free test for the dilate `d·A`. -/
def dilateSumFree (d : Nat) : Bool :=
  pairsA.all fun p => !inDilateA d ((d * (p.1 + p.2)) % 11)

/-- The attack set `A = {4,5,6,7}` is sum-free in `F_11`. -/
theorem A_sum_free : sumFreeA = true := rfl

/-- `A` is a maximal sum-free set in `F_11`: every `x ∉ A` lies in `A + A`. -/
theorem A_maximal : maximalA = true := rfl

/-- The conjectured interval for `p = 11` is exactly `{5, 6}`. -/
theorem interval_eq : intervalSet = [5, 6] := rfl

/-- The conjectured interval has size `2`. -/
theorem interval_size : intervalSize = 2 := rfl

/-- The attack set has `4` elements. -/
theorem A_size : sizeA = 4 := rfl

/-- The conjectured interval is contained in the sum-free set `A`. -/
theorem interval_subset_A :
    (List.range 11).all (fun x => !interval x || inA x) = true := rfl

/-- `4 ∈ A \ I`, so the containment is strict: `I` is not a maximal
sum-free set. -/
theorem interval_not_maximal :
    inA 4 = true ∧ interval 4 = false := ⟨rfl, rfl⟩

/-- Every nonzero dilate `d·I` (`d = 1..10`) is strictly contained in the
sum-free dilate `d·A` (witnessed by `4·d mod 11 ∈ dA \ dI`), so no dilate of
the conjectured interval is a maximal sum-free set. -/
def dilatesContained : Bool :=
  (List.range 10).all (fun i =>
    let d := i + 1
    ((List.range 11).all (fun y => !inDilateI d y || inDilateA d y))
      && inDilateA d ((4 * d) % 11)
      && !inDilateI d ((4 * d) % 11)
      && dilateSumFree d)

/-- Dilates of `I` still have two elements (`5·d ≢ 6·d mod 11` for
`d = 1..10`), so no dilate of `I` can equal the 4-element maximal set `A`. -/
def dilatesTwoElems : Bool :=
  (List.range 10).all (fun i => (5 * (i + 1)) % 11 != (6 * (i + 1)) % 11)

/-- Every nonzero dilate `d·I` (`d = 1..10`) is strictly contained in the
sum-free dilate `d·A`, so it is not a maximal sum-free set. -/
theorem dilates_of_interval_not_maximal : dilatesContained = true := rfl

/-- Dilates of `I` still have two elements, so none equals the 4-element
maximal set `A`. -/
theorem dilates_of_interval_size_2 : dilatesTwoElems = true := rfl

/-- **Main disproof.** In `F_11` the set `A = {4,5,6,7}` is a maximal
sum-free subset of size `4`, while the conjectured interval
`((p+1)/3, 2(p-1)/3)` is `{5,6}` of size `2`, strictly contained in `A`;
moreover every nonzero dilate of the interval sits strictly inside a
sum-free dilate of `A`. Hence the conjectured family contains no maximal
sum-free set, and the maximal sum-free set `A` is not a dilate of the
conjectured interval. The conjecture is false. -/
theorem disproof :
    sumFreeA = true ∧ maximalA = true ∧ sizeA = 4 ∧
      intervalSet = [5, 6] ∧ intervalSize = 2 ∧
      inA 4 = true ∧ interval 4 = false ∧
      (List.range 11).all (fun x => !interval x || inA x) = true ∧
      dilatesContained = true ∧ dilatesTwoElems = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end TLMC1068
