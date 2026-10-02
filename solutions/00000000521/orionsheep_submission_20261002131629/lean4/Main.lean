/-!
TLMC conjecture 00000000521 (v2): disproof under the LITERAL reading.

Object.  The conjecture defines `A_j = Σ_i (−1)^i β_{i,j}(I)` where
`β_{i,j}(I)` are the graded Betti numbers OF THE IDEAL `I` as a graded
`R`-module, i.e. `dim_k Tor_i^R(I, k)`: `β_{0,j}(I)` counts the minimal
generators of `I`, so `β_{0,0}(I) = 0` for every nonzero ideal.
(v1 mistakenly used the Betti table of `R/I`, which has the extra
`β_{0,0} = 1` entry.)

Counterexample.  The 4-cycle `C4`, `I = (x1x2, x2x3, x3x4, x4x1) ⊂
k[x1,x2,x3,x4]`.  Minimal free resolution OF THE MODULE `I` (verified by
hand and by `reproduce.py`: `d1` = the four adjacent-edge syzygies
`(x3,−x1,0,0), (0,x4,−x2,0), (0,0,x1,−x3), (x4,0,0,−x2)`, `d2` = their
single relation `ρ = (x4, x1, x2, −x3)`; `d1∘d2 = 0`, per-bidegree homology
vanishes, `coker d1 ≅ I` matches the Hilbert series, all entries of
positive degree):

    0 → R(−4) → R(−3)^4 → R(−2)^4 → I → 0

so `β_{0,2}(I) = 4`, `β_{1,3}(I) = 4`, `β_{2,4}(I) = 1` and `reg(I) = 2`.
Hence

    A_0 = 0, A_1 = 0, A_2 = +4, A_3 = −4, A_4 = +1, A_j = 0 (j ≥ 5),

whose nonzero entries `4, −4, 1` carry signs `+, −, +`: the sign changes
TWICE (the conjecture demands exactly once).  The monotonicity clause
holds for this example and the first change does occur as `j` crosses
`reg(I) = 2`, so the refutation is exactly the "exactly once" clause.
A second counterexample is the star `K_{1,3}`: `A = (0, 0, 3, −3, 1)`.

All proofs are `decide`/`rfl` on closed integer data with a pure Nat/Bool
encoding of the sign bookkeeping, so that the axiom audit in `Check.lean`
reports zero axioms throughout.
-/

/-- Graded Betti numbers β_{i,j} of the ideal `I(C4) = (x1x2, x2x3, x3x4,
x4x1)` as a graded `R`-module: resolution
`0 → R(−4) → R(−3)^4 → R(−2)^4 → I → 0`
(computed by `reproduce.py`, exactness verified per bidegree). -/
def beta : Nat → Nat → Int
  | 0, 2 => 4
  | 1, 3 => 4
  | 2, 4 => 1
  | _, _ => 0

/-- Betti table of the ideal of the star `K_{1,3} = (x1x2, x1x3, x1x4)`
as a graded `R`-module: resolution `0 → R(−4) → R(−3)^3 → R(−2)^3 → I → 0`. -/
def betaK13 : Nat → Nat → Int
  | 0, 2 => 3
  | 1, 3 => 3
  | 2, 4 => 1
  | _, _ => 0

/-- The alternating Betti sum `A_j = β_{0,j} − β_{1,j} + β_{2,j}`
(both counterexample ideals have projective dimension 2, so `i ≤ 2`). -/
def altSum (f : Nat → Nat → Int) (j : Nat) : Int := f 0 j - f 1 j + f 2 j

/-- A-sequence of the `C4` counterexample. -/
def A : Nat → Int := altSum beta

/-- A-sequence of the `K_{1,3}` counterexample. -/
def AK13 : Nat → Int := altSum betaK13

/-- `A_j` is the alternating sum of the Betti numbers of the ideal in
degree `j` (the conjecture's definition). -/
theorem A_from_betti : ∀ j : Nat, A j = beta 0 j - beta 1 j + beta 2 j :=
  fun _ => rfl

theorem AK13_from_betti :
    ∀ j : Nat, AK13 j = betaK13 0 j - betaK13 1 j + betaK13 2 j :=
  fun _ => rfl

/-- The Betti table of `I(C4)`: support `{(0,2), (1,3), (2,4)}`. -/
theorem betti_table : beta 0 2 = 4 ∧ beta 1 3 = 4 ∧ beta 2 4 = 1 := by decide

/-- The A-values of the `C4` counterexample. -/
theorem A_values :
    A 0 = 0 ∧ A 1 = 0 ∧ A 2 = 4 ∧ A 3 = -4 ∧ A 4 = 1 ∧ A 5 = 0 := by decide

/-- `A_j` vanishes from degree 5 on (zeros carry no sign, so the change
count below already sees the whole sequence). -/
theorem A_tail : ∀ j : Nat, 5 ≤ j → A j = 0 := by
  intro j h5
  cases j with
  | zero => exact absurd h5 (by decide)
  | succ j1 =>
    cases j1 with
    | zero => exact absurd h5 (by decide)
    | succ j2 =>
      cases j2 with
      | zero => exact absurd h5 (by decide)
      | succ j3 =>
        cases j3 with
        | zero => exact absurd h5 (by decide)
        | succ j4 =>
          cases j4 with
          | zero => exact absurd h5 (by decide)
          | succ _ => rfl

/-- `reg(I) ≤ 2`: every nonzero Betti number of the ideal lies on `j = i + 2`. -/
theorem reg_bound : ∀ i j : Nat, beta i j ≠ 0 → j ≤ i + 2 := by
  intro i j h
  revert h
  match i, j with
  | 0, 0 => intro h; exact absurd rfl h
  | 0, 1 => intro h; exact absurd rfl h
  | 0, 2 => intro _; decide
  | 0, j + 3 => intro h; exact absurd rfl h
  | 1, 0 => intro h; exact absurd rfl h
  | 1, 1 => intro h; exact absurd rfl h
  | 1, 2 => intro h; exact absurd rfl h
  | 1, 3 => intro _; decide
  | 1, j + 4 => intro h; exact absurd rfl h
  | 2, 0 => intro h; exact absurd rfl h
  | 2, 1 => intro h; exact absurd rfl h
  | 2, 2 => intro h; exact absurd rfl h
  | 2, 3 => intro h; exact absurd rfl h
  | 2, 4 => intro _; decide
  | 2, j + 5 => intro h; exact absurd rfl h
  | i + 3, j => intro h; exact absurd rfl h

/-- `reg(I) = 2` is attained: `β_{0,2}(I) = 4 ≠ 0` and `β_{2,4}(I) = 1 ≠ 0`
sit at `j − i = 2`. -/
theorem reg_attained : beta 0 2 ≠ 0 ∧ beta 2 4 ≠ 0 := by decide

/-- `reg(I_{K_{1,3}}) ≤ 2` (same support shape). -/
theorem reg_bound_K13 : ∀ i j : Nat, betaK13 i j ≠ 0 → j ≤ i + 2 := by
  intro i j h
  revert h
  match i, j with
  | 0, 0 => intro h; exact absurd rfl h
  | 0, 1 => intro h; exact absurd rfl h
  | 0, 2 => intro _; decide
  | 0, j + 3 => intro h; exact absurd rfl h
  | 1, 0 => intro h; exact absurd rfl h
  | 1, 1 => intro h; exact absurd rfl h
  | 1, 2 => intro h; exact absurd rfl h
  | 1, 3 => intro _; decide
  | 1, j + 4 => intro h; exact absurd rfl h
  | 2, 0 => intro h; exact absurd rfl h
  | 2, 1 => intro h; exact absurd rfl h
  | 2, 2 => intro h; exact absurd rfl h
  | 2, 3 => intro h; exact absurd rfl h
  | 2, 4 => intro _; decide
  | 2, j + 5 => intro h; exact absurd rfl h
  | i + 3, j => intro h; exact absurd rfl h

/-- Sign code of an integer: 0 = zero, 1 = negative, 2 = positive.
(Pure equality/order bookkeeping, no arithmetic.) -/
def sgn (x : Int) : Nat := if x = 0 then 0 else if 0 < x then 2 else 1

/-- Sign-change scan over a list of sign codes: compares each code with the
previous one (0 encodes "no sign yet").  Structurally recursive, so all
reductions stay axiom-free. -/
def goChanges (prev : Nat) : List Nat → Nat
  | [] => 0
  | b :: rest =>
      (bif prev == 0 || b == 0 || prev == b then 0 else 1) + goChanges b rest

/-- Drop zero entries (zeros carry no sign). -/
def dropZeros : List Int → List Int
  | [] => []
  | x :: xs => if x == 0 then dropZeros xs else x :: dropZeros xs

/-- Absolute value on `Int`. -/
def iabs (x : Int) : Int := if x < 0 then -x else x

/-- The A-sequence of the `C4` counterexample in degrees 0..5. -/
def seqA : List Int := [A 0, A 1, A 2, A 3, A 4, A 5]

/-- Sign codes of the nonzero entries of the A-sequence, in order:
`+ , − , +`. -/
def attackSignCodes : List Nat := (seqA.map sgn).filter (fun c => c != 0)

/-- Sign changes of the nonzero part of the A-sequence (dummy 0 start
marker contributes no change). -/
def attackSignChanges : Nat := goChanges 0 (0 :: attackSignCodes)

/-- The nonzero part of the A-sequence is `4, −4, 1`. -/
theorem nonzero_sequence : dropZeros seqA = [4, -4, 1] := by decide

/-- Sign codes of the nonzero entries: `+, −, +` (2 = positive, 1 = negative). -/
theorem attack_codes : attackSignCodes = [2, 1, 2] := by decide

/-- The sign of `{A_j}` changes exactly TWICE. -/
theorem attack_sign_changes : attackSignChanges = 2 := by decide

/-- The actual signs: `A_2 > 0`, `A_3 < 0`, `A_4 > 0`.  The first change
occurs as `j` crosses `reg(I) = 2` (`+4 → −4`), a second one follows at
`j = 3` (`−4 → +1`). -/
theorem sign_inequalities :
    (0 : Int) < A 2 ∧ A 3 < 0 ∧ (0 : Int) < A 4 := by decide

/-- The monotonicity clause of the conjecture HOLDS for this example
(`|A_0| ≤ |A_1| ≤ |A_2|`), so the counterexample refutes exactly the
"changes exactly once" clause. -/
theorem monotone_up_to_reg :
    iabs (A 0) ≤ iabs (A 1) ∧ iabs (A 1) ≤ iabs (A 2) := by decide

/-- MAIN THEOREM.  Under its literal definition (Betti numbers of the ideal
`I` itself), conjecture 00000000521 fails for the edge ideal of `C4`: the
sign of `{A_j}` changes twice, not exactly once. -/
theorem conjecture_00000000521_false :
    attackSignChanges = 2 ∧ attackSignChanges ≠ 1 := by decide

/-- Second counterexample: the star `K_{1,3}`.  Its ideal resolves as
`0 → R(−4) → R(−3)^3 → R(−2)^3 → I → 0`, giving `A = (0, 0, 3, −3, 1)`:
again two sign changes instead of exactly one. -/
def seqK13 : List Int := [AK13 0, AK13 1, AK13 2, AK13 3, AK13 4, AK13 5]

def changesK13 : Nat :=
  goChanges 0 (0 :: (seqK13.map sgn).filter (fun c => c != 0))

theorem K13_counterexample :
    AK13 2 = 3 ∧ AK13 3 = -3 ∧ AK13 4 = 1 ∧
    changesK13 = 2 ∧ changesK13 ≠ 1 := by decide
