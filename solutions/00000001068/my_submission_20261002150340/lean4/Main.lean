/-!
# Disproof of TLMC conjecture 00000001068

Conjecture: the maximal sum-free subsets of `F_p` are exactly the intervals
`((p+1)/3, 2(p-1)/3)`, uniquely up to dilation.

Counterexample at `p = 11`: `A = {4, 5, 6, 7}` is an inclusion-maximal
sum-free subset of `F_11` with 4 elements, while
`((p+1)/3, 2(p-1)/3) = (4, 20/3) = {5, 6}` has only 2 elements, so no
dilation of it equals `A`.

Everything is a finite computation in `F_11 = Z/11Z`, encoded in `Nat` with
`(% 11)`.  All proofs are `rfl` (kernel evaluation of the explicit
computations), hence axiom-free.
-/

/-- Membership in a list of residues, as a `Bool`. -/
def memB (x : Nat) (S : List Nat) : Bool := S.any fun y => y == x

/-- `S` is sum-free mod `p`: no sum of two elements of `S` lies in `S`. -/
def sumFreeB (p : Nat) (S : List Nat) : Bool :=
  S.all fun a => S.all fun b => !memB ((a + b) % p) S

/-- `S` is inclusion-maximal sum-free mod `p`: adding any element of
`F_p \ S` breaks sum-freeness. -/
def maxSumFreeB (p : Nat) (S : List Nat) : Bool :=
  (List.range p).all fun x => memB x S || !sumFreeB p (x :: S)

/-- The image of `S` under dilation by `c` in `F_p`. -/
def dil (p c : Nat) (S : List Nat) : List Nat := S.map fun x => (c * x) % p

/-- The conjectured interval `((p+1)/3, 2(p-1)/3)` as integer points of `F_11`.
    Over the rationals `(p+1)/3 < x < 2(p-1)/3` is equivalent to
    `p+1 < 3*x < 2*(p-1)`, i.e. `12 < 3*x < 20` for `p = 11`. -/
def I : List Nat :=
  (List.range 11).filter fun x => 12 < 3 * x && 3 * x < 20

/-- The counterexample `A = {4, 5, 6, 7} ⊆ F_11`. -/
def A : List Nat := [4, 5, 6, 7]

/-- The conjectured interval for `p = 11` is exactly `{5, 6}`. -/
theorem I_eq : I = [5, 6] := rfl

/-- It has only 2 points. -/
theorem I_len : I.length = 2 := by rw [I_eq]; rfl

/-- `A` is sum-free in `F_11`: `A + A = {0,1,2,3,8,9,10} = F_11 \ A`. -/
theorem A_sum_free : sumFreeB 11 A = true := rfl

/-- `A` is inclusion-maximal sum-free in `F_11`. -/
theorem A_maximal : maxSumFreeB 11 A = true := rfl

/-- `|A| = 4 ≠ 2 = |I|`. -/
theorem A_len : A.length = 4 := rfl

/-- No dilation of the conjectured interval equals `A`, checked exhaustively
over all `c ∈ F_11` (every image has at most 2 elements, `A` has 4). -/
theorem A_not_dilation :
    (List.range 11).all fun c => !(dil 11 c I == A) = true := rfl

/-- Main disproof of conjecture 00000001068: at `p = 11` the inclusion-maximal
sum-free set `A = {4,5,6,7}` is not a dilation of the conjectured interval
`((p+1)/3, 2(p-1)/3) = {5,6}`. -/
theorem counterexample_1068 :
    sumFreeB 11 A = true ∧ maxSumFreeB 11 A = true ∧ A.length = 4 ∧
      ((List.range 11).all fun c => !(dil 11 c I == A)) = true :=
  ⟨rfl, rfl, rfl, rfl⟩
