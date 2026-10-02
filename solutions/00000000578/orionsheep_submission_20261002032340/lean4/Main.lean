/-!
# Disproof of TLMC conjecture 00000000578

`bin(n, i)` is the binary matroid whose ground set is the set of `i`-subsets of
`{1, ..., n}`, represented over `GF(2)` by the weight-`i` 0/1-vectors, and
`χ_{n,i}` denotes its characteristic polynomial.

Conjecture 00000000578 claims that for all `2 ≤ i ≤ n-2` and all integers
`m ≥ 1`, the value `χ_{n,i}(-m)` is divisible by `i! · (n-i)!`.

This file proves the conjecture **false** by evaluating the characteristic
polynomial directly from the matroid data: the ground set is given as an
explicit list of weight-`i` bitmasks over `GF(2)`, and

`χ_M(t) = Σ_{X ⊆ E} (-1)^|X| · t^(r(E) - r(X))`

is computed by enumerating *all* subsets of the ground set, with the rank
function `r` implemented from scratch below.  No closed formulas are assumed.

The two counterexample instances (both inside the claimed range `2 ≤ i ≤ n-2`,
`m ≥ 1`):

* `bin(5,3)`, `m = 1`:   `χ(-1) = -332`,   remainder `-332 mod 12 = 4 ≠ 0`,
  so `3!·2! = 12 ∤ χ(-1)`  (positive side: `332 mod 12 = 8`);
* `bin(6,2)`, `m = 2`:   `χ(-2) = -2520`, remainder `-2520 mod 48 = 24 ≠ 0`,
  so `2!·4! = 48 ∤ χ(-2)`  (positive side: `2520 mod 48 = 24`).

Divisibility of `b` by a positive `a` is exactly `b % a = 0`, so these
remainder statements are the divisibility failures.

The signed subset sums are carried as `Nat × Nat` (positive part, negative
part) so that all summation reasoning uses only `Nat` addition; conversion to
`Int` happens once, at the final `rfl`.

Every theorem is proved by `rfl`/`decide` from the definitions;
`Check.lean` audits that none depends on any axiom.
-/

namespace TLMC578

/-! ## GF(2) linear algebra on bitmasks

A vector of `GF(2)^n` is a natural number (bitmask); addition is bitwise xor.
Core `Nat.xor` is avoided (its compiled form depends on `propext`); `myXor`
below is a fuel-structural replacement with recursion depth
`log₂(max) + 1`. -/

def xorAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, n, m => 2 * xorAux fuel (n / 2) (m / 2) + (n + m) % 2

/-- Bitwise xor, computed with recursion depth `log₂(n + m) + 1`. -/
def myXor (n m : Nat) : Nat := xorAux (n + m + 1) n m

/-- Insert `v` into an echelon basis (list of bitmasks whose leading bits are
strictly descending), clearing the leading bit of `v` against equal pivots.
The span of the basis together with `v` is preserved; `v = 0` is a no-op. -/
def insertBasis : List Nat → Nat → List Nat
  | bs, 0 => bs
  | [], v => [v]
  | b :: bs, v =>
      if Nat.log2 b < Nat.log2 v then v :: b :: bs
      else if Nat.log2 v < Nat.log2 b then b :: insertBasis bs v
      else b :: insertBasis bs (myXor v b)

/-- Rank of `vs` over `GF(2)` by folding `insertBasis`. -/
def rankOf : List Nat → List Nat → Nat
  | [], bs => bs.length
  | v :: vs, bs => rankOf vs (insertBasis bs v)

/-- The rank function `r` of the represented matroid. -/
def rank (vs : List Nat) : Nat := rankOf vs []

/-- Select the elements of `l` whose index-bit is set in `m` (LSB = index 0),
i.e. the subset `X ⊆ E` encoded by mask `m`. -/
def pick : List Nat → Nat → List Nat
  | [], _ => []
  | a :: as, m => (if m % 2 = 1 then [a] else []) ++ pick as (m / 2)

/-! ## Signed sums as pairs of natural numbers

A value `p.1 - p.2` is represented by the pair `p : Nat × Nat`.
Addition is componentwise, hence associative by `Nat.add_assoc`. -/

/-- `p + q` in the pair representation. -/
def vadd (p q : Nat × Nat) : Nat × Nat := (p.1 + q.1, p.2 + q.2)

theorem vadd_assoc (p q r : Nat × Nat) :
    vadd p (vadd q r) = vadd (vadd p q) r := by
  show (p.1 + (q.1 + r.1), p.2 + (q.2 + r.2))
     = ((p.1 + q.1) + r.1, (p.2 + q.2) + r.2)
  rw [Nat.add_assoc, Nat.add_assoc]

theorem vadd_comm (p q : Nat × Nat) : vadd p q = vadd q p := by
  show (p.1 + q.1, p.2 + q.2) = (q.1 + p.1, q.2 + p.2)
  rw [Nat.add_comm p.1 q.1, Nat.add_comm p.2 q.2]

/-! ## Characteristic polynomial by subset enumeration

`χ(t) = Σ_X (-1)^|X| t^(rE - rX)` at `t = -base` gives, with
`d = rE - r(X)`, the terms `(-1)^(|X| + d) · base^d`. -/

/-- The term `(-1)^(|X| + d) · base^d` as a signed pair, where `X` is the
subset selected by mask `idx` and `d = rE - r(X)`. -/
def chiTermV (E : List Nat) (rE : Nat) (base : Nat) (idx : Nat) : Nat × Nat :=
  let X := pick E idx
  let d := rE - rank X
  if (X.length + d) % 2 = 0 then (base ^ d, 0) else (0, base ^ d)

/-- Sum of the terms over subset masks `start, ..., start + bound - 1`. -/
def chiFromV (E : List Nat) (rE : Nat) (base : Nat) (start : Nat) :
    Nat → Nat × Nat
  | 0 => (0, 0)
  | m + 1 => vadd (chiTermV E rE base start) (chiFromV E rE base (start + 1) m)

/-- `χ_{bin(E)}(-base)` as a signed pair over all `2^|E|` subsets. -/
def chiTotalV (E : List Nat) (base : Nat) : Nat × Nat :=
  chiFromV E (rank E) base 0 (2 ^ E.length)

/-- The integer value of a signed pair. -/
def vval (p : Nat × Nat) : Int := (p.1 : Int) - (p.2 : Int)

/-- `χ_{bin(E)}(-base)`. -/
def chiNeg (E : List Nat) (base : Nat) : Int := vval (chiTotalV E base)

/-! ## Ground sets

`E53` is the ground set of `bin(5,3)`: the ten weight-3 masks of `GF(2)^5`
(bit `j` = coordinate `j+1`).  `E62` is the ground set of `bin(6,2)`: the
fifteen weight-2 masks of `GF(2)^6`. -/

def E53 : List Nat := [7, 11, 19, 13, 21, 25, 14, 22, 26, 28]

def E62 : List Nat := [3, 5, 9, 17, 33, 6, 10, 18, 34, 12, 20, 36, 24, 40, 48]

/-! ## Chunking lemmas

The 32768-subset sums are evaluated in 1024-subset chunks to keep the kernel
evaluation depth small. -/

/-- `chiFromV` over `a + b` consecutive masks splits at `a`. -/
theorem chiFromV_add (E : List Nat) (rE : Nat) (base : Nat) (start a b : Nat) :
    chiFromV E rE base start (a + b)
      = vadd (chiFromV E rE base start a)
          (chiFromV E rE base (start + a) b) := by
  induction a generalizing start with
  | zero =>
      rw [Nat.zero_add]
      have h1 : chiFromV E rE base start 0 = (0, 0) := rfl
      have h2 : chiFromV E rE base (start + 0) b = chiFromV E rE base start b := rfl
      rw [h1, h2]
      show chiFromV E rE base start b
        = (0 + (chiFromV E rE base start b).1, 0 + (chiFromV E rE base start b).2)
      rw [Nat.zero_add, Nat.zero_add]
  | succ a ih =>
      have h1 : (a + 1) + b = a + b + 1 := Nat.add_right_comm a 1 b
      have h2 : start + (a + 1) = start + 1 + a := by
        rw [Nat.add_comm a 1, ← Nat.add_assoc]
      rw [h1, h2]
      show vadd (chiTermV E rE base start)
            (chiFromV E rE base (start + 1) (a + b))
        = vadd (vadd (chiTermV E rE base start)
                (chiFromV E rE base (start + 1) a))
            (chiFromV E rE base (start + 1 + a) b)
      rw [ih (start + 1), vadd_assoc]

/-- Sum of the first `j` chunks of 1024 consecutive masks. -/
def chunkSumV (E : List Nat) (rE : Nat) (base : Nat) (start : Nat) :
    Nat → Nat × Nat
  | 0 => (0, 0)
  | j + 1 =>
      vadd (chiFromV E rE base (start + 1024 * j) 1024)
        (chunkSumV E rE base start j)

theorem chiFromV_eq_chunkSumV (E : List Nat) (rE : Nat) (base : Nat)
    (start j : Nat) :
    chiFromV E rE base start (1024 * j) = chunkSumV E rE base start j := by
  induction j generalizing start with
  | zero => rfl
  | succ j ih =>
      show chiFromV E rE base start (1024 * j + 1024)
        = vadd (chiFromV E rE base (start + 1024 * j) 1024)
            (chunkSumV E rE base start j)
      rw [chiFromV_add E rE base start (1024 * j) 1024, ih, vadd_comm]

/-! ## Counterexample 1: bin(5,3), m = 1

The full subset enumeration (2^10 = 1024 subsets) gives rank 5 and
`χ(-1) = -332`; since `332 = 12·27 + 8`, `12 = 3!·2!` does not divide `χ(-1)`.

Boundary: `bin(5,3)` also fails at `m = 2` (`χ(-2) = -1263`), while it passes
at `m = 3` (`χ(-3) = -3624 = 302·12`). -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem rankE53 : rank E53 = 5 := by decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem chiE53m1 : chiNeg E53 1 = -332 := by
  show vval (chiFromV E53 (rank E53) 1 0 (2 ^ List.length E53)) = -332
  rw [rankE53, show (2 ^ List.length E53) = 1024 from rfl]
  rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem chiE53m2 : chiNeg E53 2 = -1263 := by
  show vval (chiFromV E53 (rank E53) 2 0 (2 ^ List.length E53)) = -1263
  rw [rankE53, show (2 ^ List.length E53) = 1024 from rfl]
  rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem chiE53m3 : chiNeg E53 3 = -3624 := by
  show vval (chiFromV E53 (rank E53) 3 0 (2 ^ List.length E53)) = -3624
  rw [rankE53, show (2 ^ List.length E53) = 1024 from rfl]
  rfl

/-! ## Counterexample 2: bin(6,2), m = 2

The full subset enumeration (2^15 = 32768 subsets, evaluated as 32 chunks of
1024) gives rank 5 and `χ(-2) = -2520`; since `2520 = 48·52 + 24`, `48 = 2!·4!`
does not divide `χ(-2)`.

Boundary: `bin(6,2)` *does* satisfy the divisibility claim at `m = 1`
(`χ(-1) = -720 = 15·48`) and at `m = 3` (`χ(-3) = -6720 = 140·48`) — the
failure is specific to `m = 2`. -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem rankE62 : rank E62 = 5 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem chiE62m1 : chiNeg E62 1 = -720 := by
  show vval (chiFromV E62 (rank E62) 1 0 (2 ^ List.length E62)) = -720
  rw [rankE62, show (2 ^ List.length E62) = 1024 * 32 from rfl,
    chiFromV_eq_chunkSumV E62 5 1 0 32]
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem chiE62m2 : chiNeg E62 2 = -2520 := by
  show vval (chiFromV E62 (rank E62) 2 0 (2 ^ List.length E62)) = -2520
  rw [rankE62, show (2 ^ List.length E62) = 1024 * 32 from rfl,
    chiFromV_eq_chunkSumV E62 5 2 0 32]
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem chiE62m3 : chiNeg E62 3 = -6720 := by
  show vval (chiFromV E62 (rank E62) 3 0 (2 ^ List.length E62)) = -6720
  rw [rankE62, show (2 ^ List.length E62) = 1024 * 32 from rfl,
    chiFromV_eq_chunkSumV E62 5 3 0 32]
  rfl

/-! ## Divisibility failure

For positive `a`, `a ∣ b` is equivalent to `b % a = 0`; the nonzero
remainders below are therefore exactly the failure of the conjecture's
divisibility claim. -/

theorem rem_nat_332 : (332 : Nat) % 12 = 8 := by rfl

theorem rem_nat_2520 : (2520 : Nat) % 48 = 24 := by rfl

theorem int_rem_53 : (-332 : Int) % 12 = 4 := by rfl

theorem int_rem_62 : (-2520 : Int) % 48 = 24 := by rfl

theorem not_dvd_int_12_332 : ¬ ((-332 : Int) % 12 = 0) := by decide

theorem not_dvd_int_48_2520 : ¬ ((-2520 : Int) % 48 = 0) := by decide

/-! ## Conclusion

Both attacking instances lie inside the conjecture's range
(`2 ≤ 3 ≤ 3` with `m = 1`, and `2 ≤ 2 ≤ 4` with `m = 2`), so the universal
claim of conjecture 00000000578 is false; the asserted Eulerian-quotient
consequence is never reached. -/

theorem counter_bin53 :
    rank E53 = 5 ∧ chiNeg E53 1 = -332 ∧ ¬ ((-332 : Int) % 12 = 0) :=
  ⟨rankE53, chiE53m1, not_dvd_int_12_332⟩

theorem counter_bin62 :
    rank E62 = 5 ∧ chiNeg E62 2 = -2520 ∧ ¬ ((-2520 : Int) % 48 = 0) :=
  ⟨rankE62, chiE62m2, not_dvd_int_48_2520⟩

theorem conjecture_00000000578_false :
    (rank E53 = 5 ∧ chiNeg E53 1 = -332 ∧ ¬ ((-332 : Int) % 12 = 0)) ∧
    (rank E62 = 5 ∧ chiNeg E62 2 = -2520 ∧ ¬ ((-2520 : Int) % 48 = 0)) :=
  ⟨⟨rankE53, chiE53m1, not_dvd_int_12_332⟩,
   ⟨rankE62, chiE62m2, not_dvd_int_48_2520⟩⟩

end TLMC578
