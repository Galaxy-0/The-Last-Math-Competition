/-!
# Disproof of TLMC conjecture 00000001067

Conjecture 00000001067 states (verbatim): "Definition: A B_h set (unique h-fold
sums). Conjecture: The maximal B2 set in F_p has size ceil(sqrt(p)) + O(1), and
the O(1) term equals 0 for p = 3 mod 4 (an exact B2 result)."

Attack: at p = 11 (which is = 3 mod 4) the maximal B2 subset of Z/11Z has 3
elements, not ceil(sqrt(11)) = 4.  Machine-checked here with zero axioms:

* `no_ge4_B2_Z11` : every B2 subset of Z/11Z has at most 3 elements
  (exhaustive over all 2^11 = 2048 bitmasks, discharged by kernel reduction);
* `witness_B2_Z11` : {0, 1, 3} is a 3-element B2 subset of Z/11Z, so the
  maximum is exactly 3;
* `disproof_1067` : the counterexample package: 11 = 3 mod 4, max = 3,
  ceil(sqrt(11)) = 4, hence the "O(1) = 0 for p = 3 mod 4" clause is false.

## Encoding (object-level correspondence with the original definitions)

Elements of Z/pZ are the residues 0,...,p-1 (`Nat`).  A subset A is a bitmask
`n : Nat`: bit `i` of `n` is set iff `i ∈ A` (for the masks quantified over,
bits >= p are 0, so `maskPop p n = |A|`).  `isB2 p n = true` iff the sums
`a + b (mod p)` over all unordered pairs `a ≤ b` of elements of A are pairwise
distinct, i.e. A is a B2 set ("unique 2-fold sums", the h = 2 instance of the
conjecture's B_h definition, uniqueness being up to permutation of summands).
All closed computations are discharged by `rfl` (kernel reduction); the only
lemma connecting the exhaustive `Bool` check to a `∀`-statement is proved by
induction with core lemmas, and `#print axioms` confirms every theorem is
axiom-free.
-/

/-- bit `i` of the bitmask `n`. -/
def memMask (n i : Nat) : Bool := n / 2 ^ i % 2 == 1

/-- sums `a + b mod p` over all pairs `a ≤ b` with `a, b` in the mask. -/
def pairSums (p n : Nat) : List Nat :=
  (List.range p).flatMap fun a =>
    (List.range p).filterMap fun b =>
      if decide (a ≤ b) && memMask n a && memMask n b then some ((a + b) % p) else none

/-- number of occurrences of `x` in `l`. -/
def cnt (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => (if x == y then 1 else 0) + cnt x ys

/-- all values in `l` are pairwise distinct. -/
def sumsDistinct : List Nat → Bool
  | [] => true
  | x :: xs => cnt x xs == 0 && sumsDistinct xs

/-- mask `n` is a B2 set of Z/pZ: unique 2-fold sums up to permutation. -/
def isB2 (p n : Nat) : Bool := sumsDistinct (pairSums p n)

/-- number of elements of the mask among the residues `0, …, p-1`. -/
def maskPop (p n : Nat) : Nat := (List.range p).countP (memMask n)

/-- `allRange f k = true` iff `f` is `true` on all of `0, …, k-1`. -/
def allRange (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => allRange f k && f k

/-- Bridge lemma: `allRange` really is a bounded universal quantifier. -/
theorem allRange_spec {f : Nat → Bool} :
    ∀ k : Nat, allRange f k = true → ∀ n : Nat, n < k → f n = true := by
  intro k
  induction k with
  | zero => intro _ n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ k ih =>
    intro h n hn
    have h' : (allRange f k && f k) = true := h
    have h1 : allRange f k = true := by
      cases hb1 : allRange f k with
      | true => rfl
      | false => rw [hb1] at h'; rw [Bool.false_and] at h'; exact h'
    cases Nat.lt_or_ge n k with
    | inl hlt => exact ih h1 n hlt
    | inr hge =>
      have hek : n = k := Nat.le_antisymm (Nat.le_of_lt_succ hn) hge
      rw [hek]
      cases hb2 : f k with
      | true => rfl
      | false =>
        rw [hb2] at h'
        rw [h1, Bool.and_false] at h'
        exact h'

/-- The exhaustive predicate: `n` is *not* a B2 subset of Z/11Z with ≥ 4 elements. -/
def pred11 (n : Nat) : Bool := !((decide (4 ≤ maskPop 11 n)) && isB2 11 n)

-- Exhaustive check over all 2^11 = 2048 masks: no mask with ≥ 4 elements
-- is a B2 set of Z/11Z.  Discharged by kernel reduction (`rfl`).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem check11 : allRange pred11 2048 = true := by rfl

/-- **Upper bound.**  Every B2 subset of Z/11Z has at most 3 elements. -/
theorem no_ge4_B2_Z11 : ∀ n : Nat, n < 2 ^ 11 → isB2 11 n = true → maskPop 11 n ≤ 3 := by
  intro n hn hb
  have hn' : n < 2048 := hn
  have hspec : (!((decide (4 ≤ maskPop 11 n)) && isB2 11 n)) = true :=
    allRange_spec 2048 check11 n hn'
  have key : ¬ (4 ≤ maskPop 11 n) := by
    intro hge
    rw [decide_eq_true hge, hb, Bool.true_and, Bool.not_true] at hspec
    exact Bool.noConfusion hspec
  exact Nat.le_of_lt_succ (Nat.not_le.mp key)

/-- Witness mask for the set {0, 1, 3}: bits 0, 1, 3 set, i.e. 1 + 2 + 8 = 11. -/
def w11 : Nat := 11

/-- **Tightness.**  {0,1,3} is a 3-element B2 subset of Z/11Z: its pair sums
0, 1, 3, 2, 4, 6 are pairwise distinct mod 11. -/
theorem witness_B2_Z11 : isB2 11 w11 = true ∧ maskPop 11 w11 = 3 := ⟨rfl, rfl⟩

/-- floor sqrt by bounded linear search (structural on fuel; used only on
small arguments, so kernel evaluation is immediate). -/
def isqrtAux (n : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc => if (acc + 1) * (acc + 1) ≤ n then isqrtAux n k (acc + 1) else isqrtAux n k acc

/-- floor sqrt for small n (fuel `n` always suffices since ⌊√n⌋ ≤ n). -/
def isqrt (n : Nat) : Nat := isqrtAux n n 0

/-- ⌈√n⌉ for n ≥ 1, via the identity ⌈√n⌉ = ⌊√(n-1)⌋ + 1
(e.g. ⌈√11⌉ = ⌊√10⌋ + 1 = 3 + 1 = 4). -/
def ceilSqrt (n : Nat) : Nat := isqrt (n - 1) + 1

/-- 3² = 9 < 11 < 16 = 4², which pins ⌈√11⌉ = 4 independently of `ceilSqrt`. -/
theorem bounds_11 : 3 * 3 < 11 ∧ 11 < 4 * 4 := by decide

/-- **The counterexample.**  p = 11 = 3 (mod 4): every B2 subset of Z/11Z has
≤ 3 elements ({0,1,3} achieves 3), but ceil(sqrt(11)) = 4.  Hence the "O(1)
term equals 0 for p = 3 mod 4" clause of conjecture 00000001067 is false. -/
theorem disproof_1067 :
    (11 % 4 = 3)
      ∧ ((∀ n : Nat, n < 2 ^ 11 → isB2 11 n = true → maskPop 11 n ≤ 3)
        ∧ ((isB2 11 w11 = true)
          ∧ ((maskPop 11 w11 = 3) ∧ (ceilSqrt 11 = 4)))) :=
  ⟨rfl, no_ge4_B2_Z11, witness_B2_Z11.1, witness_B2_Z11.2, rfl⟩
