/-!
# TLMC conjecture 00000000142 — disproof, Lean concretization

Conjecture 00000000142 claims that the empirical spectral distribution (ESD) of the
prime-indicator matrix `M_n = (1_{i+j prime})_{1<=i,j<=n}` tends to the semicircle law,
and that its linear spectral statistics satisfy a CLT.

Refutation core (see README.md / main.tex): with
`tr M_n = 1` (Lemma `diag_eq_one`) and `tr M_n^2 = N(n) := #{(i,j) in [n]^2 : i+j prime}`
(Theorem `traceSq_eq_pairCount`), the ESD second moment equals `N(n)/n`, and `N(n)/n`
diverges (numerically ~ `n / log(2n)`), while the semicircle law has second moment `1`.

This file concretizes the exact finite-n assertions of the attack:

* `diag_eq_one`      : `tr M_n = 1` for every `n >= 1` (only `i = 1` has `2i` prime).
* `diag_1000`        : instance at `n = 1000`, by `decide`.
* `traceSq_eq_pairCount` : `tr M_n^2 = pairCount n` for every `n` (entries are 0/1 and
  the matrix is symmetric, so `tr M^2 = sum_{i,j} M_ij = N(n)`).
* `pairCount_64/128` : exact values `N(64) = 941`, `N(128) = 3239`, by `decide`.
* `moment_gt_one_*`  : `N(n) > n` at `n = 64, 128`, i.e. the ESD second moment
  `N(n)/n > 1` — already beyond the semicircle's total second moment.
* `moment_growth`    : `N(128)/128 > N(64)/64`, a witness that the second moment grows.

Everything below is proven in bare Lean 4 (no Mathlib) with **zero axioms and zero
`sorry`**: see `Check.lean`, which prints `#print axioms` for every theorem.
Only `rfl`, `decide`, explicit `Eq.trans`/`congrArg` term proofs, and structural
induction are used; tactics known to introduce `propext`/`Quot.sound` (`omega`,
`simp`, `native_decide`) are deliberately avoided.
-/

/-- Evenness as a Bool, by two-step structural recursion (no `Nat.mod` needed). -/
def bev : Nat → Bool
  | 0 => true
  | 1 => false
  | n+2 => bev n

/-- `oddCheck k fuel d`: no odd divisor of `k` in `d, d+2, ..., d+2*(fuel-1)`. -/
def oddCheck (k : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel+1, d => if d * d > k then true else if k % d == 0 then false else oddCheck k fuel (d+2)

/-- Primality: `k < 2` false; `k = 2` true; even `k > 2` false; otherwise trial division
by `3, 5, 7, ...` with early exit `d*d > k`. -/
def isPrime (k : Nat) : Bool :=
  if k < 2 then false
  else if Nat.beq k 2 then true
  else match bev k with
       | true => false
       | false => oddCheck k k 3

theorem bev_add_self : ∀ n, bev (n + n) = true := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    have B : 1 + (m + 1) = (m + 1) + 1 :=
      Eq.trans (Eq.symm (Nat.add_assoc 1 m 1)) (congrArg (fun x => x + 1) (Nat.add_comm 1 m))
    have D : (m+1) + (m+1) = m + ((m+1) + 1) :=
      Eq.trans (Nat.add_assoc m 1 (m+1)) (congrArg (fun x => m + x) B)
    have E : m + ((m+1) + 1) = (m + (m + 1)) + 1 := Eq.symm (Nat.add_assoc m (m+1) 1)
    have F : (m + (m + 1)) + 1 = (m + m + 1) + 1 :=
      congrArg (fun x => x + 1) (Eq.symm (Nat.add_assoc m m 1))
    rw [D, E, F]
    show bev (m + m) = true
    exact ih

theorem bev_two_mul (i : Nat) : bev (2 * i) = true := by
  rw [Nat.two_mul]; exact bev_add_self i

/-- Every even number `>= 4` is composite: `isPrime (2*i) = false` for `i >= 2`. -/
theorem even_composite (i : Nat) (h : 2 ≤ i) : isPrime (2 * i) = false := by
  have h4 : (4 : Nat) ≤ 2 * i := Nat.mul_le_mul_left 2 h
  have h2le : (2 : Nat) ≤ 2 * i :=
    Nat.le_trans (Nat.le_succ 2) (Nat.le_trans (Nat.le_succ 3) h4)
  have hlt : ¬ (2 * i < 2) := Nat.not_lt.mpr h2le
  have hne2 : ¬ (2 * i = 2) := by
    intro he
    have he1 : i = 1 :=
      Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ 1) (Eq.trans he (Eq.symm (Nat.mul_one 2)))
    exact Nat.not_succ_le_self 1 (Eq.subst he1 h)
  have hne2beq : ¬ (Nat.beq (2 * i) 2 = true) := fun hb => hne2 (Nat.eq_of_beq_eq_true hb)
  show ((if 2 * i < 2 then false
        else if Nat.beq (2 * i) 2 then true
        else match bev (2 * i) with
             | true => false
             | false => oddCheck (2 * i) (2 * i) 3)) = false
  rw [if_neg hlt, if_neg hne2beq, bev_two_mul]

/-- Diagonal sum of `M_n`: `diag n = tr M_n = #{i in [1,n] : 2i prime}`. -/
def diag : Nat → Nat
  | 0 => 0
  | n+1 => diag n + (if isPrime ((n+1) + (n+1)) then 1 else 0)

theorem diag_step_zero (n : Nat) (h : 2 ≤ n) : (if isPrime (n + n) then 1 else 0) = 0 := by
  have he : isPrime (n + n) = false :=
    Eq.trans (congrArg isPrime (Eq.symm (Nat.two_mul n))) (even_composite n h)
  rw [he]; rfl

/-- **Trace identity 1.** For every `n >= 1`, `tr M_n = 1`: among `2, 4, ..., 2n` the only
prime is `2`, attained at `i = 1`. Hence the ESD mean is `1/n -> 0`. -/
theorem diag_eq_one : ∀ n, 0 < n → diag n = 1 := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.not_lt_zero 0)
  | succ m ih =>
    intro h
    cases m with
    | zero => rfl
    | succ k =>
      show diag (k+1) + (if isPrime ((k+2) + (k+2)) then 1 else 0) = 1
      have h2 : 2 ≤ k + 2 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
      rw [diag_step_zero (k+2) h2, ih (Nat.succ_le_succ (Nat.zero_le k))]

set_option maxRecDepth 20000 in
-- `decide` instance: tr M_1000 = 1.
theorem diag_1000 : diag 1000 = 1 := by decide

/-- Matrix entry `M_ij = 1_{i+j prime}` (indices `i, j >= 1`). -/
def entry (i j : Nat) : Nat := if isPrime (i + j) then 1 else 0

theorem entry_sym (i j : Nat) : entry i j = entry j i := by
  show (if isPrime (i + j) then (1:Nat) else 0) = (if isPrime (j + i) then (1:Nat) else 0)
  rw [Nat.add_comm i j]

/-- `0/1` entries are idempotent under multiplication after using symmetry. -/
theorem entry_mul_sym (i j : Nat) : entry i j * entry j i = entry i j := by
  have hpeq : isPrime (i + j) = isPrime (j + i) := congrArg isPrime (Nat.add_comm i j)
  show (if isPrime (i + j) then (1:Nat) else 0) * (if isPrime (j + i) then (1:Nat) else 0)
     = (if isPrime (i + j) then (1:Nat) else 0)
  rw [hpeq]
  cases hp : isPrime (j + i) <;> rfl

/-- `rowSum i j = sum_{b=1}^{j} M_{i,b}`. -/
def rowSum : Nat → Nat → Nat
  | _, 0 => 0
  | i, j+1 => rowSum i j + entry i (j+1)

/-- `pc i j = sum_{a=1}^{i} sum_{b=1}^{j} M_{ab}` = number of prime-sum pairs. -/
def pc : Nat → Nat → Nat
  | 0, _ => 0
  | i+1, j => pc i j + rowSum (i+1) j

/-- `trRow i j = sum_{b=1}^{j} M_{i,b} M_{b,i}`. -/
def trRow : Nat → Nat → Nat
  | _, 0 => 0
  | i, j+1 => trRow i j + entry i (j+1) * entry (j+1) i

/-- `trSq i j = sum_{a=1}^{i} sum_{b=1}^{j} M_{ab} M_{ba}` = `tr M^2` contribution. -/
def trSq : Nat → Nat → Nat
  | 0, _ => 0
  | i+1, j => trSq i j + trRow (i+1) j

theorem trRow_eq_rowSum : ∀ (j i : Nat), trRow i j = rowSum i j := by
  intro j
  induction j with
  | zero => intro i; rfl
  | succ j ih =>
    intro i
    show trRow i j + entry i (j+1) * entry (j+1) i = rowSum i j + entry i (j+1)
    rw [ih i, entry_mul_sym]

/-- **Trace identity 2.** `tr M_i^2 = #{(a,b) in [i]^2 : a+b prime}` for all `i, j`:
the matrix is symmetric with 0/1 entries, so `tr M^2 = sum M_{ab} = N(n)`. -/
theorem trSq_eq_pc_aux : ∀ (i j : Nat), trSq i j = pc i j := by
  intro i
  induction i with
  | zero => intro j; cases j <;> rfl
  | succ i ih =>
    intro j
    show trSq i j + trRow (i+1) j = pc i j + rowSum (i+1) j
    rw [ih j, trRow_eq_rowSum j (i+1)]

/-- `N(n) = #{(i,j) in [n]^2 : i+j prime}`. -/
def pairCount (n : Nat) : Nat := pc n n

/-- `tr M_n^2` for the `n x n` prime-indicator matrix. -/
def traceSq (n : Nat) : Nat := trSq n n

theorem traceSq_eq_pairCount (n : Nat) : traceSq n = pairCount n := trSq_eq_pc_aux n n

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
-- exact values; ESD second moment `N(n)/n` at n=8,64,128 is 23/8, 941/64, 3239/128.
theorem pairCount_8 : pairCount 8 = 23 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem pairCount_64 : pairCount 64 = 941 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem pairCount_128 : pairCount 128 = 3239 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
-- ESD second moment at n=64 is 941/64 = 14.7 > 1 (semicircle value).
theorem moment_gt_one_64 : 64 < pairCount 64 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
-- ESD second moment at n=128 is 3239/128 = 25.3 > 1.
theorem moment_gt_one_128 : 128 < pairCount 128 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
-- cross-multiplied witness of growth: N(128)/128 > N(64)/64.
theorem moment_growth : 64 * pairCount 128 > 128 * pairCount 64 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem traceSq_64 : traceSq 64 = 941 := by decide
