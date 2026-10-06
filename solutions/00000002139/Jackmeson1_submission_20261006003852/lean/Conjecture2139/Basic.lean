import Mathlib

/-!
# Conjecture 00000002139: the floor-sum recursion follows the Euclidean algorithm

The floor-sum is `floorSum n m a b = ∑_{i=0}^{n-1} ⌊(a*i+b)/m⌋` (natural numbers, `m ≥ 1`; Lean's `/`
on `ℕ` is floor division).  Its Euclid-like recursion (AtCoder Library `floor_sum`) reduces
`a, b` modulo `m`, then swaps the roles of modulus and slope.

We prove, for every `n, a, b` and every `m ≥ 1`:
* the recursion `fsRec` computes `floorSum`;
* the list of (modulus, slope) pairs of its calls is exactly the list of argument pairs of
  Euclid's algorithm `gcd x y → gcd (y % x) x → ⋯` started at `(m, a)`, whose last modulus is
  `Nat.gcd m a`;
* the number of calls is at most `2 * log₂ m + 1` (and at most `2 * log₂ min(a, m) + 2`), and on
  consecutive Fibonacci inputs it is at least `log₂ m + 1`.
For the AtCoder loop `aclRec`, which may stop earlier, we prove that it computes the floor sum,
that its path is a prefix of the Euclid path, and the same call upper bound (the exact trace,
terminal gcd and Fibonacci lower bound are proved for `fsRec` only).  Signed `a, b` reduce to this case by one normalization step.
-/

namespace C2139

open Finset

/-- The floor-sum `∑_{i<n} ⌊(a*i+b)/m⌋`. -/
def floorSum (n m a b : ℕ) : ℕ := ∑ i ∈ range n, (a * i + b) / m

/-- Euclid's algorithm on `(x, y)`: the argument pairs of the successive calls
`gcd x y → gcd (y % x) x → ⋯`, stopping when the first argument is `0`. -/
def euclidTrace (x y : ℕ) : List (ℕ × ℕ) :=
  if _hx : x = 0 then [] else (x, y) :: euclidTrace (y % x) x
termination_by x
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _hx)

/-- The Euclid-like floor-sum recursion, instrumented with its call path.  On the call with
modulus `m` and slope `a` it adds `n(n-1)/2*⌊a/m⌋ + n*⌊b/m⌋`, reduces `a, b` modulo `m`, stops if
the reduced slope is `0`, and otherwise recurses on `(⌊y/m⌋, a mod m, m, y mod m)` with
`y = (a mod m)*n + (b mod m)`.  The second component lists the (modulus, slope) pair of every call. -/
def fsRec (n m a b : ℕ) : ℕ × List (ℕ × ℕ) :=
  if hm : m = 0 then (0, []) else
  if a % m = 0 then (n * (n - 1) / 2 * (a / m) + n * (b / m), [(m, a)]) else
  let y := a % m * n + b % m
  let r := fsRec (y / m) (a % m) m (y % m)
  (n * (n - 1) / 2 * (a / m) + n * (b / m) + r.1, (m, a) :: r.2)
termination_by m
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero hm)

/-- The AtCoder Library loop `floor_sum_unsigned`, as a recursion with its call path: identical to
`fsRec` except that it stops as soon as `y = (a mod m)*n + (b mod m) < m`. -/
def aclRec (n m a b : ℕ) : ℕ × List (ℕ × ℕ) :=
  if hm : m = 0 then (0, []) else
  if a % m * n + b % m < m then (n * (n - 1) / 2 * (a / m) + n * (b / m), [(m, a)]) else
  let y := a % m * n + b % m
  let r := aclRec (y / m) (a % m) m (y % m)
  (n * (n - 1) / 2 * (a / m) + n * (b / m) + r.1, (m, a) :: r.2)
termination_by m
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero hm)

/-! ## Floor-sum identities -/

/-- Counting: `#{k < N : c(k+1) ≤ x} = min N ⌊x/c⌋`. -/
theorem count_eq (c x N : ℕ) (hc : 0 < c) :
    ∑ k ∈ range N, (if c * (k + 1) ≤ x then 1 else 0) = min N (x / c) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    have h : c * (N + 1) ≤ x ↔ N + 1 ≤ x / c := by
      rw [Nat.le_div_iff_mul_le hc, mul_comm]
    by_cases hx : c * (N + 1) ≤ x
    · rw [if_pos hx]; have := h.1 hx; omega
    · rw [if_neg hx]; have : ¬ N + 1 ≤ x / c := fun h' => hx (h.2 h'); omega

/-- Reduction: `F(n,m,a,b) = n(n-1)/2*⌊a/m⌋ + n*⌊b/m⌋ + F(n,m,a mod m,b mod m)`. -/
theorem floorSum_reduce (n m a b : ℕ) (hm : 0 < m) :
    floorSum n m a b = n * (n - 1) / 2 * (a / m) + n * (b / m) + floorSum n m (a % m) (b % m) := by
  have key : ∀ i, (a * i + b) / m = (a / m) * i + b / m + (a % m * i + b % m) / m := by
    intro i
    have e : a * i + b = (a % m * i + b % m) + m * ((a / m) * i + b / m) := by
      conv_lhs => rw [← Nat.mod_add_div a m, ← Nat.mod_add_div b m]
      ring
    rw [e, Nat.add_mul_div_left _ _ hm]; ring
  simp only [floorSum, key, sum_add_distrib, sum_const, card_range, smul_eq_mul]
  rw [← mul_sum, sum_range_id]
  ring

/-- Swap (lattice points under a line, counted by rows and by columns): for `0 < a` and `b < m`,
`F(n,m,a,b) = F(⌊y/m⌋, a, m, y mod m)` where `y = a*n+b`. -/
theorem floorSum_swap (n m a b : ℕ) (ha : 0 < a) (hb : b < m) :
    floorSum n m a b = floorSum ((a * n + b) / m) a m ((a * n + b) % m) := by
  have hm : 0 < m := by omega
  set N := (a * n + b) / m with hN
  set B := (a * n + b) % m with hB
  have hy : m * N + B = a * n + b := Nat.div_add_mod _ _
  -- rows
  have rows : floorSum n m a b =
      ∑ i ∈ range n, ∑ k ∈ range N, (if m * (k + 1) ≤ a * i + b then 1 else 0) := by
    unfold floorSum
    refine sum_congr rfl fun i hi => ?_
    rw [count_eq _ _ _ hm]
    have : (a * i + b) / m ≤ N := by
      apply Nat.div_le_div_right
      have := Nat.mul_le_mul_left a (le_of_lt (mem_range.1 hi)); omega
    omega
  -- columns
  have cols : floorSum N a m B =
      ∑ k ∈ range N, ∑ i ∈ range n, (if a * (i + 1) ≤ m * k + B then 1 else 0) := by
    unfold floorSum
    refine sum_congr rfl fun k hk => ?_
    rw [count_eq _ _ _ ha]
    have hk' : m * (k + 1) ≤ m * N := Nat.mul_le_mul_left m (mem_range.1 hk)
    have : (m * k + B) / a ≤ n := by
      apply Nat.div_le_of_le_mul
      have : m * (k + 1) = m * k + m := by ring
      omega
    omega
  rw [rows, sum_comm, cols, ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  rw [← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hk := mem_range.1 hk
  have hi := mem_range.1 hi
  -- linear arithmetic over the products
  have e1 : m * (N - 1 - k + 1) + m * k = m * N := by
    rw [← mul_add]; congr 1; omega
  have e2 : a * (n - 1 - i) + a * (i + 1) = a * n := by
    rw [← mul_add]; congr 1; omega
  generalize m * (N - 1 - k + 1) = P at *
  generalize m * k = P' at *
  generalize a * (n - 1 - i) = Q at *
  generalize a * (i + 1) = Q' at *
  have : (P ≤ Q + b) ↔ (Q' ≤ P' + B) := by omega
  simp only [this]

/-! ## Euclid's algorithm -/

theorem euclidTrace_zero (y : ℕ) : euclidTrace 0 y = [] := by
  rw [euclidTrace]; simp

theorem euclidTrace_pos {x : ℕ} (y : ℕ) (hx : 0 < x) :
    euclidTrace x y = (x, y) :: euclidTrace (y % x) x := by
  rw [euclidTrace]; simp [hx.ne']

/-- Euclid's algorithm ends at the gcd: the last modulus on the path is `Nat.gcd x y`. -/
theorem euclidTrace_last (x : ℕ) : ∀ y, 0 < x →
    (euclidTrace x y).getLast?.map Prod.fst = some (Nat.gcd x y) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro y hx
    rw [euclidTrace_pos y hx]
    by_cases hr : y % x = 0
    · rw [hr, euclidTrace_zero]
      simp [Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero hr)]
    · have h := ih (y % x) (Nat.mod_lt _ hx) x (Nat.pos_of_ne_zero hr)
      rw [Nat.gcd_rec x y, List.getLast?_cons]
      cases hl : (euclidTrace (y % x) x).getLast? with
      | none => simp [hl] at h
      | some p => simp_all [Nat.gcd_comm]

/-- Lamé-type bound: Euclid's algorithm on `(x, y)` with `x ≥ 1` makes at most `2 log₂ x + 1` calls. -/
theorem euclidTrace_length (x : ℕ) : ∀ y, 0 < x →
    (euclidTrace x y).length ≤ 2 * Nat.log 2 x + 1 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro y hx
    rw [euclidTrace_pos y hx]
    set r := y % x with hr
    have hrx : r < x := Nat.mod_lt _ hx
    rcases Nat.eq_zero_or_pos r with h0 | hr0
    · rw [h0, euclidTrace_zero]; simp
    rw [euclidTrace_pos x hr0]
    set s := x % r with hs
    have hsr : s < r := Nat.mod_lt _ hr0
    -- 2s < x
    have h2s : 2 * s < x := by
      have h1 : r * (x / r) + s = x := Nat.div_add_mod x r
      have h2 : 1 ≤ x / r := (Nat.one_le_div_iff hr0).2 hrx.le
      have : r ≤ r * (x / r) := Nat.le_mul_of_pos_right r h2
      omega
    have hlog1 : 1 ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) (by omega)
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · rw [hs0, euclidTrace_zero]; simp; omega
    · have h := ih s (by omega) r hs0
      have hl : Nat.log 2 s + 1 ≤ Nat.log 2 x := by
        rw [← Nat.log_mul_base (by norm_num) hs0.ne']
        exact Nat.log_mono_right (by omega)
      simp only [List.length_cons]
      omega

/-- The bound in terms of `min(x, y)`: at most `2 log₂ min(y, x) + 2` calls. -/
theorem euclidTrace_length_min (x y : ℕ) (hx : 0 < x) :
    (euclidTrace x y).length ≤ 2 * Nat.log 2 (min y x) + 2 := by
  rw [euclidTrace_pos y hx]
  rcases Nat.eq_zero_or_pos (y % x) with h0 | hr
  · rw [h0, euclidTrace_zero]; simp
  · have h := euclidTrace_length (y % x) x hr
    have : Nat.log 2 (y % x) ≤ Nat.log 2 (min y x) :=
      Nat.log_mono_right (le_min (Nat.mod_le y x) (Nat.mod_lt y hx).le)
    simp only [List.length_cons]; omega

/-! ## The recursion computes the floor-sum and follows Euclid -/

theorem floorSum_zero_slope (n m b : ℕ) (hm : 0 < m) : floorSum n m 0 (b % m) = 0 := by
  simp [floorSum, Nat.div_eq_of_lt (Nat.mod_lt b hm)]

theorem fsRec_spec (m : ℕ) : ∀ n a b,
    (fsRec n m a b).1 = floorSum n m a b ∧ (fsRec n m a b).2 = euclidTrace m a := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n a b
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · subst h0; rw [fsRec, euclidTrace_zero]; simp [floorSum]
    rw [fsRec, dif_neg hm.ne', euclidTrace_pos a hm, floorSum_reduce n m a b hm]
    by_cases ha : a % m = 0
    · rw [if_pos ha, ha, euclidTrace_zero, floorSum_zero_slope n m b hm]; simp
    · rw [if_neg ha]
      obtain ⟨h1, h2⟩ := ih (a % m) (Nat.mod_lt _ hm) ((a % m * n + b % m) / m) m
        ((a % m * n + b % m) % m)
      refine ⟨?_, by simp only [h2]⟩
      simp only [h1]
      rw [floorSum_swap n m (a % m) (b % m) (Nat.pos_of_ne_zero ha) (Nat.mod_lt _ hm)]

theorem aclRec_spec (m : ℕ) : ∀ n a b,
    (aclRec n m a b).1 = floorSum n m a b ∧ (aclRec n m a b).2 <+: euclidTrace m a := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n a b
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · subst h0; rw [aclRec, euclidTrace_zero]; simp [floorSum]
    rw [aclRec, dif_neg hm.ne', euclidTrace_pos a hm, floorSum_reduce n m a b hm]
    by_cases hy : a % m * n + b % m < m
    · rw [if_pos hy]
      refine ⟨?_, by simp⟩
      have : floorSum n m (a % m) (b % m) = 0 := by
        apply sum_eq_zero; intro i hi
        apply Nat.div_eq_of_lt
        have := Nat.mul_le_mul_left (a % m) (le_of_lt (mem_range.1 hi))
        omega
      simp [this]
    · rw [if_neg hy]
      have ha : a % m ≠ 0 := by
        intro h; rw [h] at hy; have := Nat.mod_lt b hm; simp at hy; omega
      obtain ⟨h1, h2⟩ := ih (a % m) (Nat.mod_lt _ hm) ((a % m * n + b % m) / m) m
        ((a % m * n + b % m) % m)
      refine ⟨?_, by simpa using h2⟩
      simp only [h1]
      rw [floorSum_swap n m (a % m) (b % m) (Nat.pos_of_ne_zero ha) (Nat.mod_lt _ hm)]

/-! ## Integer slopes and offsets (AtCoder `floor_sum` with signed `a, b`) -/

/-- The floor-sum with integer `a, b`, using the genuine floor `⌊(a*i+b)/m⌋` of a rational number. -/
def floorSumInt (n m : ℕ) (a b : ℤ) : ℤ := ∑ i ∈ range n, ⌊((a * i + b : ℤ) : ℚ) / m⌋

/-- The natural-number floor-sum (with `ℕ` division) is the genuine floor-sum. -/
theorem floorSum_cast (n m a b : ℕ) : (floorSum n m a b : ℤ) = floorSumInt n m a b := by
  unfold floorSum floorSumInt
  rw [Nat.cast_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Rat.floor_intCast_div_natCast]
  norm_cast

theorem floorSumInt_term (m : ℕ) (a b : ℤ) (i : ℕ) (hm : 0 < m) :
    ⌊((a * i + b : ℤ) : ℚ) / m⌋ =
      ⌊(a : ℚ) / m⌋ * i + ⌊(b : ℚ) / m⌋ + (((a % m).toNat * i + (b % m).toNat) / m : ℕ) := by
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Rat.floor_intCast_div_natCast, Rat.floor_intCast_div_natCast, Rat.floor_intCast_div_natCast]
  have ea : ((a % m).toNat : ℤ) = a % m := Int.toNat_of_nonneg (Int.emod_nonneg a hm')
  have eb : ((b % m).toNat : ℤ) = b % m := Int.toNat_of_nonneg (Int.emod_nonneg b hm')
  rw [Int.natCast_ediv]; push_cast; rw [ea, eb]
  have e : a * i + b = (a % m * i + b % m) + m * (a / m * i + b / m) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv a m, ← Int.emod_add_mul_ediv b m]
    ring
  rw [e, Int.add_mul_ediv_left _ _ hm']; ring

/-- One normalization step reduces signed `a, b` to `a mod m, b mod m ∈ [0, m)`. -/
theorem floorSumInt_normalize (n m : ℕ) (a b : ℤ) (hm : 0 < m) :
    floorSumInt n m a b = ⌊(a : ℚ) / m⌋ * ((n * (n - 1) / 2 : ℕ) : ℤ) + n * ⌊(b : ℚ) / m⌋ +
      floorSum n m (a % m).toNat (b % m).toNat := by
  simp only [floorSumInt, floorSumInt_term _ _ _ _ hm, floorSum, sum_add_distrib, sum_const,
    card_range, nsmul_eq_mul, Nat.cast_sum]
  rw [← mul_sum, ← sum_range_id]; push_cast; ring

/-- Signed version: after the normalization step, the recursion `fsRec` computes the floor-sum,
and its path is Euclid's path from `(m, a mod m)`, of length at most `2 log₂ m + 1`. -/
theorem floorSumInt_recursion (n m : ℕ) (a b : ℤ) (hm : 0 < m) :
    floorSumInt n m a b = ⌊(a : ℚ) / m⌋ * ((n * (n - 1) / 2 : ℕ) : ℤ) + n * ⌊(b : ℚ) / m⌋ +
      (fsRec n m (a % m).toNat (b % m).toNat).1 ∧
    (fsRec n m (a % m).toNat (b % m).toNat).2 = euclidTrace m (a % m).toNat ∧
    (fsRec n m (a % m).toNat (b % m).toNat).2.length ≤ 2 * Nat.log 2 m + 1 := by
  obtain ⟨h1, h2⟩ := fsRec_spec m n (a % m).toNat (b % m).toNat
  refine ⟨by rw [h1, floorSumInt_normalize n m a b hm], h2, h2 ▸ euclidTrace_length m _ hm⟩

/-! ## The logarithmic bound is attained up to a constant (consecutive Fibonacci numbers) -/

theorem euclidTrace_fib (k : ℕ) :
    (euclidTrace (Nat.fib (k + 2)) (Nat.fib (k + 3))).length = k + 1 := by
  induction k with
  | zero =>
    rw [euclidTrace_pos _ (show 0 < Nat.fib 2 by decide), show Nat.fib 2 = 1 by decide, Nat.mod_one,
      euclidTrace_zero]
    rfl
  | succ k ih =>
    rw [euclidTrace_pos _ (Nat.fib_pos.2 (by omega))]
    have hlt : Nat.fib (k + 2) < Nat.fib (k + 3) := Nat.fib_lt_fib_succ (by omega)
    have e : Nat.fib (k + 1 + 3) % Nat.fib (k + 1 + 2) = Nat.fib (k + 2) := by
      rw [show k + 1 + 3 = (k + 2) + 2 by ring, Nat.fib_add_two, show k + 2 + 1 = k + 1 + 2 by ring,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by simpa using hlt)]
    rw [e, show k + 1 + 2 = k + 3 by ring, List.length_cons, ih]

theorem fib_le_two_pow (k : ℕ) : Nat.fib (k + 2) ≤ 2 ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · decide
    · decide
    · rw [show k + 2 + 2 = k + 2 + 2 by rfl, Nat.fib_add_two]
      have h1 := ih k (by omega)
      have h2 := ih (k + 1) (by omega)
      rw [show k + 1 + 2 = k + 2 + 1 by ring] at h2
      rw [pow_succ, pow_succ]
      rw [pow_succ] at h2
      omega

/-- Tightness: on the infinite family `m = F_{k+2}`, `a = F_{k+3}` the recursion makes `k + 1`
calls, which is at least `log₂ m + 1`.  So the number of calls is `Θ(log m)` in the worst case. -/
theorem fsRec_fib (n b k : ℕ) :
    (fsRec n (Nat.fib (k + 2)) (Nat.fib (k + 3)) b).2.length = k + 1 ∧
    Nat.log 2 (Nat.fib (k + 2)) + 1 ≤ k + 1 := by
  refine ⟨by rw [(fsRec_spec _ n _ b).2, euclidTrace_fib], ?_⟩
  have := Nat.log_mono_right (b := 2) (fib_le_two_pow k)
  rw [Nat.log_pow (by norm_num)] at this
  omega

/-! ## Main theorem -/

/-- **Conjecture 00000002139 (floor-sum Euclidean recursion).**  For all `n, a, b` and `m ≥ 1`:
(0) `floorSum` (with `ℕ` division) equals the genuine floor-sum `∑_{i<n} ⌊(a i+b)/m⌋`;
(1) the Euclid-like recursion `fsRec` returns `floorSum n m a b`;
(2) its call path (the (modulus, slope) pairs of its calls) is exactly the path of Euclid's
algorithm started at `(m, a)`, and the last modulus on it is `gcd(m, a)`;
(3) the number of calls is at most `2 log₂ m + 1` and at most `2 log₂ min(a, m) + 2`
(logarithmic, independent of `n` and `b`);
(4) the AtCoder loop `aclRec` also returns the floor-sum, its path is a prefix of the same Euclid
path, so it makes at most `2 log₂ m + 1` iterations.
Signed `a, b`: `floorSumInt_recursion`.  Tightness of the logarithmic order: `fsRec_fib`. -/
theorem floorSum_recursion_euclid (n m a b : ℕ) (hm : 0 < m) :
    (floorSum n m a b : ℤ) = floorSumInt n m a b ∧
    (fsRec n m a b).1 = floorSum n m a b ∧
    (fsRec n m a b).2 = euclidTrace m a ∧
    (euclidTrace m a).getLast?.map Prod.fst = some (Nat.gcd m a) ∧
    (fsRec n m a b).2.length ≤ 2 * Nat.log 2 m + 1 ∧
    (fsRec n m a b).2.length ≤ 2 * Nat.log 2 (min a m) + 2 ∧
    (aclRec n m a b).1 = floorSum n m a b ∧
    (aclRec n m a b).2 <+: euclidTrace m a ∧
    (aclRec n m a b).2.length ≤ 2 * Nat.log 2 m + 1 := by
  obtain ⟨h1, h2⟩ := fsRec_spec m n a b
  obtain ⟨h3, h4⟩ := aclRec_spec m n a b
  have hl := euclidTrace_length m a hm
  refine ⟨floorSum_cast n m a b, h1, h2, euclidTrace_last m a hm, h2 ▸ hl,
    h2 ▸ euclidTrace_length_min m a hm, h3, h4, le_trans h4.length_le hl⟩

end C2139
