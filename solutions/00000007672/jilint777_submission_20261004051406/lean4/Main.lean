/-!
# Conjecture 00000007672: gcd of q-Fibonacci polynomials

The q-Fibonacci polynomials are `F_n(q) = Σ_j [n-1-j choose j]_q q^{j²}`.
The conjecture claims that `gcd(F_n, F_m)` in `ℤ[q]` equals `F_{gcd(n,m)}`
times a correction factor.  We refute this for `(n, m) = (6, 3)`:
`F_3 = 1 + q` and `F_6 = 1 + q + q² + q³ + 2q⁴ + q⁵ + q⁶`, and `1` is a gcd of
`F_6` and `F_3` in `ℤ[q]`, but `1` is not a multiple of `F_3 = F_{gcd(6,3)}`.
We also refute it for `(n, m) = (11, 55)`, whose indices involve no prime
`≡ ±2 (mod 5)`: no divisor of `F_55` is a multiple of `F_11`
(`F_11(-1) = 3` does not divide `F_55(-1) = 121393`).

Polynomials in `ℤ[q]` are coefficient lists (constant term first).  Two lists
represent the same polynomial when all their coefficients agree (`PEq`), so
trailing zeros are harmless.  Divisibility in `ℤ[q]` is `Dvd`.
Gaussian binomials are defined by the q-Pascal rule and checked against the
product formula; `F_n` is built from them exactly as in the conjecture.
-/

namespace QFib

abbrev Poly := List Int

/-! ## Polynomial arithmetic on coefficient lists -/

def addL : Poly → Poly → Poly
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addL l m

def scale (a : Int) (l : Poly) : Poly := l.map (a * ·)

def mulL : Poly → Poly → Poly
  | [], _ => []
  | a :: l, m => addL (scale a m) (0 :: mulL l m)

/-- `q^k`. -/
def qpow (k : Nat) : Poly := List.replicate k 0 ++ [1]

def coeff (l : Poly) (k : Nat) : Int := l.getD k 0

/-- Same polynomial. -/
def PEq (a b : Poly) : Prop := ∀ k, coeff a k = coeff b k

/-- Divisibility in `ℤ[q]`. -/
def Dvd (a b : Poly) : Prop := ∃ c, PEq (mulL a c) b

/-- `G` is a greatest common divisor of `a` and `b` in `ℤ[q]`. -/
def IsGcd (G a b : Poly) : Prop :=
  Dvd G a ∧ Dvd G b ∧ ∀ D, Dvd D a → Dvd D b → Dvd D G

def evalL (x : Int) : Poly → Int
  | [] => 0
  | a :: l => a + x * evalL x l

/-! ## Basic lemmas -/

theorem coeff_nil (k : Nat) : coeff [] k = 0 := by simp [coeff]
theorem coeff_cons_zero (a : Int) (l : Poly) : coeff (a :: l) 0 = a := by simp [coeff]
theorem coeff_cons_succ (a : Int) (l : Poly) (k : Nat) :
    coeff (a :: l) (k + 1) = coeff l k := by simp [coeff]

theorem coeff_addL (l m : Poly) (k : Nat) :
    coeff (addL l m) k = coeff l k + coeff m k := by
  induction l generalizing m k with
  | nil => simp [addL, coeff_nil]
  | cons a l ih =>
    cases m with
    | nil => simp [addL, coeff_nil]
    | cons b m =>
      cases k with
      | zero => simp [addL, coeff_cons_zero]
      | succ k => simp [addL, coeff_cons_succ, ih]

theorem coeff_scale (a : Int) (l : Poly) (k : Nat) :
    coeff (scale a l) k = a * coeff l k := by
  induction l generalizing k with
  | nil => simp [scale, coeff_nil]
  | cons b l ih =>
    cases k with
    | zero => simp [scale, coeff_cons_zero]
    | succ k =>
      have := ih k
      simp only [scale] at this
      simp [scale, coeff_cons_succ, this]

theorem coeff_mulL_cons (a : Int) (l m : Poly) (k : Nat) :
    coeff (mulL (a :: l) m) k =
      a * coeff m k + (match k with | 0 => 0 | k + 1 => coeff (mulL l m) k) := by
  cases k with
  | zero => simp [mulL, coeff_addL, coeff_scale, coeff_cons_zero]
  | succ k => simp [mulL, coeff_addL, coeff_scale, coeff_cons_succ]

theorem evalL_addL (x : Int) (l m : Poly) :
    evalL x (addL l m) = evalL x l + evalL x m := by
  induction l generalizing m with
  | nil => simp [addL, evalL]
  | cons a l ih =>
    cases m with
    | nil => simp [addL, evalL]
    | cons b m =>
      simp only [addL, evalL, ih, Int.mul_add]
      omega

theorem evalL_scale (x a : Int) (l : Poly) : evalL x (scale a l) = a * evalL x l := by
  induction l with
  | nil => simp [scale, evalL]
  | cons b l ih =>
    simp only [scale] at ih
    simp only [scale, List.map, evalL, ih, Int.mul_add, Int.mul_left_comm]

theorem evalL_mulL (x : Int) (l m : Poly) :
    evalL x (mulL l m) = evalL x l * evalL x m := by
  induction l with
  | nil => simp [mulL, evalL]
  | cons a l ih =>
    simp only [mulL, evalL_addL, evalL_scale, evalL, ih, Int.add_mul, Int.mul_assoc]
    omega

theorem evalL_zero_of_coeffs (x : Int) (l : Poly) (h : ∀ k, coeff l k = 0) :
    evalL x l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : a = 0 := by have := h 0; rwa [coeff_cons_zero] at this
    have hl : evalL x l = 0 := ih fun k => by have := h (k + 1); rwa [coeff_cons_succ] at this
    simp [evalL, ha, hl]

/-- Equal coefficients give equal values. -/
theorem evalL_congr (x : Int) {a b : Poly} (h : PEq a b) : evalL x a = evalL x b := by
  induction a generalizing b with
  | nil =>
    rw [evalL_zero_of_coeffs x b (fun k => by rw [← h k, coeff_nil])]; rfl
  | cons a l ih =>
    cases b with
    | nil =>
      rw [evalL_zero_of_coeffs x (a :: l) (fun k => by rw [h k, coeff_nil])]; rfl
    | cons b m =>
      have h0 : a = b := by have := h 0; rwa [coeff_cons_zero, coeff_cons_zero] at this
      have ht : PEq l m := fun k => by
        have := h (k + 1); rwa [coeff_cons_succ, coeff_cons_succ] at this
      simp [evalL, h0, ih ht]

theorem evalL_zero (l : Poly) : evalL 0 l = coeff l 0 := by
  cases l with
  | nil => rfl
  | cons a l => simp [evalL, coeff_cons_zero]

/-- Multiplying by a constant. -/
theorem coeff_mulL_const (l : Poly) (e : Int) (k : Nat) :
    coeff (mulL l [e]) k = coeff l k * e := by
  induction l generalizing k with
  | nil => simp [mulL, coeff_nil]
  | cons a l ih =>
    rw [coeff_mulL_cons]
    cases k with
    | zero => simp [coeff_cons_zero, Int.mul_comm]
    | succ k => simp [coeff_cons_succ, coeff_nil, ih]

/-- A polynomial with all coefficients zero has a zero product. -/
theorem coeff_mulL_of_zero (l m : Poly) (h : ∀ k, coeff l k = 0) (k : Nat) :
    coeff (mulL l m) k = 0 := by
  induction l generalizing k with
  | nil => simp [mulL, coeff_nil]
  | cons a l ih =>
    have ha : a = 0 := by have := h 0; rwa [coeff_cons_zero] at this
    have hl : ∀ k, coeff l k = 0 := fun k => by
      have := h (k + 1); rwa [coeff_cons_succ] at this
    rw [coeff_mulL_cons, ha]
    cases k with
    | zero => simp
    | succ k => simp [ih hl k]

/-- The top coefficient of a product is the product of the top coefficients. -/
theorem coeff_mulL_top (l m : Poly) (i j : Nat)
    (hi : ∀ k, i < k → coeff l k = 0) (hj : ∀ k, j < k → coeff m k = 0) :
    coeff (mulL l m) (i + j) = coeff l i * coeff m j := by
  induction l generalizing i with
  | nil => simp [mulL, coeff_nil]
  | cons a l ih =>
    rw [coeff_mulL_cons]
    cases i with
    | zero =>
      have hl : ∀ k, coeff l k = 0 := fun k => by
        have := hi (k + 1) (by omega); rwa [coeff_cons_succ] at this
      cases j with
      | zero => simp [coeff_cons_zero]
      | succ j =>
        simp only [Nat.zero_add, coeff_cons_zero]
        rw [coeff_mulL_of_zero l m hl]; omega
    | succ i =>
      have hA : coeff m (i + 1 + j) = 0 := hj _ (by omega)
      have hl : ∀ k, i < k → coeff l k = 0 := fun k hk => by
        have := hi (k + 1) (by omega); rwa [coeff_cons_succ] at this
      rw [show i + 1 + j = (i + j) + 1 by omega]
      simp only [coeff_cons_succ]
      rw [show i + j + 1 = i + 1 + j by omega, hA, ih i hl]
      simp

theorem coeff_of_length_le (l : Poly) (k : Nat) (h : l.length ≤ k) : coeff l k = 0 := by
  have : l[k]? = none := List.getElem?_eq_none_iff.mpr h
  simp [coeff, this]

/-- A nonzero coefficient beyond degree 0 can be pushed up to the top one. -/
theorem exists_top (l : Poly) :
    ∀ n i, 1 ≤ i → coeff l i ≠ 0 → l.length ≤ i + n →
      ∃ t, 1 ≤ t ∧ coeff l t ≠ 0 ∧ ∀ k, t < k → coeff l k = 0 := by
  intro n
  induction n with
  | zero => intro i _ hi hlen; exact absurd (coeff_of_length_le l i (by omega)) hi
  | succ n ih =>
    intro i h1 hi hlen
    by_cases hall : ∀ k, i < k → coeff l k = 0
    · exact ⟨i, h1, hi, hall⟩
    · have : ∃ k, i < k ∧ coeff l k ≠ 0 := by
        apply Classical.byContradiction
        intro hne
        exact hall fun k hk => Classical.byContradiction fun hk' => hne ⟨k, hk, hk'⟩
      obtain ⟨k, hik, hk⟩ := this
      exact ih k (by omega) hk (by omega)

/-- `Const l`: all coefficients of degree ≥ 1 vanish. -/
def Const (l : Poly) : Prop := ∀ k, 1 ≤ k → coeff l k = 0

/-- If `l * m` has degree at most 1, then `l` or `m` is constant. -/
theorem const_or_const (l m : Poly) (h : ∀ k, 2 ≤ k → coeff (mulL l m) k = 0) :
    Const l ∨ Const m := by
  apply Classical.byContradiction
  intro hn
  have hl : ¬ Const l := fun c => hn (Or.inl c)
  have hm : ¬ Const m := fun c => hn (Or.inr c)
  have gl : ∃ i, 1 ≤ i ∧ coeff l i ≠ 0 := Classical.byContradiction fun hc =>
    hl fun k hk => Classical.byContradiction fun hk' => hc ⟨k, hk, hk'⟩
  have gm : ∃ j, 1 ≤ j ∧ coeff m j ≠ 0 := Classical.byContradiction fun hc =>
    hm fun k hk => Classical.byContradiction fun hk' => hc ⟨k, hk, hk'⟩
  obtain ⟨i0, hi0, hci0⟩ := gl
  obtain ⟨j0, hj0, hcj0⟩ := gm
  obtain ⟨i, hi1, hci, hitop⟩ := exists_top l l.length i0 hi0 hci0 (by omega)
  obtain ⟨j, hj1, hcj, hjtop⟩ := exists_top m m.length j0 hj0 hcj0 (by omega)
  have htop := coeff_mulL_top l m i j hitop hjtop
  rw [h (i + j) (by omega)] at htop
  exact (Int.mul_eq_zero.mp htop.symm).elim hci hcj

/-! ## Gaussian binomials and q-Fibonacci polynomials -/

/-- Gaussian binomial `[n choose k]_q` by the q-Pascal rule
`[n+1, k+1] = [n, k] + q^{k+1} [n, k+1]`. -/
def gauss : Nat → Nat → Poly
  | _, 0 => [1]
  | 0, _ + 1 => []
  | n + 1, k + 1 => addL (gauss n k) (mulL (qpow (k + 1)) (gauss n (k + 1)))

def sumL (ps : List Poly) : Poly := ps.foldr addL []

/-- `F_n(q) = Σ_{j=0}^{n-1} [n-1-j choose j]_q q^{j²}` (terms with `j > n-1-j` vanish). -/
def qfib (n : Nat) : Poly :=
  sumL ((List.range n).map fun j => mulL (gauss (n - 1 - j) j) (qpow (j * j)))

/-- Drop trailing zeros (used only for readable `decide` checks). -/
def trim (l : Poly) : Poly := (l.reverse.dropWhile (· == 0)).reverse

/-- `(q;q)_n = (1-q)(1-q²)⋯(1-qⁿ)`. -/
def qfact : Nat → Poly
  | 0 => [1]
  | n + 1 => mulL (qfact n) (addL [1] (scale (-1) (qpow (n + 1))))

/-- Sanity check: the q-Pascal definition agrees with the product formula
`[n choose k]_q (q;q)_k (q;q)_{n-k} = (q;q)_n` for all `k ≤ n ≤ 7`. -/
theorem gauss_product_formula :
    ∀ n, n ≤ 7 → ∀ k, k ≤ n →
      trim (mulL (mulL (gauss n k) (qfact k)) (qfact (n - k))) = trim (qfact n) := by
  decide

set_option maxRecDepth 100000 in
/-- Sanity check: `F_n(1)` is the Fibonacci number `1, 1, 2, 3, 5, …`. -/
theorem qfib_at_one :
    (List.range 15).map (fun n => evalL 1 (qfib (n + 1))) =
      [1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610] := by
  decide

theorem qfib_3 : trim (qfib 3) = [1, 1] := by decide
theorem qfib_6 : trim (qfib 6) = [1, 1, 1, 1, 2, 1, 1] := by decide

theorem qfib_3_coeffs : ∀ k, 2 ≤ k → coeff (qfib 3) k = 0 := by
  intro k hk
  have hlen : (qfib 3).length = 3 := by decide
  by_cases h2 : k = 2
  · subst h2; decide
  · exact coeff_of_length_le _ _ (by omega)

theorem qfib_3_at_neg_one : evalL (-1) (qfib 3) = 0 := by decide
theorem qfib_3_at_zero : evalL 0 (qfib 3) = 1 := by decide
theorem qfib_6_at_neg_one : evalL (-1) (qfib 6) = 2 := by decide

theorem gcd_6_3 : Nat.gcd 6 3 = 3 := by decide

/-- `F_3 = 1 + q` divides none of `F_6, F_9, …, F_18`, since `F_{3k}(-1) ≠ 0`. -/
theorem qfib_mult3_at_neg_one :
    (List.range 5).map (fun k => evalL (-1) (qfib (3 * (k + 2)))) = [2, 2, 8, 8, 34] := by
  decide +kernel

/-! ## `1` is a gcd of `F_6` and `F_3` in `ℤ[q]` -/

theorem one_mul_peq (m : Poly) : PEq (mulL [1] m) m := fun k => by
  rw [coeff_mulL_cons]; cases k <;> simp [mulL, coeff_nil]

/-- Every common divisor of `F_6` and `F_3` divides `1`. -/
theorem common_divisor_dvd_one (D : Poly)
    (h6 : Dvd D (qfib 6)) (h3 : Dvd D (qfib 3)) : Dvd D [1] := by
  obtain ⟨B, hB⟩ := h6
  obtain ⟨A, hA⟩ := h3
  have hdeg : ∀ k, 2 ≤ k → coeff (mulL D A) k = 0 := fun k hk => by
    rw [hA k]; exact qfib_3_coeffs k hk
  -- evaluations of `D * A = F_3` and `D * B = F_6`
  have e0 := evalL_congr 0 hA
  have e1 := evalL_congr (-1) hA
  have e6 := evalL_congr (-1) hB
  rw [evalL_mulL, qfib_3_at_zero] at e0
  rw [evalL_mulL, qfib_3_at_neg_one] at e1
  rw [evalL_mulL, qfib_6_at_neg_one] at e6
  rcases const_or_const D A hdeg with hD | hA'
  · -- `D` is a constant `d` with `d * A(0) = 1`, so `d = ±1` and `D * [d] = 1`.
    refine ⟨[coeff D 0], fun k => ?_⟩
    rw [coeff_mulL_const]
    rw [evalL_zero, evalL_zero] at e0
    have hd : coeff D 0 * coeff D 0 = 1 := by
      have h1 : (coeff D 0).natAbs * (coeff A 0).natAbs = 1 := by
        rw [← Int.natAbs_mul, e0]; rfl
      have h2 : (coeff D 0).natAbs = 1 := Nat.eq_one_of_dvd_one ⟨_, h1.symm⟩
      rw [← Int.natAbs_mul_self' (coeff D 0), h2]; rfl
    cases k with
    | zero => simp [coeff_cons_zero, hd]
    | succ k => simp [coeff_cons_succ, coeff_nil, hD (k + 1) (by omega)]
  · -- `A` is a constant `a ≠ 0`, so `D(-1) = 0`, contradicting `D(-1) * B(-1) = 2`.
    exfalso
    have hAc : ∀ x, evalL x A = coeff A 0 := by
      intro x
      have : PEq A [coeff A 0] := fun k => by
        cases k with
        | zero => simp [coeff_cons_zero]
        | succ k => simp [coeff_cons_succ, coeff_nil, hA' (k + 1) (by omega)]
      rw [evalL_congr x this]; simp [evalL]
    rw [hAc] at e0 e1
    have ha : coeff A 0 ≠ 0 := fun h => by rw [h, Int.mul_zero] at e0; exact absurd e0 (by decide)
    have hD : evalL (-1) D = 0 := (Int.mul_eq_zero.mp e1).resolve_right ha
    rw [hD, Int.zero_mul] at e6
    exact absurd e6 (by decide)

theorem isGcd_one : IsGcd [1] (qfib 6) (qfib 3) :=
  ⟨⟨qfib 6, one_mul_peq _⟩, ⟨qfib 3, one_mul_peq _⟩, common_divisor_dvd_one⟩

/-! ## Fast evaluation of `F_n` at an integer

To evaluate `F_55` without expanding it, we evaluate the Gaussian binomials
row by row (q-Pascal at `q = x`) and prove that this agrees with `evalL x`. -/

theorem evalL_qpow (x : Int) (k : Nat) : evalL x (qpow k) = x ^ k := by
  induction k with
  | zero => simp [qpow, evalL]
  | succ k ih =>
    have : qpow (k + 1) = 0 :: qpow k := by simp [qpow, List.replicate_succ]
    rw [this]; simp only [evalL, ih, Int.pow_succ]
    rw [Int.mul_comm]; omega

theorem evalL_gauss_zero (x : Int) (n : Nat) : evalL x (gauss n 0) = 1 := by
  cases n <;> simp [gauss, evalL]

theorem evalL_gauss_succ (x : Int) (n k : Nat) :
    evalL x (gauss (n + 1) (k + 1)) =
      evalL x (gauss n k) + x ^ (k + 1) * evalL x (gauss n (k + 1)) := by
  simp only [gauss, evalL_addL, evalL_mulL, evalL_qpow]

theorem evalL_gauss_gt (x : Int) : ∀ n k, n < k → evalL x (gauss n k) = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    cases k with
    | zero => omega
    | succ k => simp [gauss, evalL]
  | succ n ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k =>
      rw [evalL_gauss_succ, ih k (by omega), ih (k + 1) (by omega)]
      simp

/-- One q-Pascal step on a row of values `[g(n,0), …, g(n,n)]`. -/
def rowStep (x : Int) (r : List Int) : List Int :=
  1 :: (List.range r.length).map fun k => r.getD k 0 + x ^ (k + 1) * r.getD (k + 1) 0

/-- `row x n = [g(n,0), …, g(n,n)]` with `g(n,k) = [n choose k]_q` at `q = x`. -/
def row (x : Int) : Nat → List Int
  | 0 => [1]
  | n + 1 => rowStep x (row x n)

theorem row_length (x : Int) (n : Nat) : (row x n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [row, rowStep, ih]

theorem row_spec (x : Int) : ∀ n k, (row x n).getD k 0 = evalL x (gauss n k) := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k with
    | zero => simp [row, gauss, evalL]
    | succ k => simp [row, gauss, evalL]
  | succ n ih =>
    intro k
    cases k with
    | zero => simp [row, rowStep, evalL_gauss_zero]
    | succ k =>
      rw [evalL_gauss_succ, ← ih k, ← ih (k + 1)]
      by_cases hk : k < n + 1
      · simp [row, rowStep, row_length, hk]
      · have h1 : (row x n).getD k 0 = 0 := by
          rw [ih k]; exact evalL_gauss_gt x n k (by omega)
        have h2 : (row x n).getD (k + 1) 0 = 0 := by
          rw [ih (k + 1)]; exact evalL_gauss_gt x n (k + 1) (by omega)
        rw [h1, h2]
        have hr : (List.range (n + 1))[k]? = none :=
          List.getElem?_eq_none_iff.mpr (by rw [List.length_range]; omega)
        simp [row, rowStep, row_length, hr]

/-- `F_n(x)` computed from the rows. -/
def fastF (x : Int) (n : Nat) : Int :=
  ((List.range n).map fun j => (row x (n - 1 - j)).getD j 0 * x ^ (j * j)).foldr (· + ·) 0

theorem evalL_sum_map (x : Int) (l : List Nat) (f : Nat → Poly) (g : Nat → Int)
    (h : ∀ j, evalL x (f j) = g j) :
    evalL x ((l.map f).foldr addL []) = (l.map g).foldr (· + ·) 0 := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [List.map, List.foldr, evalL_addL, ih, h]

theorem evalL_qfib (x : Int) (n : Nat) : evalL x (qfib n) = fastF x n := by
  unfold qfib sumL fastF
  apply evalL_sum_map
  intro j
  rw [evalL_mulL, evalL_qpow, row_spec]

theorem qfib_11_at_neg_one : evalL (-1) (qfib 11) = 3 := by
  rw [evalL_qfib]; decide

/-- Checked by kernel reduction (`decide +kernel`). -/
theorem qfib_55_at_neg_one : evalL (-1) (qfib 55) = 121393 := by
  rw [evalL_qfib]; decide +kernel

theorem gcd_11_55 : Nat.gcd 11 55 = 11 := by decide

/-- No divisor of `F_55` in `ℤ[q]` is a multiple of `F_11 = F_{gcd(11,55)}`:
`F_11(-1) = 3` does not divide `F_55(-1) = 121393`. -/
theorem no_divisor_of_F55_is_multiple_of_F11 (G c : Poly)
    (hG : Dvd G (qfib 55)) (hc : PEq G (mulL (qfib 11) c)) : False := by
  obtain ⟨B, hB⟩ := hG
  have e55 := evalL_congr (-1) hB
  have eG := evalL_congr (-1) hc
  rw [evalL_mulL, qfib_55_at_neg_one] at e55
  rw [evalL_mulL, qfib_11_at_neg_one] at eG
  rw [eG, Int.mul_assoc] at e55
  generalize evalL (-1) c * evalL (-1) B = t at e55
  omega

/-! ## The conjecture's gcd clause and its refutation -/

/-- No divisor of `F_6` in `ℤ[q]` is a multiple of `F_3 = F_{gcd(6,3)}`. -/
theorem no_divisor_of_F6_is_multiple_of_F3 (G c : Poly)
    (hG : Dvd G (qfib 6)) (hc : PEq G (mulL (qfib 3) c)) : False := by
  obtain ⟨B, hB⟩ := hG
  have e6 := evalL_congr (-1) hB
  have eG := evalL_congr (-1) hc
  rw [evalL_mulL, qfib_6_at_neg_one] at e6
  rw [evalL_mulL, qfib_3_at_neg_one, Int.zero_mul] at eG
  rw [eG, Int.zero_mul] at e6
  exact absurd e6 (by decide)

/-- The gcd clause: for all `n, m ≥ 1`, every gcd of `F_n` and `F_m` in `ℤ[q]` is
`F_{gcd(n,m)}` times some polynomial (the "correction factor"). -/
def GcdClause : Prop :=
  ∀ n m G, 1 ≤ n → 1 ≤ m → IsGcd G (qfib n) (qfib m) →
    ∃ c, PEq G (mulL (qfib (Nat.gcd n m)) c)

theorem conjecture_00000007672_false : ¬ GcdClause := by
  intro h
  obtain ⟨c, hc⟩ := h 6 3 [1] (by decide) (by decide) isGcd_one
  rw [gcd_6_3] at hc
  exact no_divisor_of_F6_is_multiple_of_F3 [1] c isGcd_one.1 hc

/-- The clause read existentially: "a gcd of `F_n` and `F_m` equals
`F_{gcd(n,m)} · c`" (in `ℤ[q]` a gcd exists and is unique up to sign). -/
def GcdClauseExists : Prop :=
  ∀ n m, 1 ≤ n → 1 ≤ m → ∃ G c, IsGcd G (qfib n) (qfib m) ∧
    PEq G (mulL (qfib (Nat.gcd n m)) c)

/-- The existential form also fails for `(6, 3)`. -/
theorem conjecture_00000007672_false_exists_6_3 : ¬ GcdClauseExists := by
  intro h
  obtain ⟨G, c, hG, hc⟩ := h 6 3 (by decide) (by decide)
  rw [gcd_6_3] at hc
  exact no_divisor_of_F6_is_multiple_of_F3 G c hG.1 hc

/-- Refutation with `(n, m) = (11, 55)`: all prime factors of `11, 55` are
`5` or `11`, none `≡ ±2 (mod 5)`; moreover `F_11` has no cyclotomic factor
(checked in `verify.py`, not used here). -/
theorem conjecture_00000007672_false_11_55 : ¬ GcdClauseExists := by
  intro h
  obtain ⟨G, c, hG, hc⟩ := h 11 55 (by decide) (by decide)
  rw [gcd_11_55] at hc
  exact no_divisor_of_F55_is_multiple_of_F11 G c hG.2.1 hc

end QFib

#print axioms QFib.gauss_product_formula
#print axioms QFib.qfib_at_one
#print axioms QFib.qfib_6
#print axioms QFib.qfib_mult3_at_neg_one
#print axioms QFib.common_divisor_dvd_one
#print axioms QFib.isGcd_one
#print axioms QFib.no_divisor_of_F6_is_multiple_of_F3
#print axioms QFib.conjecture_00000007672_false
#print axioms QFib.qfib_55_at_neg_one
#print axioms QFib.no_divisor_of_F55_is_multiple_of_F11
#print axioms QFib.conjecture_00000007672_false_exists_6_3
#print axioms QFib.conjecture_00000007672_false_11_55
