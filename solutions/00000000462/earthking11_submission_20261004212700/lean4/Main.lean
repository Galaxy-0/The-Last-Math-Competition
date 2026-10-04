/-
  Disproof of conjecture `00000000462`: formalisation.

  Conjecture (as filed):
    "τ(circulant C_n(1,2)) satisfies a linear recurrence whose largest real
     characteristic root tends to α², where α = 2+√3."

  Refutation.  Let τ(n) be the number of spanning trees of the circulant graph
  C_n(1,2) (the square of the n-cycle).  The matrix-tree theorem and the
  unit-root product give the exact closed form

      τ(n) = n·(L(2n) + 2·(−1)^(n+1)) / 5,

  where L is the Lucas sequence.  Writing u(n) = L(2n) + 2·(−1)^(n+1), the
  sequence u satisfies the three-term recurrence

      u(n+3) = 2·u(n+2) + 2·u(n+1) − u(n),

  whose characteristic polynomial factors as

      x³ − 2x² − 2x + 1 = (x + 1)(x² − 3x + 1).

  Since τ(n) = n·u(n)/5, the sequence τ satisfies the six-term recurrence with
  characteristic polynomial

      p(x) = (x³ − 2x² − 2x + 1)² = x⁶ − 4x⁵ + 10x³ − 4x + 1
           = (x + 1)²(x² − 3x + 1)².

  Its largest real root is (3+√5)/2 = 2.6180339887…, from the factor
  x² − 3x + 1.  The conjectured value α² = (2+√3)² = 7 + 4√3 = 13.9282032302…
  is **not** a root: the computation below shows

      p(7 + 4√3) = 2615536 + 1510080·√3 ≠ 0

  in ℤ[√3] ≅ ℤ[t]/(t²−3).  Hence α² is not a characteristic root of the
  recurrence satisfied by τ, and the conjecture is false.

  Core Lean only (`import Std`); no Mathlib, no `ring`, no `sorry`.
-/

import Std

namespace Tlmc462

/-! ## Lucas numbers -/

/-- Lucas numbers: `L 0 = 2`, `L 1 = 1`, `L (n+2) = L (n+1) + L n`. -/
def L : Nat → Nat
  | 0 => 2
  | 1 => 1
  | n + 2 => L (n + 1) + L n

/-- The defining recurrence of the Lucas numbers. -/
theorem L_rec (n : Nat) : L (n + 2) = L (n + 1) + L n := rfl

/-- Even-index Lucas numbers, `M n = L (2n)`. -/
def M (n : Nat) : Int := (L (2 * n) : Int)

/-- The four-step Lucas identity `L (m+4) + L m = 3·L (m+2)`. -/
theorem L_add_four (m : Nat) :
    (L (m + 4) : Int) + (L m : Int) = 3 * (L (m + 2) : Int) := by
  have e1 : L (m + 4) = L (m + 3) + L (m + 2) := by
    have h : m + 4 = (m + 2) + 2 := by omega
    rw [h]; rfl
  have e2 : L (m + 3) = L (m + 2) + L (m + 1) := by
    have h : m + 3 = (m + 1) + 2 := by omega
    rw [h]; rfl
  have e3 : L (m + 2) = L (m + 1) + L m := rfl
  rw [e1, e2, e3]
  simp only [Int.natCast_add]
  omega

/-- `M n = L (2n)` satisfies `M (n+2) = 3 M (n+1) − M n`; the characteristic
polynomial of `M` is `x² − 3x + 1`. -/
theorem M_rec (n : Nat) : M (n + 2) = 3 * M (n + 1) - M n := by
  have h := L_add_four (2 * n)
  have h4 : 2 * (n + 2) = 2 * n + 4 := by omega
  have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
  show (L (2 * (n + 2)) : Int) = 3 * (L (2 * (n + 1)) : Int) - (L (2 * n) : Int)
  rw [h4, h2]
  omega

/-! ## The sign sequence and the sequence `u` -/

/-- The sign sequence `s n = (−1)^(n+1)`, defined so that the shift rule is
definitional: `s 0 = −1`, `s (n+1) = −s n`. -/
def s : Nat → Int
  | 0 => -1
  | n + 1 => -s n

theorem s_succ (n : Nat) : s (n + 1) = -s n := rfl

theorem s_add_two (n : Nat) : s (n + 2) = s n := by
  show -s (n + 1) = s n
  rw [s_succ]
  exact Int.neg_neg (s n)

/-- `u n = L(2n) + 2(−1)^(n+1)`; then `τ(n) = n·u(n)/5`. -/
def u (n : Nat) : Int := M n + 2 * s n

/-- The sequence `u` satisfies `u(n+3) = 2u(n+2) + 2u(n+1) − u(n)`, i.e. its
characteristic polynomial is `x³ − 2x² − 2x + 1`. -/
theorem u_rec (n : Nat) : u (n + 3) = 2 * u (n + 2) + 2 * u (n + 1) - u n := by
  have hs1 : s (n + 1) = -s n := s_succ n
  have hs2 : s (n + 2) = s n := s_add_two n
  have hs3 : s (n + 3) = -s n := by
    have h : s (n + 3) = s (n + 1) := s_add_two (n + 1)
    rw [h, s_succ]
  have hM : M (n + 3) = 3 * M (n + 2) - M (n + 1) := by
    rw [show n + 3 = (n + 1) + 2 from by omega]
    exact M_rec (n + 1)
  show M (n + 3) + 2 * s (n + 3)
      = 2 * (M (n + 2) + 2 * s (n + 2)) + 2 * (M (n + 1) + 2 * s (n + 1))
        - (M n + 2 * s n)
  rw [hs1, hs2, hs3, hM, M_rec n]
  omega

/-! ## Iterated forms and the two vanishing parts -/

theorem u3 (n : Nat) : u (n + 3) = 2 * u (n + 2) + 2 * u (n + 1) - u n := u_rec n

theorem u4 (n : Nat) : u (n + 4) = 6 * u (n + 2) + 3 * u (n + 1) - 2 * u n := by
  have h := u_rec (n + 1)
  rw [show n + 1 + 3 = n + 4 from by omega,
      show n + 1 + 2 = n + 3 from by omega,
      show n + 1 + 1 = n + 2 from by omega] at h
  rw [h, u_rec n]
  omega

theorem u5 (n : Nat) : u (n + 5) = 15 * u (n + 2) + 10 * u (n + 1) - 6 * u n := by
  have h := u_rec (n + 2)
  rw [show n + 2 + 3 = n + 5 from by omega,
      show n + 2 + 2 = n + 4 from by omega,
      show n + 2 + 1 = n + 3 from by omega] at h
  rw [h, u4 n, u3 n]
  omega

theorem u6 (n : Nat) : u (n + 6) = 40 * u (n + 2) + 24 * u (n + 1) - 15 * u n := by
  have h := u_rec (n + 3)
  rw [show n + 3 + 3 = n + 6 from by omega,
      show n + 3 + 2 = n + 5 from by omega,
      show n + 3 + 1 = n + 4 from by omega] at h
  rw [h, u5 n, u4 n, u3 n]
  omega

/-- The pure six-term operator applied to `u` vanishes (this is `p(E)²u = 0`). -/
theorem P_zero (n : Nat) :
    u (n + 6) - 4 * u (n + 5) + 10 * u (n + 3) - 4 * u (n + 1) + u n = 0 := by
  rw [u6 n, u5 n, u3 n]
  omega

/-- The correction produced by the factor `n` in `τ(n) = n·u(n)/5` vanishes. -/
theorem Q_zero (n : Nat) :
    6 * u (n + 6) - 20 * u (n + 5) + 30 * u (n + 3) - 4 * u (n + 1) = 0 := by
  rw [u6 n, u5 n, u3 n]
  omega

/-! ## The six-term recurrence for `c n = n·u(n) = 5·τ(n)` -/

/-- `c n = n·u(n) = 5·τ(n)`. -/
def c (n : Nat) : Int := (n : Int) * u n

/-- `c n = n·u(n)` satisfies the six-term linear recurrence whose
characteristic polynomial is `p(x) = x⁶ − 4x⁵ + 10x³ − 4x + 1`. -/
theorem c_rec (n : Nat) :
    c (n + 6) = 4 * c (n + 5) - 10 * c (n + 3) + 4 * c (n + 1) - c n := by
  have key :
      c (n + 6) - 4 * c (n + 5) + 10 * c (n + 3) - 4 * c (n + 1) + c n = 0 := by
    have split :
        c (n + 6) - 4 * c (n + 5) + 10 * c (n + 3) - 4 * c (n + 1) + c n
          = (n : Int) * (u (n + 6) - 4 * u (n + 5) + 10 * u (n + 3) - 4 * u (n + 1) + u n)
            + (6 * u (n + 6) - 20 * u (n + 5) + 30 * u (n + 3) - 4 * u (n + 1)) := by
      show ((n + 6 : Nat) : Int) * u (n + 6) - 4 * (((n + 5 : Nat) : Int) * u (n + 5))
          + 10 * (((n + 3 : Nat) : Int) * u (n + 3)) - 4 * (((n + 1 : Nat) : Int) * u (n + 1))
          + (n : Int) * u n
        = (n : Int) * (u (n + 6) - 4 * u (n + 5) + 10 * u (n + 3) - 4 * u (n + 1) + u n)
          + (6 * u (n + 6) - 20 * u (n + 5) + 30 * u (n + 3) - 4 * u (n + 1))
      rw [Int.natCast_add n 6, Int.natCast_add n 5, Int.natCast_add n 3, Int.natCast_add n 1]
      rw [Int.add_mul, Int.add_mul, Int.add_mul, Int.add_mul]
      simp only [Int.mul_add, Int.mul_sub, Int.mul_left_comm]
      omega
    rw [split, P_zero n, Q_zero n]
    omega
  omega

/-! ## Integrality and the spanning-tree sequence `τ` -/

/-- `5` divides every `u n`: the base cases are `u 0 = 0`, `u 1 = 5`, `u 2 = 5`,
and the three-term recurrence propagates divisibility. -/
theorem five_dvd_u : ∀ n : Nat, (5 : Int) ∣ u n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => exact ⟨0, by decide⟩
    | 1 => exact ⟨1, by decide⟩
    | 2 => exact ⟨1, by decide⟩
    | k + 3 =>
      have h := u_rec k
      obtain ⟨a, ha⟩ := ih (k + 2) (by omega)
      obtain ⟨b, hb⟩ := ih (k + 1) (by omega)
      obtain ⟨d, hd⟩ := ih k (by omega)
      refine ⟨2 * a + 2 * b - d, ?_⟩
      rw [h, ha, hb, hd]
      omega

/-- `5` divides `c n = n·u(n)`. -/
theorem five_dvd_c (n : Nat) : (5 : Int) ∣ c n := by
  obtain ⟨a, ha⟩ := five_dvd_u n
  refine ⟨(n : Int) * a, ?_⟩
  unfold c
  rw [ha, ← Int.mul_assoc, Int.mul_comm (n : Int) 5, Int.mul_assoc]

/-- The number of spanning trees of the circulant graph `C_n(1,2)`, in the
exact closed form `τ(n) = n·(L(2n) + 2(−1)^(n+1))/5`. -/
def tau (n : Nat) : Int := c n / 5

/-- `5·τ(n) = c n`. -/
theorem five_mul_tau (n : Nat) : 5 * tau n = c n := by
  unfold tau
  exact Int.mul_ediv_cancel' (five_dvd_c n)

/-- The spanning-tree counts satisfy the six-term recurrence with
characteristic polynomial `p(x) = x⁶ − 4x⁵ + 10x³ − 4x + 1`. -/
theorem tau_rec (n : Nat) :
    tau (n + 6) = 4 * tau (n + 5) - 10 * tau (n + 3) + 4 * tau (n + 1) - tau n := by
  have h6 := five_mul_tau (n + 6)
  have h5 := five_mul_tau (n + 5)
  have h3 := five_mul_tau (n + 3)
  have h1 := five_mul_tau (n + 1)
  have h0 := five_mul_tau n
  have hr := c_rec n
  omega

/-! ## The known spanning-tree counts (initial values) -/

theorem tau_5 : tau 5 = 125 := by decide
theorem tau_6 : tau 6 = 384 := by decide
theorem tau_7 : tau 7 = 1183 := by decide
theorem tau_8 : tau 8 = 3528 := by decide
theorem tau_9 : tau 9 = 10404 := by decide
theorem tau_10 : tau 10 = 30250 := by decide
theorem tau_11 : tau 11 = 87131 := by decide
theorem tau_12 : tau 12 = 248832 := by decide

/-! ## Coefficients: the factorisation of the characteristic polynomial

Polynomials are coefficient lists in ascending order.  We verify
`x⁶ − 4x⁵ + 10x³ − 4x + 1 = (x+1)²(x²−3x+1)²`. -/

/-- Addition of coefficient lists. -/
def padd : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => (a + b) :: padd as bs

/-- Multiplication of coefficient lists. -/
def pmul : List Int → List Int → List Int
  | [], _ => []
  | a :: as, q => padd (q.map (fun b => a * b)) (0 :: pmul as q)

/-- `x³ − 2x² − 2x + 1 = (x + 1)(x² − 3x + 1)`. -/
theorem char_factor :
    pmul ([1, 1] : List Int) ([1, -3, 1] : List Int) = ([1, -2, -2, 1] : List Int) := by
  decide

/-- `(x³ − 2x² − 2x + 1)² = x⁶ − 4x⁵ + 10x³ − 4x + 1`. -/
theorem char_square :
    pmul ([1, -2, -2, 1] : List Int) ([1, -2, -2, 1] : List Int)
      = ([1, -4, 0, 10, 0, -4, 1] : List Int) := by
  decide

/-! ## The algebraic obstruction in `ℤ[√3]`

`ZS3` models `ℤ[√3] ≅ ℤ[t]/(t²−3)` as pairs `(a,b) ↔ a + b√3`.  It embeds in
`ℝ` via `t ↦ √3`, so a nonzero element here is a nonzero real number. -/

/-- The ring `ℤ[√3]`, as pairs `(re, im) ↔ re + im·√3`. -/
structure ZS3 where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace ZS3

def zero : ZS3 := ⟨0, 0⟩
def one : ZS3 := ⟨1, 0⟩
def add (x y : ZS3) : ZS3 := ⟨x.re + y.re, x.im + y.im⟩
def sub (x y : ZS3) : ZS3 := ⟨x.re - y.re, x.im - y.im⟩
def scale (k : Int) (x : ZS3) : ZS3 := ⟨k * x.re, k * x.im⟩
def mul (x y : ZS3) : ZS3 := ⟨x.re * y.re + 3 * x.im * y.im, x.re * y.im + x.im * y.re⟩

def pow (x : ZS3) : Nat → ZS3
  | 0 => one
  | n + 1 => mul (pow x n) x

end ZS3

/-- `α = 2 + √3`. -/
def alpha : ZS3 := ⟨2, 1⟩

/-- `α² = (2+√3)² = 7 + 4√3`. -/
theorem alpha_sq : ZS3.mul alpha alpha = (⟨7, 4⟩ : ZS3) := by decide

/-- `α⁴ − 3α² + 1 = 77 + 44√3`, the value of `x² − 3x + 1` at `x = α²`. -/
theorem alpha_sq_factor :
    ZS3.add (ZS3.sub (ZS3.pow (ZS3.mul alpha alpha) 2) (ZS3.scale 3 (ZS3.mul alpha alpha)))
        ZS3.one
      = (⟨77, 44⟩ : ZS3) := by decide

/-- The characteristic polynomial `p(x) = x⁶ − 4x⁵ + 10x³ − 4x + 1` evaluated
at a point of `ℤ[√3]`. -/
def pEval (x : ZS3) : ZS3 :=
  ZS3.add
    (ZS3.add
      (ZS3.sub (ZS3.pow x 6) (ZS3.scale 4 (ZS3.pow x 5)))
      (ZS3.scale 10 (ZS3.pow x 3)))
    (ZS3.add (ZS3.scale (-4) x) ZS3.one)

/-- **The algebraic heart of the refutation.**  `p(α²) = 2615536 + 1510080√3`,
which is nonzero in `ℤ[√3]`.  Therefore `α²` is not a root of the
characteristic polynomial of the recurrence satisfied by `τ`. -/
theorem pEval_alpha_sq :
    pEval (ZS3.mul alpha alpha) = (⟨2615536, 1510080⟩ : ZS3) := by decide

/-- `α² ≠ −1`, the other real root of the characteristic polynomial. -/
theorem alpha_sq_ne_neg_one : ZS3.mul alpha alpha ≠ ZS3.scale (-1) ZS3.one := by decide

/-- **The refutation.**  The spanning-tree sequence `τ(C_n(1,2))` satisfies a
six-term linear recurrence with characteristic polynomial
`p(x) = x⁶ − 4x⁵ + 10x³ − 4x + 1`, and `α² = 7 + 4√3` is not a root of `p`.
Hence `α²` is not a characteristic root of the recurrence, so the conjecture's
claimed largest real characteristic root `α²` is impossible. -/
theorem conjecture_00000000462_false :
    (∀ n : Nat, tau (n + 6) = 4 * tau (n + 5) - 10 * tau (n + 3) + 4 * tau (n + 1) - tau n)
      ∧ (∀ x : ZS3, x = ZS3.mul alpha alpha → pEval x ≠ ZS3.zero)
      ∧ ZS3.mul alpha alpha ≠ ZS3.scale (-1) ZS3.one :=
  ⟨tau_rec,
   fun x hx => by rw [hx, pEval_alpha_sq]; decide,
   alpha_sq_ne_neg_one⟩

end Tlmc462
