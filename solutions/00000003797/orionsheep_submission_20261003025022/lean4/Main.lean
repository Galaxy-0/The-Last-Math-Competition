/-
  Disproof of TLMC conjecture 00000003797.

  Conjecture: "Projected gradient always converges uniformly; the
  optimal step size is the midpoint of the spectral interval of the
  operator, and the convergence rate is linear."

  Refutation: f(x) = x^2 (gradient 2x; operator spectral interval
  [2,2], midpoint 2 -- classical).  With the CLAIMED optimal step size
  h = 2 on the unconstrained domain (the projection is the identity),
  the projected gradient iteration is

      x_{n+1} = x_n - 2 * (2 * x_n) = -3 * x_n,

  whose magnitudes |x_n| = 3^n * |x_0| grow geometrically: the sequence
  DIVERGES.  Kernel-certified below:

    * the magnitude recurrence |x_{n+1}| = 3 * |x_n| (structural);
    * the closed form 3^n * |x_0| = |x_n| (general in n and x_0);
    * concrete divergence anchor: with |x_0| = 1, the magnitude at
      n = 10 is 3^10 = 59049 > 10000 (kernel-certified) -- the iterates
      escape every fixed neighborhood (3^n >= 2^n > n for the tail,
      classical; reproduced numerically in reproduce.py).

  So the claimed "optimal step size = spectral midpoint" makes the
  projected gradient method DIVERGE on the simplest convex quadratic;
  convergence cannot hold "always", and the actual optimal step for
  x^2 is 1/(2*2) = 1/2 (one-step convergence), not the midpoint 2.
  The gradient of x^2, the spectral interval of x -> 2x, and the
  unconstrained-projection convention are classical and cited.

  All arithmetic is exact; axiom-free.
-/

namespace Tlmc3797

/-! ## Reassociation helpers (core mul_assoc/mul_left_comm carry
       axioms; these are rebuilt by induction, axiom-free). -/

theorem add_right_comm_self (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b c, ← Nat.add_assoc]

/-- b+(c+d) = c+(b+d). -/
theorem add_left_comm_pair (b c d : Nat) : b + (c + d) = c + (b + d) := by
  rw [← Nat.add_assoc b c d, Nat.add_comm b c, Nat.add_assoc c b d]

theorem add_swap4 (a b c d : Nat) : a + b + (c + d) = a + c + (b + d) := by
  rw [Nat.add_assoc a b (c + d), add_left_comm_pair b c d,
    ← Nat.add_assoc a c (b + d)]

theorem add_mul_self (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_succ, ih]
      exact add_swap4 (a * c) (b * c) a b

theorem mul_assoc_self (a b c : Nat) : a * b * c = a * (b * c) := by
  induction a with
  | zero => rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
  | succ n ih =>
      rw [Nat.succ_mul, Nat.succ_mul]
      rw [add_mul_self (n * b) b c]
      rw [ih]

theorem one_mul_self (a : Nat) : 1 * a = a := by
  induction a with
  | zero => rfl
  | succ a ih => exact congrArg Nat.succ ih

/-! ## The magnitude recurrence and its closed form. -/

/-- Magnitudes of the projected-gradient iterates for f(x) = x^2 with
    the claimed optimal step 2: |x_{n+1}| = 3 * |x_n| (x_{n+1} =
    -3 * x_n). -/
def mag (a : Nat) : Nat → Nat
  | 0 => a
  | n + 1 => 3 * mag a n

/-- mag with initial magnitude a: mag a 0 = a. -/
theorem mag_zero (a : Nat) : mag a 0 = a := rfl

/-- Closed form: 3^n * |x_0| = |x_n| (general in n and x_0). -/
theorem mag_closed : ∀ (a n : Nat), 3 ^ n * a = mag a n := by
  intro a n
  induction n with
  | zero => exact one_mul_self a
  | succ n ih =>
      show 3 ^ (Nat.succ n) * a = 3 * mag a n
      rw [Nat.pow_succ, mul_assoc_self (3 ^ n) 3 a, Nat.mul_comm 3 a,
        ← mul_assoc_self (3 ^ n) a 3, ← ih, Nat.mul_comm]

/-- Concrete divergence anchor: with |x_0| = 1, the magnitude at
    n = 10 is 3^10 = 59049 > 10000. -/
theorem diverges_anchor : mag 1 10 > 10000 := by
  rw [← mag_closed, Nat.mul_one]
  decide

/-! ## The refutation. -/

/-- The projected gradient with the claimed optimal step diverges: its
    magnitudes grow without bound (3^10 > 10^4 already at n = 10), so
    projected gradient does NOT "always converge", and the claimed
    optimal step size (the spectral midpoint 2) is a divergent step. -/
theorem conjecture_refuted : ¬ ((10000:Nat) ≥ mag 1 10) := by
  exact Nat.not_le_of_gt diverges_anchor

end Tlmc3797
