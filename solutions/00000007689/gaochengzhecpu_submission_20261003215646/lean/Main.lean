import Std

namespace Conjecture7689
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual Delannoy numbers, including both boundary rows. -/
def D : Nat → Nat → Nat
  | 0, _ => 1
  | _, 0 => 1
  | r+1, s+1 => D r (s+1) + D (r+1) s + D r s
termination_by r s => r+s

theorem recursion_unique (a : Nat → Nat → Nat)
    (hzero : ∀ s, a 0 s=1) (hzero' : ∀ r, a r 0=1)
    (hstep : ∀ r s, a (r+1) (s+1)=a r (s+1)+a (r+1) s+a r s) :
    ∀ r s, a r s = D r s := by
  intro r s
  induction r generalizing s with
  | zero => simp [hzero, D]
  | succ r ihr =>
    induction s with
    | zero => simp [hzero', D]
    | succ s ihs => rw [hstep, D, ihr, ihr, ihs]

theorem mono_right (r s : Nat) : D r s ≤ D r (s+1) := by
  cases r with
  | zero => simp [D]
  | succ r => rw [D]; omega
theorem mono_left (r s : Nat) : D r s ≤ D (r+1) s := by
  cases s with
  | zero => cases r <;> simp [D]
  | succ s => rw [D]; omega

theorem block_growth (r s : Nat) : 13 * D r s ≤ D (r+2) (s+2) := by
  have a := mono_left r s
  have b := mono_right r s
  have c := mono_left (r+1) s
  have d := mono_right r (s+1)
  change D (r+1) s ≤ D (r+2) s at c
  change D r (s+1) ≤ D r (s+2) at d
  have e : D (r+1) (s+1) = D r (s+1)+D (r+1) s+D r s := by rw [D]
  have f : D (r+1) (s+2) = D r (s+2)+D (r+1) (s+1)+D r (s+1) := by rw [D]
  have g : D (r+2) (s+1) = D (r+1) (s+1)+D (r+2) s+D (r+1) s := by rw [D]
  have h : D (r+2) (s+2) = D (r+1) (s+2)+D (r+2) (s+1)+D (r+1) (s+1) := by rw [D]
  omega

theorem all_diagonal_lower_bounds (n : Nat) : 13^n ≤ D (2*n) (2*n) := by
  induction n with
  | zero => simp [D]
  | succ n ih =>
    have h := block_growth (2*n) (2*n)
    have hm := Nat.mul_le_mul_left 13 ih
    rw [Nat.pow_succ]
    have he : 2*(n+1)=2*n+2 := by omega
    rw [he]
    omega

/-- A fully quantified elementary Bernoulli estimate, avoiding numerical
    approximation to the exponential growth constant. -/
theorem bernoulli_bound (n : Nat) : (4*n+9)*9^n ≤ 9*13^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc
      (4*(n+1)+9)*9^(n+1) = ((4*(n+1)+9)*9)*9^n := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ ((4*n+9)*13)*9^n := Nat.mul_le_mul_right _ (by omega)
      _ = 13*((4*n+9)*9^n) := by ac_rfl
      _ ≤ 13*(9*13^n) := Nat.mul_le_mul_left 13 ih
      _ = 9*13^(n+1) := by rw [Nat.pow_succ]; ac_rfl

theorem no_eventual_three_power_bound :
    ¬ ∃ C N : Nat, ∀ m : Nat, N ≤ m → D m m ≤ C*3^m := by
  rintro ⟨C, N, h⟩
  let n := 9*C+N+1
  have hm : N ≤ 2*n := by dsimp [n]; omega
  have hu := h (2*n) hm
  have hl := all_diagonal_lower_bounds n
  have hp : 3^(2*n)=9^n := by rw [Nat.pow_mul]
  rw [hp] at hu
  have he : 13^n ≤ C*9^n := Nat.le_trans hl hu
  have hb := bernoulli_bound n
  have hc := Nat.mul_le_mul_left 9 he
  have hi : (4*n+9)*9^n ≤ (9*C)*9^n := by
    exact Nat.le_trans hb (by simpa only [Nat.mul_assoc] using hc)
  have hf := Nat.le_of_mul_le_mul_right hi (Nat.pow_pos (by decide))
  dsimp [n] at hf
  omega

/-- An O(3^m) bound is already a necessary consequence of the claimed
    positive finite-constant asymptotic c*3^m/sqrt(m). The conjunction fails
    for every array, independently of how its Bailey interpretation is made. -/
def NecessaryAssertions (a : Nat → Nat → Nat) : Prop :=
  (∀ r s : Nat, a r s = D r s) ∧
  ∃ C N : Nat, ∀ m : Nat, N ≤ m → a m m ≤ C*3^m

theorem conjecture7689_counterexample (a : Nat → Nat → Nat) :
    ¬ NecessaryAssertions a := by
  rintro ⟨heq, C, N, hb⟩
  apply no_eventual_three_power_bound
  refine ⟨C, N, ?_⟩
  intro m hm
  simpa only [heq] using hb m hm

end Conjecture7689
#print axioms Conjecture7689.recursion_unique
#print axioms Conjecture7689.conjecture7689_counterexample
