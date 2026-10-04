import Std

namespace Conjecture7683

/-- Coefficient lists are in increasing degree order. -/
abbrev Poly := List Nat

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

/-- Ordinary polynomial multiplication: aQ + X(PQ). -/
def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add (q.map (a * ·)) (0 :: mul p q)

def eval (x : Nat) : Poly → Nat
  | [] => 0
  | a :: p => a + x * eval x p

theorem eval_add (x : Nat) (p q : Poly) :
    eval x (add p q) = eval x p + eval x q := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add, eval]
    | cons b q =>
      simp [add, eval, ih, Nat.mul_add, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm]

theorem eval_scale (x a : Nat) (p : Poly) :
    eval x (p.map (a * ·)) = a * eval x p := by
  induction p with
  | nil => simp [eval]
  | cons b p ih =>
    simp [eval, ih, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm]

theorem eval_mul (x : Nat) (p q : Poly) :
    eval x (mul p q) = eval x p * eval x q := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih =>
    simp [mul, eval_add, eval_scale, eval, ih, Nat.add_mul, Nat.mul_assoc]

/-- The coefficients of 1 + X + ... + X^(n-1). -/
def qInteger (n : Nat) : Poly := List.replicate n 1

/-- The product of qInteger i for i = 1,...,n; the empty product is 1. -/
def qFactorial : Nat → Poly
  | 0 => [1]
  | n + 1 => mul (qFactorial n) (qInteger (n + 1))

theorem eval_qFactorial_succ (x n : Nat) :
    eval x (qFactorial (n + 1)) =
      eval x (qFactorial n) * eval x (qInteger (n + 1)) :=
  eval_mul x (qFactorial n) (qInteger (n + 1))

def coeff (p : Poly) (m : Nat) : Nat := p[m]?.getD 0

/-- No equal adjacent coefficients within the finite coefficient sequence. -/
def FlatFree (p : Poly) : Prop :=
  ∀ m, m + 1 < p.length → coeff p m ≠ coeff p (m + 1)

/-- An adjacent pair of equal global maximum coefficients inside the support. -/
def HasFlatMaximum (p : Poly) : Prop :=
  ∃ m, m + 1 < p.length ∧
    coeff p m = coeff p (m + 1) ∧
    (∀ k, coeff p k ≤ coeff p m)

theorem qFactorial_three : qFactorial 3 = [1, 2, 2, 1] := by rfl

theorem coefficient_formula (m : Nat) :
    coeff (qFactorial 3) m =
      if m = 0 then 1 else if m = 1 then 2 else if m = 2 then 2
      else if m = 3 then 1 else 0 := by
  cases m with
  | zero => rfl
  | succ m =>
    cases m with
    | zero => rfl
    | succ m =>
      cases m with
      | zero => rfl
      | succ m =>
        cases m with
        | zero => rfl
        | succ m => simp [qFactorial_three, coeff]

theorem flat_maximum : HasFlatMaximum (qFactorial 3) := by
  refine ⟨1, by decide, by decide, ?_⟩
  intro k
  change coeff (qFactorial 3) k ≤ 2
  rw [coefficient_formula]
  split <;> (try split) <;> (try split) <;> (try split) <;> decide

theorem not_flatFree : ¬ FlatFree (qFactorial 3) := by
  intro h
  exact h 1 (by decide) (by decide)

/-- A necessary clause of the conjecture, restricted even to n >= 3. -/
def AllFlatFree : Prop := ∀ n, 3 ≤ n → FlatFree (qFactorial n)

theorem conjecture_flatFree_false : ¬ AllFlatFree := by
  intro h
  exact not_flatFree (h 3 (by decide))

/-- Adding any other clauses cannot repair the contradicted clause. -/
theorem conjecture_false (remainingClauses : Prop) :
    ¬ (AllFlatFree ∧ remainingClauses) := by
  intro h
  exact conjecture_flatFree_false h.1

#print axioms eval_mul
#print axioms coefficient_formula
#print axioms flat_maximum
#print axioms conjecture_flatFree_false
#print axioms conjecture_false

end Conjecture7683
