import Std

namespace Conjecture231

/- The literal source says that the Fibonacci period does not divide p^2.
   It does not state the conventional Wall--Sun--Sun equality pi(p^2)=pi(p).
   We cover periods modulo p and, separately, modulo p^2. -/
def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n+1 => let a := fibPair n; (a.2, a.1+a.2)

def fib (n : Nat) : Nat := (fibPair n).1

theorem fib_zero : fib 0 = 0 := rfl
theorem fib_one : fib 1 = 1 := rfl
theorem fib_recurrence (n : Nat) : fib (n+2) = fib n + fib (n+1) := rfl
theorem fibPair_second (n : Nat) : (fibPair n).2 = fib (n+1) := rfl

theorem fibonacci_unique (f : Nat → Nat) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hs : ∀ n, f (n+2) = f n + f (n+1)) : ∀ n, f n = fib n := by
  have paired : ∀ n, f n = fib n ∧ f (n+1) = fib (n+1) := by
    intro n
    induction n with
    | zero => exact ⟨h0,h1⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [show n+1+1 = n+2 by omega, hs, ih.1, ih.2, fib_recurrence]
  exact fun n => (paired n).1

def residue (m n : Nat) : Nat × Nat :=
  ((fibPair n).1 % m, (fibPair n).2 % m)
def step (m : Nat) (a : Nat × Nat) : Nat × Nat := (a.2, (a.1+a.2)%m)

theorem residue_step (m n : Nat) : residue m (n+1) = step m (residue m n) := by
  apply Prod.ext
  · rfl
  · exact Nat.add_mod _ _ _

theorem return_implies_period (m k : Nat) (h : residue m k = residue m 0) :
    ∀ n, residue m (n+k) = residue m n := by
  intro n
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [show n+1+k = (n+k)+1 by omega, residue_step, residue_step, ih]

def Period (m k : Nat) : Prop := 0 < k ∧ ∀ n, fib (n+k)%m = fib n%m
def LeastPeriod (m k : Nat) : Prop := Period m k ∧ ∀ j, Period m j → k ≤ j

theorem period_returns_pair (m k : Nat) (h : Period m k) :
    residue m k = residue m 0 := by
  apply Prod.ext
  · simpa [residue, fib] using h.2 0
  · change fib (k+1)%m = fib 1%m
    simpa [Nat.add_comm] using h.2 1

theorem least_period_certificate (m k : Nat) (hk : 0 < k)
    (returns : residue m k = residue m 0)
    (earlier : ∀ j : Fin k, 0 < j.val → residue m j.val ≠ residue m 0) :
    LeastPeriod m k := by
  refine ⟨⟨hk, ?_⟩, ?_⟩
  · intro n
    exact congrArg Prod.fst (return_implies_period m k returns n)
  · intro j hj
    by_cases hlt : j < k
    · exact False.elim (earlier ⟨j,hlt⟩ hj.1 (period_returns_pair m j hj))
    · omega

def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

theorem seven_prime : Prime 7 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have hle : d ≤ 7 := Nat.le_of_dvd (by decide) hd
  have bounded : ∀ a : Fin 8, a.val ∣ 7 → a.val = 1 ∨ a.val = 7 := by decide
  exact bounded ⟨d,by omega⟩ hd

set_option maxRecDepth 4096 in
theorem period_mod_seven : LeastPeriod 7 16 := by
  apply least_period_certificate
  · decide
  · decide
  · decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem period_mod_forty_nine : LeastPeriod 49 112 := by
  apply least_period_certificate
  · decide
  · decide
  · decide

theorem least_period_unique (m k l : Nat) (hk : LeastPeriod m k)
    (hl : LeastPeriod m l) : k = l :=
  Nat.le_antisymm (hk.2 l hl.1) (hl.2 k hk.1)

def SourceExceptionalPrime (modulus : Nat → Nat) (p : Nat) : Prop :=
  Prime p ∧ ∃ k, LeastPeriod (modulus p) k ∧ ¬ k ∣ p^2

theorem literal_counterexample :
    SourceExceptionalPrime (fun p => p) 7 ∧ 7 < 10^17 := by
  exact ⟨⟨seven_prime,16,period_mod_seven,by decide⟩,by decide⟩

theorem prime_square_reading_counterexample :
    SourceExceptionalPrime (fun p => p^2) 7 ∧ 7 < 10^17 := by
  exact ⟨⟨seven_prime,112,period_mod_forty_nine,by decide⟩,by decide⟩

theorem conjecture231_false :
    ¬ (∀ p, p < 10^17 → ¬ SourceExceptionalPrime (fun p => p) p) := by
  intro h
  exact h 7 literal_counterexample.2 literal_counterexample.1

theorem conjecture231_prime_square_reading_false :
    ¬ (∀ p, p < 10^17 → ¬ SourceExceptionalPrime (fun p => p^2) p) := by
  intro h
  exact h 7 prime_square_reading_counterexample.2 prime_square_reading_counterexample.1

theorem seven_is_not_conventional_exception :
    ∀ a b, LeastPeriod 7 a → LeastPeriod 49 b → a ≠ b := by
  intro a b ha hb
  have ha16 := least_period_unique 7 a 16 ha period_mod_seven
  have hb112 := least_period_unique 49 b 112 hb period_mod_forty_nine
  omega

#print axioms fibonacci_unique
#print axioms least_period_certificate
#print axioms period_mod_seven
#print axioms period_mod_forty_nine
#print axioms conjecture231_false
#print axioms conjecture231_prime_square_reading_false
#print axioms seven_is_not_conventional_exception
end Conjecture231
