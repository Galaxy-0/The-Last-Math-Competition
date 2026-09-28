/-!
# Disproof of TLMC conjecture 00000000119

Conjecture 00000000119 claims: there are infinitely many primes `p` for which
the Pisano period `pi(p)` (the period of the Fibonacci sequence modulo `p`)
is itself prime.

## The attack

Let `Q = [[1,1],[1,0]]`, so `det Q = -1` and `Q^m = [[F(m+1), F(m)], [F(m), F(m-1)]]`.
If `n` is a period of the Fibonacci sequence modulo `p` (i.e. `F(n) ≡ 0` and
`F(n+1) ≡ 1 mod p`), then `Q^n ≡ I mod p`, hence `det(Q^n) = (-1)^n ≡ 1 mod p`.
For `p ≥ 3` this forces `n` to be even. Since `pi(p) = 2` is impossible
(`F(2) = 1 ≢ 0 mod p`), the period of any `p ≥ 3`, being an even number
different from `2`, is **not prime**. On the other hand `pi(2) = 3`, which is
prime. Hence the set of primes `p` with `pi(p)` prime is exactly `{2}` —
finite — and the conjecture is false.

The determinant step is formalized through Cassini's identity
`F(n+1)^2 - F(n)F(n+2) = (-1)^n`: modulo `p` it reads `1 ≡ (-1)^n`, which is
impossible for odd `n` when `p ≥ 3`.

## Formal content of this file

Everything is proved in core Lean 4 (no Mathlib) with **zero axioms**
(verified by `Check.lean`: every declaration `#print axioms`-audited).
The formalization deliberately avoids `omega`, `simp` and `decide` on
symbolic goals (those tactics pull in `propext`/`Quot.sound`); all arithmetic
is done by structural induction and explicit rewriting with axiom-free
lemmas. Congruences are phrased in existential form (`fib n = p * a`,
`fib (n+1) = p * b + 1`), so no `%`/`/` theory is needed:

* `period_even` : the universal heart of the attack — for **every** `p ≥ 3`
  (primality of `p` is not even needed) and every `n` with `fib n = p * a`
  and `fib (n+1) = p * b + 1`, `n` is even and `n ≠ 2`.
* `only_two` : if `p` and `n` are primes and `n` is a period of the Fibonacci
  sequence mod `p`, then `p = 2`. So the set of primes with prime Pisano
  period is contained in `{2}`.
* `pisano2, pisano3, pisano5, pisano7, pisano11, pisano13` : the concrete
  Pisano periods of the first primes, matching the referee's numbers
  `pi(2)=3, pi(3)=8, pi(5)=20, pi(7)=16, pi(11)=10, pi(13)=28` (each `rfl`
  computation also verifies minimality and the wrap-around).
* `two_survives` : `pi(2) = 3` and `3` is prime, so the set is exactly `{2}`.
-/

/-- Fibonacci numbers, `fib 0 = 0`, `fib 1 = 1`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Self-contained primality predicate (equivalent to `Nat.Prime`),
phrased with an existential so that no divisibility theory is needed. -/
structure IsPrime (n : Nat) : Prop where
  ge2 : 2 ≤ n
  dvd_prime : ∀ m : Nat, (∃ c, n = m * c) → m = 1 ∨ m = n

/-! ### A small axiom-free arithmetic toolkit (proofs by structural induction) -/

theorem kMulSucc (a c : Nat) : a * (c + 1) = a * c + a := rfl

theorem kAddMul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
    rw [kMulSucc, ih, kMulSucc a c, kMulSucc b c,
        Nat.add_assoc (a * c) (b * c) (a + b), Nat.add_left_comm (b * c) a b,
        Nat.add_assoc (a * c) a (b * c + b)]

theorem kMulAssoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih => rw [kMulSucc, kMulSucc b c, ih, Nat.mul_add]

theorem kLeMulSucc (m c : Nat) : m ≤ m * (c + 1) := by
  rw [kMulSucc]
  exact Nat.le_add_left m (m * c)

/-- Every natural number is even or odd, phrased existentially. -/
theorem kParity : ∀ n : Nat, (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1) := by
  intro n
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ n ih =>
    rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inr ⟨k, by rw [hk]⟩
    · refine Or.inl ⟨k + 1, ?_⟩
      rw [hk, Nat.mul_add 2 k 1, Nat.mul_one, Nat.add_assoc (2 * k) 1 1]

/-- Existential form of `m ≤ n`. -/
theorem kLeEx : ∀ a b : Nat, a ≤ b → ∃ d, b = a + d := by
  intro a
  induction a with
  | zero => intro b _; exact ⟨b, by rw [Nat.zero_add]⟩
  | succ a ih =>
    intro b h
    cases b with
    | zero => exact absurd h (Nat.not_succ_le_zero a)
    | succ c =>
      obtain ⟨d, hd⟩ := ih c (Nat.le_of_succ_le_succ h)
      refine ⟨d, ?_⟩
      rw [hd, Nat.add_assoc a d 1, Nat.add_comm d 1, ← Nat.add_assoc a 1 d]

/-- Left cancellation for addition. -/
theorem kAddCancel (a : Nat) : ∀ b c : Nat, a + b = a + c → b = c := by
  induction a with
  | zero => intro b c h; rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | succ a ih =>
    intro b c h
    have h1' : (a + 1) + b = (a + b) + 1 := Nat.succ_add a b
    have h2' : (a + 1) + c = (a + c) + 1 := Nat.succ_add a c
    exact ih b c (Nat.succ.inj (h1'.symm.trans (h.trans h2')))

/-- `n.succ = 0` is absurd. -/
theorem mySuccNeZero (n : Nat) (h : n.succ = 0) : False := by
  cases n with
  | zero => exact absurd h (by decide)
  | succ n' => exact Nat.noConfusion h

/-- `t + 2 = 0` is absurd. -/
theorem kTwoAbsurd (t : Nat) : t + 2 = 0 → False := by
  cases t with
  | zero => intro h; rw [Nat.zero_add] at h; exact absurd h (by decide)
  | succ t' =>
    intro h
    rw [Nat.add_succ, Nat.add_succ, Nat.add_zero] at h
    have h2 : Nat.succ (Nat.succ (Nat.succ t')) = 0 := h
    exact mySuccNeZero (Nat.succ (Nat.succ t')) h2

/-- Trichotomy, existential form. -/
theorem kle : ∀ m n : Nat, m ≤ n ∨ n ≤ m
  | 0, n => Or.inl (Nat.zero_le n)
  | m+1, 0 => Or.inr (Nat.zero_le (m+1))
  | m+1, n+1 =>
    match kle m n with
    | Or.inl h => Or.inl (Nat.succ_le_succ h)
    | Or.inr h => Or.inr (Nat.succ_le_succ h)

/-- Odd-indexed Fibonacci numbers are positive. -/
theorem kFibPosOdd : ∀ k : Nat, 1 ≤ fib (2*k+1) := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    have he : fib (2*(k+1)+1) = fib (2*k+1) + fib (2*k+2) := rfl
    rw [he]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem myLeZero (m : Nat) (h : m ≤ 0) : m = 0 := by
  cases m with
  | zero => rfl
  | succ m' => exact absurd h (Nat.not_succ_le_zero m')

/-- `2 * c = 3` is absurd (parity). -/
theorem kOdd (c : Nat) (h : 2*c = 3) : False := by
  induction c with
  | zero => rw [Nat.mul_zero] at h; exact absurd h (by decide)
  | succ c' ih =>
    rw [kMulSucc, Nat.add_succ, Nat.add_succ] at h
    -- h : succ (succ (2*c'+1)) = 3, so 2*c' = 1
    have h2 : 2*c' = Nat.succ 0 := Nat.succ.inj (Nat.succ.inj h)
    cases c' with
    | zero => rw [Nat.mul_zero] at h2; exact absurd h2 (by decide)
    | succ c'' =>
      rw [kMulSucc] at h2
      -- h2 : 2*c'' + 2 = 1, but 2*c'' + 2 ≥ 2
      exact absurd (Nat.le_trans (Nat.le_refl 2)
        (Nat.le_trans (Nat.le_add_left 2 (2*c'')) (Nat.le_of_eq h2))) (by decide)

/-- `2 * c = 3` is absurd (parity). -/
theorem kTwoMulThree (c : Nat) (h : 2*c = 3) : False := by
  induction c with
  | zero => rw [Nat.mul_zero] at h; exact absurd h (by decide)
  | succ c' =>
    rw [kMulSucc, Nat.add_succ, Nat.add_succ] at h
    -- h : succ (succ (2*c'+1)) = 3
    have h2 : 2*c' = Nat.succ 0 := Nat.succ.inj (Nat.succ.inj h)
    cases c' with
    | zero => rw [Nat.mul_zero] at h2; exact absurd h2 (by decide)
    | succ c'' =>
      rw [kMulSucc] at h2
      -- h2 : 2*c'' + 2 = 1, but 2*c'' + 2 ≥ 2
      exact absurd (Nat.le_trans (Nat.le_refl 2)
        (Nat.le_trans (Nat.le_add_left 2 (2*c'')) (Nat.le_of_eq h2))) (by decide)

/-! ### Cassini's identity, the engine of the parity obstruction -/

/-- Three-leaf commutation for aligning the Cassini expansions. -/
theorem q4 (aa ab ba X : Nat) : ((aa + ba) + (ab + X)) + 1 = ((aa + ab) + (ba + X)) + 1 := by
  rw [Nat.add_assoc aa ab (ba + X), Nat.add_left_comm ab ba X, ← Nat.add_assoc aa ba (ab + X)]

/-- Odd-step Cassini algebra. -/
theorem q3 (aa ab ba X : Nat) (h : X = aa + ab + 1) :
    X + (ba + X) = ((aa + ba) + (ab + X)) + 1 := by
  rw [h,
      Nat.add_assoc (aa + ab) 1 (ba + (aa + ab + 1)),
      Nat.add_left_comm (aa + ab) 1 (ba + (aa + ab + 1)),
      Nat.add_assoc aa ab (ba + (aa + ab + 1)),
      Nat.add_left_comm ab ba (aa + ab + 1),
      ← Nat.add_assoc aa ba (ab + (aa + ab + 1)),
      Nat.add_assoc (aa + ba) (ab + (aa + ab + 1)) 1,
      Nat.add_comm (ab + (aa + ab + 1)) 1,
      Nat.add_left_comm (aa + ba) 1 (ab + (aa + ab + 1))]

/-- Even-step Cassini algebra. -/
theorem q2 (aa ab ba X : Nat) (h : X = aa + ab + 1) :
    (X + (ba + X)) + ((ab + (aa + ab)) + (X + (ba + X)))
    = ((aa + ab) + (ba + X)) + ((ab + (aa + ab)) + (X + (ba + X))) + 1 := by
  rw [q3 aa ab ba X h, q4 aa ab ba X,
      Nat.add_assoc (aa + ab + (ba + X)) 1 ((ab + (aa + ab)) + ((aa + ab) + (ba + X) + 1)),
      Nat.add_comm 1 ((ab + (aa + ab)) + ((aa + ab) + (ba + X) + 1)),
      Nat.add_assoc (aa + ab + (ba + X)) ((ab + (aa + ab)) + ((aa + ab) + (ba + X) + 1)) 1]

/-- Cassini at even index `2*k`: `F(2k+1)^2 = F(2k) F(2k+2) + 1`. -/
theorem cassini_even (k : Nat) :
    fib (2*k+1) * fib (2*k+1) = fib (2*k) * fib (2*k+2) + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have i1 : 2 * (k + 1) + 1 = 2 * k + 3 := rfl
    have i2 : 2 * (k + 1) = 2 * k + 2 := rfl
    have i3 : 2 * (k + 1) + 2 = 2 * k + 4 := rfl
    rw [i3, i1, i2]
    have e1 : fib (2 * k + 2) = fib (2 * k) + fib (2 * k + 1) := rfl
    have e2 : fib (2 * k + 3) = fib (2 * k + 1) + fib (2 * k + 2) := rfl
    have e3 : fib (2 * k + 4) = fib (2 * k + 2) + fib (2 * k + 3) := rfl
    rw [e3, e2, e1]
    have h : fib (2 * k + 1) * fib (2 * k + 1)
        = fib (2 * k) * fib (2 * k) + fib (2 * k) * fib (2 * k + 1) + 1 := by
      rw [ih, e1, Nat.mul_add]
    rw [kAddMul (fib (2*k+1)) (fib (2*k) + fib (2*k+1)) (fib (2*k+1) + (fib (2*k) + fib (2*k+1))),
        Nat.mul_add (fib (2*k+1)) (fib (2*k+1)) (fib (2*k) + fib (2*k+1)),
        Nat.mul_add (fib (2*k+1)) (fib (2*k)) (fib (2*k+1)),
        kAddMul (fib (2*k)) (fib (2*k+1)) (fib (2*k+1) + (fib (2*k) + fib (2*k+1))),
        Nat.mul_add (fib (2*k)) (fib (2*k+1)) (fib (2*k) + fib (2*k+1)),
        Nat.mul_add (fib (2*k)) (fib (2*k)) (fib (2*k+1)),
        Nat.mul_add (fib (2*k+1)) (fib (2*k+1)) (fib (2*k) + fib (2*k+1)),
        Nat.mul_add (fib (2*k+1)) (fib (2*k)) (fib (2*k+1)),
        Nat.mul_add (fib (2*k) + fib (2*k+1)) (fib (2*k) + fib (2*k+1))
          (fib (2*k+1) + (fib (2*k) + fib (2*k+1))),
        kAddMul (fib (2*k)) (fib (2*k+1)) (fib (2*k) + fib (2*k+1)),
        Nat.mul_add (fib (2*k)) (fib (2*k)) (fib (2*k+1)),
        Nat.mul_add (fib (2*k+1)) (fib (2*k)) (fib (2*k+1)),
        kAddMul (fib (2*k)) (fib (2*k+1)) (fib (2*k+1) + (fib (2*k) + fib (2*k+1))),
        Nat.mul_add (fib (2*k)) (fib (2*k+1)) (fib (2*k) + fib (2*k+1)),
        Nat.mul_add (fib (2*k)) (fib (2*k)) (fib (2*k+1)),
        Nat.mul_add (fib (2*k+1)) (fib (2*k+1)) (fib (2*k) + fib (2*k+1)),
        Nat.mul_add (fib (2*k+1)) (fib (2*k)) (fib (2*k+1)),
        h,
        q2 (fib (2*k) * fib (2*k)) (fib (2*k) * fib (2*k+1)) (fib (2*k+1) * fib (2*k))
          (fib (2*k) * fib (2*k) + fib (2*k) * fib (2*k+1) + 1) rfl]


/-- Cassini at odd index `2*k+1`: `F(2k+1) F(2k+3) = F(2k+2)^2 + 1`. -/
theorem cassini_odd (k : Nat) :
    fib (2*k+1) * fib (2*k+3) = fib (2*k+2) * fib (2*k+2) + 1 := by
  have e1 : fib (2*k+2) = fib (2*k) + fib (2*k+1) := rfl
  have e2 : fib (2*k+3) = fib (2*k+1) + fib (2*k+2) := rfl
  have h : fib (2*k+1) * fib (2*k+1)
      = fib (2*k) * fib (2*k) + fib (2*k) * fib (2*k+1) + 1 := by
    rw [cassini_even k, e1, Nat.mul_add]
  rw [e2, e1,
      Nat.mul_add (fib (2*k+1)) (fib (2*k+1)) (fib (2*k) + fib (2*k+1)),
      Nat.mul_add (fib (2*k+1)) (fib (2*k)) (fib (2*k+1)),
      kAddMul (fib (2*k)) (fib (2*k+1)) (fib (2*k) + fib (2*k+1)),
      Nat.mul_add (fib (2*k)) (fib (2*k)) (fib (2*k+1)),
      Nat.mul_add (fib (2*k+1)) (fib (2*k)) (fib (2*k+1)),
      h,
      q3 (fib (2*k) * fib (2*k)) (fib (2*k) * fib (2*k+1)) (fib (2*k+1) * fib (2*k))
        (fib (2*k) * fib (2*k) + fib (2*k) * fib (2*k+1) + 1) rfl,
      q4 (fib (2*k) * fib (2*k)) (fib (2*k) * fib (2*k+1)) (fib (2*k+1) * fib (2*k))
        (fib (2*k) * fib (2*k) + fib (2*k) * fib (2*k+1) + 1)]

/-- The algebra of the odd-index contradiction: `(p*b+1)^2 + 1` equals
`p * (p*(b*b) + (b+b)) + 2`, exhibiting a remainder of `2` modulo `p`. -/
theorem hr (p b : Nat) : (p*b+1)*(p*b+1) + 1 = p*(p*(b*b) + (b+b)) + 2 := by
  rw [kAddMul (p*b) 1 (p*b+1),
      Nat.one_mul,
      kMulSucc (p*b) (p*b),
      kMulAssoc p b (p*b)]
  have hb1 : b * (p * b) = p * (b * b) := by
    rw [← kMulAssoc b p b, Nat.mul_comm b p, kMulAssoc p b b]
  rw [hb1, Nat.add_assoc (p*(p*(b*b))) (p*b) (p*b+1),
      Nat.mul_add p (p*(b*b)) (b+b),
      Nat.mul_add p b b,
      Nat.add_succ, Nat.add_succ, Nat.add_zero]
  rfl

/-! ### The universal obstruction -/

/-- An even number different from `2` is not prime. -/
theorem not_prime_of_even_ne_two (n : Nat) (he : ∃ k, n = 2 * k) (h2 : n ≠ 2) :
    ¬ IsPrime n := by
  intro hp
  obtain ⟨k, hk⟩ := he
  rcases hp.dvd_prime 2 ⟨k, hk⟩ with h1 | h3
  · exact absurd h1 (by decide)
  · exact absurd h3.symm h2

/-- **The universal heart of the attack.**
For every `p ≥ 3` (primality not needed) every period `n` of the Fibonacci
sequence mod `p` is even and is not `2`. Consequently no `p ≥ 3` has a prime
Pisano period: an even period different from `2` is composite. -/
theorem period_even (p n : Nat) (hp : 3 ≤ p)
    (h0 : ∃ a, fib n = p * a) (h1 : ∃ b, fib (n + 1) = p * b + 1) :
    (∃ k, n = 2 * k) ∧ n ≠ 2 := by
  have hn2 : n ≠ 2 := by
    intro he
    obtain ⟨a, ha⟩ := h0
    rw [he] at ha
    rw [show fib 2 = 1 from rfl] at ha
    cases a with
    | zero => rw [Nat.mul_zero] at ha; exact absurd ha (by decide)
    | succ a' =>
      rw [kMulSucc] at ha
      have hle : p ≤ 1 := Nat.le_trans (Nat.le_add_left p (p * a')) (Nat.le_of_eq ha.symm)
      exact absurd (Nat.le_trans hp hle) (by decide)
  rcases kParity n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨⟨k, hk⟩, hn2⟩
  · exfalso
    obtain ⟨a, ha⟩ := h0
    obtain ⟨b, hb⟩ := h1
    rw [hk] at ha hb
    have hb2 : fib (2*k+2) = p * b + 1 := hb
    have hpos : 1 ≤ fib (2*k+1) := kFibPosOdd k
    have hage : 1 ≤ a := by
      cases a with
      | zero =>
        rw [Nat.mul_zero] at ha
        rw [ha] at hpos
        exact absurd hpos (by decide)
      | succ a' => exact Nat.succ_le_succ (Nat.zero_le a')
    have h2 : fib (2*k+3) = p * (a + b) + 1 := by
      have e2 : fib (2*k+3) = fib (2*k+1) + fib (2*k+2) := rfl
      rw [e2, ha, hb2, ← Nat.add_assoc (p*a) (p*b) 1, ← Nat.mul_add p a b]
    have hoc := cassini_odd k
    rw [ha, hb2, h2, kMulAssoc p a (p*(a+b)+1), hr p b] at hoc
    rcases kle (a*(p*(a+b)+1)) (p*(b*b)+(b+b)) with hle | hle
    · obtain ⟨d, hd⟩ := kLeEx (a*(p*(a+b)+1)) (p*(b*b)+(b+b)) hle
      rw [hd, Nat.mul_add p (a*(p*(a+b)+1)) d,
          Nat.add_assoc (p*(a*(p*(a+b)+1))) (p*d) 2] at hoc
      have h'' : p*(a*(p*(a+b)+1)) = p*(a*(p*(a+b)+1)) + (p*d+2) := hoc
      exact absurd (kAddCancel _ (p*d+2) 0 h''.symm) (kTwoAbsurd (p*d))
    · obtain ⟨d, hd⟩ := kLeEx (p*(b*b)+(b+b)) (a*(p*(a+b)+1)) hle
      have hA : p*(a*(p*(a+b)+1)) = p*((p*(b*b)+(b+b)) + d) := by rw [hd]
      rw [Nat.mul_add p (p*(b*b)+(b+b)) d] at hA
      rw [hA] at hoc
      have h2' : p*d = 2 := kAddCancel _ (p*d) 2 hoc
      cases d with
      | zero => rw [Nat.mul_zero] at h2'; exact absurd h2' (by decide)
      | succ d' =>
        rw [kMulSucc] at h2'
        have hle2 : p ≤ 2 :=
          Nat.le_trans (Nat.le_add_left p (p*d')) (Nat.le_of_eq h2')
        exact absurd (Nat.le_trans hp hle2) (by decide)

/-- **Uniqueness.** If `p` and `n` are primes and `n` is a period of the
Fibonacci sequence mod `p`, then `p = 2`. So the set of primes with prime
Pisano period is contained in `{2}` — the conjecture's infinitude fails. -/
theorem only_two (p n : Nat) (hpp : IsPrime p) (hnp : IsPrime n)
    (h0 : ∃ a, fib n = p * a) (h1 : ∃ b, fib (n + 1) = p * b + 1) : p = 2 := by
  cases p with
  | zero => exact absurd hpp.ge2 (by decide)
  | succ p' =>
    cases p' with
    | zero => exact absurd hpp.ge2 (by decide)
    | succ p'' =>
      cases p'' with
      | zero => rfl
      | succ p''' =>
        exfalso
        have hge : 3 ≤ Nat.succ (Nat.succ (Nat.succ p''')) :=
          Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le p''')))
        have h := period_even (Nat.succ (Nat.succ (Nat.succ p'''))) n hge h0 h1
        obtain ⟨k, hk⟩ := h.1
        have hne : n ≠ 2 := h.2
        rcases hnp.dvd_prime 2 ⟨k, hk⟩ with h1' | h2'
        · exact absurd h1' (by decide)
        · exact absurd h2'.symm hne

/-! ### The surviving prime: `p = 2` with `pi(2) = 3` prime -/

theorem prime2 : IsPrime 2 := by
  refine ⟨by decide, ?_⟩
  intro m hd
  obtain ⟨c, hc⟩ := hd
  -- hc : 2 = m * c
  cases Nat.lt_or_ge m 2 with
  | inl hlt =>
    -- m < 2:  m = 0 or m = 1
    cases m with
    | zero => rw [Nat.zero_mul] at hc; exact absurd hc (by decide)
    | succ m' =>
      cases m' with
      | zero => exact Or.inl rfl
      | succ m'' =>
        have h1' : Nat.succ (Nat.succ (Nat.succ m'')) ≤ Nat.succ (Nat.succ 0) := hlt
        have h2' : Nat.succ (Nat.succ m'') ≤ Nat.succ 0 := Nat.le_of_succ_le_succ h1'
        have h3' : Nat.succ m'' ≤ 0 := Nat.le_of_succ_le_succ h2'
        exact absurd h3' (Nat.not_succ_le_zero m'')
  | inr hge =>
    -- m ≥ 2 and c ≥ 1 force m ≤ m*c = 2, so m = 2
    cases c with
    | zero => rw [Nat.mul_zero] at hc; exact absurd hc (by decide)
    | succ c' =>
      have hle : m ≤ 2 := Nat.le_trans (kLeMulSucc m c') (Nat.le_of_eq hc.symm)
      exact Or.inr (Nat.le_antisymm hle hge)

theorem prime3 : IsPrime 3 := by
  refine ⟨by decide, ?_⟩
  intro m hd
  obtain ⟨c, hc⟩ := hd
  -- hc : 3 = m * c
  cases Nat.lt_or_ge m 3 with
  | inl hlt =>
    -- m < 3:  m = 0, 1 or 2
    cases m with
    | zero => rw [Nat.zero_mul] at hc; exact absurd hc (by decide)
    | succ m' =>
      cases m' with
      | zero => exact Or.inl rfl
      | succ m'' =>
        cases m'' with
        | zero => exact absurd (kTwoMulThree c hc.symm) (by decide)
        | succ m''' =>
          have hs1 : Nat.succ (Nat.succ (Nat.succ (Nat.succ m''')))
              ≤ Nat.succ (Nat.succ (Nat.succ 0)) := hlt
          have hs2 := Nat.le_of_succ_le_succ hs1
          have hs3 := Nat.le_of_succ_le_succ hs2
          have hs4 := Nat.le_of_succ_le_succ hs3
          exact absurd hs4 (Nat.not_succ_le_zero m''')
  | inr hge =>
    -- m ≥ 3 and c ≥ 1 force m ≤ m*c = 3, so m = 3
    cases c with
    | zero => rw [Nat.mul_zero] at hc; exact absurd hc (by decide)
    | succ c' =>
      have hle : m ≤ 3 := Nat.le_trans (kLeMulSucc m c') (Nat.le_of_eq hc.symm)
      exact Or.inr (Nat.le_antisymm hle hge)

/-- Bounded period search: the least `n ≥ 1` with `fib n % p = 0` and
`fib (n+1) % p = 1`, or `0` if there is none up to the fuel bound. -/
def search (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
      if fib n % p = 0 && fib (n + 1) % p = 1 then n else search p fuel (n + 1)

/-- The Pisano period of `p` computed by bounded search from `n = 1`. -/
def pisano (p fuel : Nat) : Nat := search p fuel 1

/-- The referee's numbers: `pi(2)=3, pi(3)=8, pi(5)=20, pi(7)=16,
pi(11)=10, pi(13)=28`. Each `rfl` computation verifies the whole bounded
search, including minimality (failed candidates) and the wrap-around. -/
theorem pisano2 : pisano 2 10 = 3 := rfl
theorem pisano3 : pisano 3 20 = 8 := rfl
theorem pisano5 : pisano 5 40 = 20 := rfl
theorem pisano7 : pisano 7 40 = 16 := rfl
theorem pisano11 : pisano 11 40 = 10 := rfl
theorem pisano13 : pisano 13 60 = 28 := rfl

/-- `3` is a period of the Fibonacci sequence mod `2`, and it is prime. -/
theorem two_survives : fib 3 % 2 = 0 ∧ fib 4 % 2 = 1 ∧ IsPrime 3 := ⟨rfl, rfl, prime3⟩

/-- The period `3` of `p = 2` in existential form, matching the hypothesis
shape of `period_even` and `only_two`. -/
theorem two_period_ex : (∃ a, fib 3 = 2 * a) ∧ (∃ b, fib 4 = 2 * b + 1) :=
  ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩
