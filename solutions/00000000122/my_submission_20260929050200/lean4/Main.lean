/-!
# Disproof of TLMC conjecture 00000000122

**Conjecture.** For every `n ≥ 2` there exist infinitely many primes `q` such that
the `n`-th `q`-Catalan number `C_n(q)` is prime.

**Attack (n = 2).** In the standard reading (Gaussian-binomial q-Catalan,
`C_n(q) = [2n choose n]_q / [n+1]_q`) one has `C_2(q) = q² + 1`.  For every odd
prime `q`, the number `q² + 1` is even and `≥ 10`, hence composite.  So among
primes `q`, at most `q = 2` can give a prime value (indeed `C_2(2) = 5` is prime):
there is exactly one, not infinitely many.

Under the Carlitz reading (`C_0 = 1`, `C_{n+1} = Σ_k q^k C_k C_{n-k}`, so
`C_2(q) = q + 1`) the same collapse happens: odd prime `q` gives `q + 1` even
and `≥ 4`, and again `q = 2` (`C_2(2) = 3`) is the only prime witness.

This file formalizes the numerical assertion of the attack in core Lean
(no Mathlib).  Every theorem is proved with **zero axioms and zero `sorry`**
(avoiding `omega`, `simp` and the core mod/div lemmas, which carry `propext`
or `Quot.sound` in this toolchain); see `Check.lean` for the audit.
-/

/-- Self-contained primality predicate (same content as `Nat.Prime`). -/
def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

/-- Standard q-Catalan, second level: `C₂(q) = q² + 1`
(`[4 choose 2]_q = (1+q²)(1+q+q²)`, `[3]_q = 1+q+q²`, quotient `= 1+q²`). -/
def C2 (q : Nat) : Nat := q * q + 1

/-- Carlitz q-Catalan, second level: `C₂(q) = q + 1`
(`C₀ = 1`, `C₁ = 1`, `C₂ = C₀C₁ + q C₁ C₀ = 1 + q`). -/
def C2Carlitz (q : Nat) : Nat := q + 1

/-- Even numbers, by decomposition `n = 2 * k` (avoids the axiom-carrying
core `%` API). -/
def EvenN (n : Nat) : Prop := ∃ k, n = 2 * k

/-- Odd numbers, by decomposition `n = 2 * k + 1`. -/
def OddN (n : Nat) : Prop := ∃ k, n = 2 * k + 1

/-! ### Small arithmetic utilities (all built from axiom-free core lemmas) -/

theorem add4 (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b (c + d), ← Nat.add_assoc b c d, Nat.add_comm b c,
      Nat.add_assoc c b d, Nat.add_assoc a c (b + d)]

theorem bridge (Y Q : Nat) :
    (((Y + Y) + Q) + (Q + 1)) + 1 = ((Y + Q) + 1) + ((Y + Q) + 1) := by
  rw [Nat.add_assoc ((Y + Y) + Q) (Q + 1) 1,
      Nat.add_assoc Q 1 1,
      Nat.add_assoc (Y + Y) Q (Q + (1 + 1)),
      ← Nat.add_assoc Q Q (1 + 1),
      add4 (Y + Q) 1 (Y + Q) 1,
      add4 Y Q Y Q,
      ← Nat.add_assoc (Y + Y) (Q + Q) (1 + 1)]

/-! ### Parity -/

theorem even_or_odd : ∀ n : Nat, EvenN n ∨ OddN n
  | 0 => Or.inl ⟨0, rfl⟩
  | n + 1 => by
    rcases even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inr ⟨k, by rw [hk]⟩
    · exact Or.inl ⟨k + 1, by rw [hk, Nat.mul_succ]⟩

/-- If `q` is odd then `q² + 1` is even: `(2j+1)² + 1 = 2·(2j² + 2j + 1)`. -/
theorem odd_sq_add_one_even {q : Nat} (h : OddN q) : EvenN (q * q + 1) := by
  obtain ⟨j, hj⟩ := h
  refine ⟨(j * j + j * j) + (j + j) + 1, ?_⟩
  rw [hj]
  have h1 : (2 * j + 1) * (2 * j + 1) = (2 * j + 1) * Nat.succ (2 * j) := rfl
  have h2 : (2 * j + 1) * Nat.succ (2 * j) = (2 * j + 1) * (2 * j) + (2 * j + 1) :=
    Nat.mul_succ (2 * j + 1) (2 * j)
  have h3 : (2 * j + 1) * (2 * j) = (2 * j) * (2 * j) + 2 * j := Nat.succ_mul (2 * j) (2 * j)
  rw [h1, h2, h3, Nat.two_mul, Nat.mul_add, Nat.mul_comm (j + j) j, Nat.mul_add, bridge,
      ← Nat.two_mul]

/-- If `q` is odd then `q + 1` is even. -/
theorem odd_add_one_even {q : Nat} (h : OddN q) : EvenN (q + 1) :=
  let ⟨j, hj⟩ := h
  ⟨j + 1, by rw [hj, Nat.mul_add, Nat.two_mul]⟩

theorem odd_sq_add_one_dvd {q : Nat} (h : OddN q) : 2 ∣ q * q + 1 := odd_sq_add_one_even h

theorem odd_add_one_dvd {q : Nat} (h : OddN q) : 2 ∣ q + 1 := odd_add_one_even h

/-! ### Primes are odd unless they are 2 -/

/-- An even prime number must be `2`. -/
theorem even_prime_eq_two {q : Nat} (hp : IsPrime q) (he : EvenN q) : q = 2 := by
  obtain ⟨h2, hd⟩ := hp
  obtain ⟨k, hk⟩ := he
  rcases hd 2 ⟨k, hk⟩ with h1 | hq2
  · exact absurd h1 (by decide)
  · exact hq2.symm

/-- A prime different from `2` is odd. -/
theorem odd_of_prime_ne_two {q : Nat} (hp : IsPrime q) (hne : q ≠ 2) : OddN q := by
  rcases even_or_odd q with h | h
  · exact absurd (even_prime_eq_two hp h) hne
  · exact h

/-! ### The attack -/

/-- **Attack, standard reading.** For an odd prime `q` (any odd `q ≥ 3`),
`C₂(q) = q² + 1` is not prime: it is even (`2 ∣ q² + 1`) and `≥ 10 > 2`. -/
theorem not_prime_C2_of_odd {q : Nat} (hq : OddN q) (h3 : 3 ≤ q) : ¬ IsPrime (C2 q) := by
  show ¬ IsPrime (q * q + 1)
  rintro ⟨_, hd⟩
  have h9 : (9 : Nat) ≤ q * q := Nat.mul_le_mul h3 h3
  rcases hd 2 (odd_sq_add_one_dvd hq) with h1 | h2
  · exact absurd h1 (by decide)
  · have h10 : (10 : Nat) ≤ q * q + 1 := Nat.succ_le_succ h9
    rw [← h2] at h10
    exact absurd h10 (by decide)

/-- **Attack, Carlitz reading.** For an odd prime `q`, `C₂(q) = q + 1` is not
prime: it is even and `≥ 4 > 2`. -/
theorem not_prime_C2Carlitz_of_odd {q : Nat} (hq : OddN q) (h3 : 3 ≤ q) :
    ¬ IsPrime (C2Carlitz q) := by
  show ¬ IsPrime (q + 1)
  rintro ⟨_, hd⟩
  have h4 : 4 ≤ q + 1 := Nat.succ_le_succ h3
  rcases hd 2 (odd_add_one_dvd hq) with h1 | h2
  · exact absurd h1 (by decide)
  · rw [← h2] at h4
    exact absurd h4 (by decide)

/-! ### Collapse of the n = 2 instance: at most one prime witness -/

/-- **Standard reading.** For a prime `q`, `C₂(q) = q² + 1` is prime **only if**
`q = 2`.  Hence the set of primes `q` with `C₂(q)` prime has at most one
element — contradicting "infinitely many". -/
theorem C2_prime_only_q_two {q : Nat} (hp : IsPrime q) (hc : IsPrime (C2 q)) : q = 2 := by
  have h2 : 2 ≤ q := hp.1
  rcases Nat.lt_or_ge q 3 with h3 | h3
  · exact Nat.le_antisymm (Nat.le_of_lt_succ h3) h2
  · have hne : q ≠ 2 := by
      intro he
      rw [he] at h3
      exact absurd h3 (by decide)
    exact absurd hc (not_prime_C2_of_odd (odd_of_prime_ne_two hp hne) h3)

/-- **Carlitz reading.** For a prime `q`, `C₂(q) = q + 1` is prime **only if**
`q = 2`. -/
theorem C2Carlitz_prime_only_q_two {q : Nat} (hp : IsPrime q) (hc : IsPrime (C2Carlitz q)) :
    q = 2 := by
  have h2 : 2 ≤ q := hp.1
  rcases Nat.lt_or_ge q 3 with h3 | h3
  · exact Nat.le_antisymm (Nat.le_of_lt_succ h3) h2
  · have hne : q ≠ 2 := by
      intro he
      rw [he] at h3
      exact absurd h3 (by decide)
    exact absurd hc (not_prime_C2Carlitz_of_odd (odd_of_prime_ne_two hp hne) h3)

/-! ### The unique witness is genuine (boundary of the attack) -/

/-- `C₂(2) = 5` in the standard reading. -/
theorem C2_two : C2 2 = 5 := rfl

/-- `C₂(2) = 3` in the Carlitz reading. -/
theorem C2Carlitz_two : C2Carlitz 2 = 3 := rfl

/-- `5` is prime. -/
theorem five_is_prime : IsPrime 5 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  obtain ⟨a, ha⟩ := hd
  have hap : 0 < a := by
    cases a with
    | zero => rw [Nat.mul_zero] at ha; exact absurd ha (by decide)
    | succ a' => exact Nat.zero_lt_succ a'
  have hda5 : d * a ≤ 5 := by rw [ha]; exact Nat.le_refl _
  have hd5 : d ≤ 5 := Nat.le_trans (Nat.le_mul_of_pos_right d hap) hda5
  have hd1 : 1 ≤ d := by
    rcases Nat.lt_or_ge d 1 with h | h
    · have hd0 : d = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h)
      rw [hd0, Nat.zero_mul] at ha
      exact absurd ha (by decide)
    · exact h
  rcases Nat.lt_or_ge d 2 with h12 | h2le
  · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h12) hd1)
  · rcases Nat.lt_or_ge d 3 with h23 | h3le
    · exfalso
      have hd2 : d = 2 := Nat.le_antisymm (Nat.le_of_lt_succ h23) h2le
      rw [hd2] at ha
      rcases Nat.lt_or_ge a 3 with hlt | hge
      · rcases Nat.lt_or_ge a 1 with ha0 | ha1le
        · rw [Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha0), Nat.mul_zero] at ha
          exact absurd ha (by decide)
        · rcases Nat.lt_or_ge a 2 with ha12 | ha2le
          · rw [Nat.le_antisymm (Nat.le_of_lt_succ ha12) ha1le, Nat.mul_one] at ha
            exact absurd ha (by decide)
          · rw [Nat.le_antisymm (Nat.le_of_lt_succ hlt) ha2le] at ha
            exact absurd ha (by decide)
      · have h6 : (6 : Nat) ≤ a * 2 := Nat.mul_le_mul hge (Nat.le_refl 2)
        rw [Nat.mul_comm a 2, ← ha] at h6
        exact absurd h6 (by decide)
    · rcases Nat.lt_or_ge d 4 with h34 | h4le
      · exfalso
        have hd3 : d = 3 := Nat.le_antisymm (Nat.le_of_lt_succ h34) h3le
        rw [hd3] at ha
        rcases Nat.lt_or_ge a 2 with hlt | hge
        · rcases Nat.lt_or_ge a 1 with ha0 | ha1
          · rw [Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha0), Nat.mul_zero] at ha
            exact absurd ha (by decide)
          · rw [Nat.le_antisymm (Nat.le_of_lt_succ hlt) ha1, Nat.mul_one] at ha
            exact absurd ha (by decide)
        · have h6 : (6 : Nat) ≤ 3 * a := Nat.mul_le_mul (Nat.le_refl 3) hge
          rw [← ha] at h6
          exact absurd h6 (by decide)
      · rcases Nat.lt_or_ge d 5 with h45 | h5le
        · exfalso
          have hd4 : d = 4 := Nat.le_antisymm (Nat.le_of_lt_succ h45) h4le
          rw [hd4] at ha
          rcases Nat.lt_or_ge a 2 with hlt | hge
          · rcases Nat.lt_or_ge a 1 with ha0 | ha1
            · rw [Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha0), Nat.mul_zero] at ha
              exact absurd ha (by decide)
            · rw [Nat.le_antisymm (Nat.le_of_lt_succ hlt) ha1, Nat.mul_one] at ha
              exact absurd ha (by decide)
          · have h8 : (8 : Nat) ≤ 4 * a := Nat.mul_le_mul (Nat.le_refl 4) hge
            rw [← ha] at h8
            exact absurd h8 (by decide)
        · exact Or.inr (Nat.le_antisymm hd5 h5le)

/-- `3` is prime. -/
theorem three_is_prime : IsPrime 3 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  obtain ⟨a, ha⟩ := hd
  have hap : 0 < a := by
    cases a with
    | zero => rw [Nat.mul_zero] at ha; exact absurd ha (by decide)
    | succ a' => exact Nat.zero_lt_succ a'
  have hda3 : d * a ≤ 3 := by rw [ha]; exact Nat.le_refl _
  have hd3 : d ≤ 3 := Nat.le_trans (Nat.le_mul_of_pos_right d hap) hda3
  have hd1 : 1 ≤ d := by
    rcases Nat.lt_or_ge d 1 with h | h
    · have hd0 : d = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h)
      rw [hd0, Nat.zero_mul] at ha
      exact absurd ha (by decide)
    · exact h
  rcases Nat.lt_or_ge d 2 with h12 | h2le
  · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h12) hd1)
  · rcases Nat.lt_or_ge d 3 with h23 | h3le
    · exfalso
      have hd2 : d = 2 := Nat.le_antisymm (Nat.le_of_lt_succ h23) h2le
      rw [hd2] at ha
      rcases Nat.lt_or_ge a 3 with hlt | hge
      · rcases Nat.lt_or_ge a 1 with ha0 | ha1le
        · rw [Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha0), Nat.mul_zero] at ha
          exact absurd ha (by decide)
        · rcases Nat.lt_or_ge a 2 with ha12 | ha2le
          · rw [Nat.le_antisymm (Nat.le_of_lt_succ ha12) ha1le, Nat.mul_one] at ha
            exact absurd ha (by decide)
          · rw [Nat.le_antisymm (Nat.le_of_lt_succ hlt) ha2le] at ha
            exact absurd ha (by decide)
      · have h6 : (6 : Nat) ≤ a * 2 := Nat.mul_le_mul hge (Nat.le_refl 2)
        rw [Nat.mul_comm a 2, ← ha] at h6
        exact absurd h6 (by decide)
    · exact Or.inr (Nat.le_antisymm hd3 h3le)

/-! ### Full classification and headline disproofs -/

/-- Full classification, standard reading: the only prime `q` with `C₂(q)`
prime is `q = 2` (where `C₂(2) = 5`). -/
theorem C2_prime_iff_eq_two {q : Nat} (hp : IsPrime q) : IsPrime (C2 q) ↔ q = 2 :=
  ⟨C2_prime_only_q_two hp, by
    intro h
    subst h
    exact five_is_prime⟩

/-- Full classification, Carlitz reading: the only prime `q` with `C₂(q)`
prime is `q = 2` (where `C₂(2) = 3`). -/
theorem C2Carlitz_prime_iff_eq_two {q : Nat} (hp : IsPrime q) :
    IsPrime (C2Carlitz q) ↔ q = 2 :=
  ⟨C2Carlitz_prime_only_q_two hp, by
    intro h
    subst h
    exact three_is_prime⟩

/-- **Headline (standard reading).** For every prime `q`, if `C₂(q) = q² + 1`
is prime then `q = 2`: the `n = 2` instance of conjecture 00000000122 admits at
most one prime `q`, so there are not infinitely many. The conjecture is FALSE. -/
theorem tlmc122_disproof_standard : ∀ q : Nat, IsPrime q → IsPrime (C2 q) → q = 2 :=
  fun _ hp hc => C2_prime_only_q_two hp hc

/-- **Headline (Carlitz reading).** Same collapse for the Carlitz `q`-Catalan
`C₂(q) = q + 1`. -/
theorem tlmc122_disproof_carlitz : ∀ q : Nat, IsPrime q → IsPrime (C2Carlitz q) → q = 2 :=
  fun _ hp hc => C2Carlitz_prime_only_q_two hp hc
