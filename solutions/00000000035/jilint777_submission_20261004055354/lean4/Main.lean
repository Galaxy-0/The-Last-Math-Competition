/-!
# Conjecture 00000000035: monochromatic Schur triples with `xy + 1` prime

Conjecture: there exists `N` such that every 2-coloring of `[N] = {1, …, N}`
contains a monochromatic Schur triple `(x, y, z)`, `x + y = z`, with `xy + 1`
prime.  We prove it with `N = 17`, even requiring `x < y`
(`conjecture_00000000035`).  The bound is sharp for `x < y`: the coloring
`0010101110110101` of `[16]` avoids all such triples (`sixteen_avoids`).

The proof is a case analysis on colors (a DPLL refutation tree with 11
branchings over the 31 relevant triples), checked by Lean.  Primality is the
standard definition `Prime`, with a verified Boolean checker.
-/

namespace SchurPrime

/-- Standard primality. -/
def Prime (n : Nat) : Prop := 2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n

/-- Trial-division checker. -/
def primeCheck (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all fun d => decide (d < 2) || decide (n % d ≠ 0)

theorem prime_of_check (n : Nat) (h : primeCheck n = true) : Prime n := by
  simp only [primeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at h
  obtain ⟨h2, hall⟩ := h
  refine ⟨h2, fun d hd => ?_⟩
  have hdn : d ≤ n := Nat.le_of_dvd (by omega) hd
  by_cases hdeq : d = n
  · exact Or.inr hdeq
  · rcases hall d (by omega) with h0 | h0
    · by_cases hd0 : d = 0
      · subst hd0; rw [Nat.zero_dvd] at hd; omega
      · left; omega
    · exact absurd (Nat.mod_eq_zero_of_dvd hd) h0

theorem check_of_prime (n : Nat) (h : Prime n) : primeCheck n = true := by
  simp only [primeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true]
  refine ⟨h.1, fun d hd => ?_⟩
  by_cases hd2 : d < 2
  · exact Or.inl hd2
  · right
    intro hmod
    rcases h.2 d (Nat.dvd_of_mod_eq_zero hmod) with h1 | h1 <;> omega

/-- `(x, y, z)` is a Schur triple in `[N]` with `x < y` and `xy + 1` prime. -/
def SchurPrimeTriple (N x y z : Nat) : Prop :=
  1 ≤ x ∧ x < y ∧ x + y = z ∧ z ≤ N ∧ Prime (x * y + 1)

theorem sp (x y z : Nat) (h1 : 1 ≤ x) (h2 : x < y) (h3 : x + y = z) (h4 : z ≤ 17)
    (hp : primeCheck (x * y + 1) = true) : SchurPrimeTriple 17 x y z :=
  ⟨h1, h2, h3, h4, prime_of_check _ hp⟩

/-! ## Propagation lemmas for two colors -/

theorem clash : ∀ {a b d v : Bool}, ¬(a = b ∧ b = d) → a = v → b = v → d = v → False := by
  decide
theorem force_z : ∀ {a b d v : Bool}, ¬(a = b ∧ b = d) → a = v → b = v → d = !v := by
  decide
theorem force_y : ∀ {a b d v : Bool}, ¬(a = b ∧ b = d) → a = v → d = v → b = !v := by
  decide
theorem force_x : ∀ {a b d v : Bool}, ¬(a = b ∧ b = d) → b = v → d = v → a = !v := by
  decide

/-! ## Main theorem -/

/-- Every 2-coloring of `[17]` (given as any `c : Nat → Bool`; only the values on
`1, …, 17` matter) has a monochromatic Schur triple with `x < y` and `xy + 1` prime. -/
theorem schur_17 (c : Nat → Bool) :
    ∃ x y z, SchurPrimeTriple 17 x y z ∧ c x = c y ∧ c y = c z := by
  apply Classical.byContradiction
  intro hno
  have t0 : ¬(c 1 = c 2 ∧ c 2 = c 3) := fun hh => hno ⟨1, 2, 3, sp 1 2 3 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t1 : ¬(c 1 = c 4 ∧ c 4 = c 5) := fun hh => hno ⟨1, 4, 5, sp 1 4 5 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t2 : ¬(c 1 = c 6 ∧ c 6 = c 7) := fun hh => hno ⟨1, 6, 7, sp 1 6 7 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t3 : ¬(c 1 = c 10 ∧ c 10 = c 11) := fun hh => hno ⟨1, 10, 11, sp 1 10 11 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t4 : ¬(c 1 = c 12 ∧ c 12 = c 13) := fun hh => hno ⟨1, 12, 13, sp 1 12 13 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t5 : ¬(c 1 = c 16 ∧ c 16 = c 17) := fun hh => hno ⟨1, 16, 17, sp 1 16 17 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t6 : ¬(c 2 = c 3 ∧ c 3 = c 5) := fun hh => hno ⟨2, 3, 5, sp 2 3 5 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t7 : ¬(c 2 = c 5 ∧ c 5 = c 7) := fun hh => hno ⟨2, 5, 7, sp 2 5 7 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t8 : ¬(c 2 = c 6 ∧ c 6 = c 8) := fun hh => hno ⟨2, 6, 8, sp 2 6 8 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t9 : ¬(c 2 = c 8 ∧ c 8 = c 10) := fun hh => hno ⟨2, 8, 10, sp 2 8 10 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t10 : ¬(c 2 = c 9 ∧ c 9 = c 11) := fun hh => hno ⟨2, 9, 11, sp 2 9 11 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t11 : ¬(c 2 = c 11 ∧ c 11 = c 13) := fun hh => hno ⟨2, 11, 13, sp 2 11 13 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t12 : ¬(c 2 = c 14 ∧ c 14 = c 16) := fun hh => hno ⟨2, 14, 16, sp 2 14 16 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t13 : ¬(c 2 = c 15 ∧ c 15 = c 17) := fun hh => hno ⟨2, 15, 17, sp 2 15 17 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t14 : ¬(c 3 = c 4 ∧ c 4 = c 7) := fun hh => hno ⟨3, 4, 7, sp 3 4 7 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t15 : ¬(c 3 = c 6 ∧ c 6 = c 9) := fun hh => hno ⟨3, 6, 9, sp 3 6 9 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t16 : ¬(c 3 = c 10 ∧ c 10 = c 13) := fun hh => hno ⟨3, 10, 13, sp 3 10 13 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t17 : ¬(c 3 = c 12 ∧ c 12 = c 15) := fun hh => hno ⟨3, 12, 15, sp 3 12 15 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t18 : ¬(c 3 = c 14 ∧ c 14 = c 17) := fun hh => hno ⟨3, 14, 17, sp 3 14 17 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t19 : ¬(c 4 = c 7 ∧ c 7 = c 11) := fun hh => hno ⟨4, 7, 11, sp 4 7 11 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t20 : ¬(c 4 = c 9 ∧ c 9 = c 13) := fun hh => hno ⟨4, 9, 13, sp 4 9 13 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t21 : ¬(c 4 = c 10 ∧ c 10 = c 14) := fun hh => hno ⟨4, 10, 14, sp 4 10 14 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t22 : ¬(c 4 = c 13 ∧ c 13 = c 17) := fun hh => hno ⟨4, 13, 17, sp 4 13 17 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t23 : ¬(c 5 = c 6 ∧ c 6 = c 11) := fun hh => hno ⟨5, 6, 11, sp 5 6 11 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t24 : ¬(c 5 = c 8 ∧ c 8 = c 13) := fun hh => hno ⟨5, 8, 13, sp 5 8 13 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t25 : ¬(c 5 = c 12 ∧ c 12 = c 17) := fun hh => hno ⟨5, 12, 17, sp 5 12 17 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t26 : ¬(c 6 = c 7 ∧ c 7 = c 13) := fun hh => hno ⟨6, 7, 13, sp 6 7 13 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t27 : ¬(c 6 = c 10 ∧ c 10 = c 16) := fun hh => hno ⟨6, 10, 16, sp 6 10 16 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t28 : ¬(c 6 = c 11 ∧ c 11 = c 17) := fun hh => hno ⟨6, 11, 17, sp 6 11 17 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t29 : ¬(c 7 = c 10 ∧ c 10 = c 17) := fun hh => hno ⟨7, 10, 17, sp 7 10 17 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  have t30 : ¬(c 8 = c 9 ∧ c 9 = c 17) := fun hh => hno ⟨8, 9, 17, sp 8 9 17 (by decide) (by decide) rfl (by decide) (by decide), hh.1, hh.2⟩
  cases h2 : c 2
  · skip
    cases h17 : c 17
    · skip
      have h15 : c 15 = true := force_y t13 h2 h17
      cases h3 : c 3
      · skip
        have h1 : c 1 = true := force_x t0 h2 h3
        have h5 : c 5 = true := force_z t6 h2 h3
        have h4 : c 4 = false := force_y t1 h1 h5
        have h7 : c 7 = true := force_z t14 h3 h4
        have h6 : c 6 = false := force_y t2 h1 h7
        have h8 : c 8 = true := force_z t8 h2 h6
        have h9 : c 9 = true := force_z t15 h3 h6
        have h14 : c 14 = true := force_y t18 h3 h17
        have h13 : c 13 = true := force_y t22 h4 h17
        exact clash t24 h5 h8 h13
      · skip
        have h12 : c 12 = false := force_y t17 h3 h15
        have h5 : c 5 = true := force_x t25 h12 h17
        cases h6 : c 6
        · skip
          have h8 : c 8 = true := force_z t8 h2 h6
          have h13 : c 13 = false := force_z t24 h5 h8
          have h1 : c 1 = true := force_x t4 h12 h13
          have h4 : c 4 = false := force_y t1 h1 h5
          exact clash t22 h4 h13 h17
        · skip
          have h9 : c 9 = false := force_z t15 h3 h6
          have h11 : c 11 = true := force_z t10 h2 h9
          exact clash t23 h5 h6 h11
    · skip
      cases h3 : c 3
      · skip
        have h1 : c 1 = true := force_x t0 h2 h3
        have h16 : c 16 = false := force_y t5 h1 h17
        have h5 : c 5 = true := force_z t6 h2 h3
        have h4 : c 4 = false := force_y t1 h1 h5
        have h14 : c 14 = true := force_y t12 h2 h16
        have h7 : c 7 = true := force_z t14 h3 h4
        have h6 : c 6 = false := force_y t2 h1 h7
        have h8 : c 8 = true := force_z t8 h2 h6
        have h9 : c 9 = true := force_z t15 h3 h6
        exact clash t30 h8 h9 h17
      · skip
        have h14 : c 14 = false := force_y t18 h3 h17
        have h16 : c 16 = true := force_z t12 h2 h14
        have h1 : c 1 = false := force_x t5 h16 h17
        cases h6 : c 6
        · skip
          have h7 : c 7 = true := force_z t2 h1 h6
          have h8 : c 8 = true := force_z t8 h2 h6
          have h4 : c 4 = false := force_y t14 h3 h7
          have h5 : c 5 = true := force_z t1 h1 h4
          have h10 : c 10 = true := force_y t21 h4 h14
          exact clash t29 h7 h10 h17
        · skip
          have h9 : c 9 = false := force_z t15 h3 h6
          have h11 : c 11 = true := force_z t10 h2 h9
          exact clash t28 h6 h11 h17
  · skip
    cases h17 : c 17
    · skip
      cases h3 : c 3
      · skip
        have h14 : c 14 = true := force_y t18 h3 h17
        have h16 : c 16 = false := force_z t12 h2 h14
        have h1 : c 1 = true := force_x t5 h16 h17
        cases h6 : c 6
        · skip
          have h9 : c 9 = true := force_z t15 h3 h6
          have h11 : c 11 = false := force_z t10 h2 h9
          exact clash t28 h6 h11 h17
        · skip
          have h7 : c 7 = false := force_z t2 h1 h6
          have h8 : c 8 = false := force_z t8 h2 h6
          have h4 : c 4 = true := force_y t14 h3 h7
          have h5 : c 5 = false := force_z t1 h1 h4
          have h10 : c 10 = false := force_y t21 h4 h14
          exact clash t29 h7 h10 h17
      · skip
        have h1 : c 1 = false := force_x t0 h2 h3
        have h16 : c 16 = true := force_y t5 h1 h17
        have h5 : c 5 = false := force_z t6 h2 h3
        have h4 : c 4 = true := force_y t1 h1 h5
        have h14 : c 14 = false := force_y t12 h2 h16
        have h7 : c 7 = false := force_z t14 h3 h4
        have h6 : c 6 = true := force_y t2 h1 h7
        have h8 : c 8 = false := force_z t8 h2 h6
        have h9 : c 9 = false := force_z t15 h3 h6
        exact clash t30 h8 h9 h17
    · skip
      have h15 : c 15 = false := force_y t13 h2 h17
      cases h3 : c 3
      · skip
        have h12 : c 12 = true := force_y t17 h3 h15
        have h5 : c 5 = false := force_x t25 h12 h17
        cases h6 : c 6
        · skip
          have h9 : c 9 = true := force_z t15 h3 h6
          have h11 : c 11 = false := force_z t10 h2 h9
          exact clash t23 h5 h6 h11
        · skip
          have h8 : c 8 = false := force_z t8 h2 h6
          have h13 : c 13 = true := force_z t24 h5 h8
          have h1 : c 1 = false := force_x t4 h12 h13
          have h4 : c 4 = true := force_y t1 h1 h5
          exact clash t22 h4 h13 h17
      · skip
        have h1 : c 1 = false := force_x t0 h2 h3
        have h5 : c 5 = false := force_z t6 h2 h3
        have h4 : c 4 = true := force_y t1 h1 h5
        have h7 : c 7 = false := force_z t14 h3 h4
        have h6 : c 6 = true := force_y t2 h1 h7
        have h8 : c 8 = false := force_z t8 h2 h6
        have h9 : c 9 = false := force_z t15 h3 h6
        have h14 : c 14 = false := force_y t18 h3 h17
        have h13 : c 13 = false := force_y t22 h4 h17
        exact clash t24 h5 h8 h13

/-- The conjecture: there is `N` such that every 2-coloring of `[N]` contains a
monochromatic Schur triple with `xy + 1` prime.  (The `k` in `N(k)` does not
occur in the statement, so `N = 17` works for every `k`.) -/
theorem conjecture_00000000035 :
    ∀ _k : Nat, ∃ N, ∀ c : Nat → Bool,
      ∃ x y z, SchurPrimeTriple N x y z ∧ c x = c y ∧ c y = c z :=
  fun _ => ⟨17, schur_17⟩

/-- The same with `x ≤ y` allowed (the weaker requirement on the triple). -/
theorem conjecture_00000000035_le :
    ∃ N, ∀ c : Nat → Bool, ∃ x y z, 1 ≤ x ∧ x ≤ y ∧ x + y = z ∧ z ≤ N ∧
      Prime (x * y + 1) ∧ c x = c y ∧ c y = c z := by
  refine ⟨17, fun c => ?_⟩
  obtain ⟨x, y, z, ⟨h1, h2, h3, h4, hp⟩, hc⟩ := schur_17 c
  exact ⟨x, y, z, h1, Nat.le_of_lt h2, h3, h4, hp, hc⟩

/-! ## Sharpness for `x < y`: a good coloring of `[16]` -/

/-- Colors of `1, …, 16`: `0010101110110101`. -/
def good16 (n : Nat) : Bool := "0010101110110101".toList.getD (n - 1) '0' == '1'

theorem good16_check :
    ∀ x, x < 17 → ∀ y, y < 17 →
      (1 ≤ x ∧ x < y ∧ x + y ≤ 16 ∧ primeCheck (x * y + 1) = true) →
        ¬(good16 x = good16 y ∧ good16 y = good16 (x + y)) := by
  decide

theorem sixteen_avoids :
    ∃ c : Nat → Bool, ∀ x y z, SchurPrimeTriple 16 x y z → ¬(c x = c y ∧ c y = c z) := by
  refine ⟨good16, fun x y z ⟨h1, h2, h3, h4, hp⟩ => ?_⟩
  subst h3
  exact good16_check x (by omega) y (by omega) ⟨h1, h2, h4, check_of_prime _ hp⟩

end SchurPrime

#print axioms SchurPrime.schur_17
#print axioms SchurPrime.conjecture_00000000035
#print axioms SchurPrime.conjecture_00000000035_le
#print axioms SchurPrime.sixteen_avoids
