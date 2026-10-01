/-
  TLMC #1186 DISPROOF (standalone)
-/

import Mathlib

namespace TLMC1186

/-! ## #1186 — minimal orders of nonabelian simple groups -/

/-- The set of prime divisors of `n`. -/
def primeDivisors (n : ℕ) : Finset ℕ := (Nat.divisors n).filter Nat.Prime

/-- Number of distinct prime factors. -/
def omega (n : ℕ) : ℕ := (primeDivisors n).card

/-- `n` is the order of some nonabelian finite simple group. -/
def IsNonabelianSimpleOrder (n : ℕ) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Fintype G),
    IsSimpleGroup G ∧ (¬ ∀ a b : G, a * b = b * a) ∧ Fintype.card G = n

/-- m(k): minimal order of a nonabelian simple group with exactly k
    distinct prime factors. -/
noncomputable def m (k : ℕ) : ℕ := sInf {n | IsNonabelianSimpleOrder n ∧ omega n = k}

theorem prime_eq_of_dvd_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hd : p ∣ q) :
    p = q := by
  rcases (Nat.dvd_prime hq).mp hd with h | h
  · have h2 := hp.two_le
    omega
  · exact h

theorem dvd_504 {p : ℕ} (hp : p.Prime) (hd : p ∣ 504) : p = 2 ∨ p = 3 ∨ p = 7 := by
  have e1 : (504:ℕ) = 2 * 252 := by norm_num
  have e2 : (252:ℕ) = 2 * 126 := by norm_num
  have e3 : (126:ℕ) = 2 * 63 := by norm_num
  have e4 : (63:ℕ) = 3 * 21 := by norm_num
  have e5 : (21:ℕ) = 3 * 7 := by norm_num
  rcases (Nat.Prime.dvd_mul hp).mp (e1 ▸ hd) with h1 | h1
  · left; exact prime_eq_of_dvd_prime hp (by decide : Nat.Prime 2) h1
  · rcases (Nat.Prime.dvd_mul hp).mp (e2 ▸ h1) with h2 | h2
    · left; exact prime_eq_of_dvd_prime hp (by decide : Nat.Prime 2) h2
    · rcases (Nat.Prime.dvd_mul hp).mp (e3 ▸ h2) with h3 | h3
      · left; exact prime_eq_of_dvd_prime hp (by decide : Nat.Prime 2) h3
      · rcases (Nat.Prime.dvd_mul hp).mp (e4 ▸ h3) with h4 | h4
        · right; left; exact prime_eq_of_dvd_prime hp (by decide : Nat.Prime 3) h4
        · rcases (Nat.Prime.dvd_mul hp).mp (e5 ▸ h4) with h5 | h5
          · right; left; exact prime_eq_of_dvd_prime hp (by decide : Nat.Prime 3) h5
          · right; right; exact prime_eq_of_dvd_prime hp (by decide : Nat.Prime 7) h5

theorem dvd_660 {p : ℕ} (hp : p.Prime) (hd : p ∣ 660) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 11 := by
  have e1 : (660:ℕ) = 2 * 330 := by norm_num
  have e2 : (330:ℕ) = 2 * 165 := by norm_num
  have e3 : (165:ℕ) = 3 * 55 := by norm_num
  have e4 : (55:ℕ) = 5 * 11 := by norm_num
  have h5 : (5:ℕ).Prime := by decide
  have h11 : (11:ℕ).Prime := by decide
  rcases (Nat.Prime.dvd_mul hp).mp (e1 ▸ hd) with h1 | h1
  · left; exact prime_eq_of_dvd_prime hp (by decide : Nat.Prime 2) h1
  · rcases (Nat.Prime.dvd_mul hp).mp (e2 ▸ h1) with h2 | h2
    · left; exact prime_eq_of_dvd_prime hp (by decide : Nat.Prime 2) h2
    · rcases (Nat.Prime.dvd_mul hp).mp (e3 ▸ h2) with h3 | h3
      · right; left; exact prime_eq_of_dvd_prime hp (by decide : Nat.Prime 3) h3
      · rcases (Nat.Prime.dvd_mul hp).mp (e4 ▸ h3) with h4 | h4
        · right; right; left; exact prime_eq_of_dvd_prime hp h5 h4
        · right; right; right; exact prime_eq_of_dvd_prime hp h11 h4

theorem primeDivisors_504 : primeDivisors 504 = {2, 3, 7} := by
  ext p
  simp only [primeDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hd, _⟩, hp⟩
    rcases dvd_504 hp hd with h | h | h <;> simp [h]
  · intro hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩

theorem primeDivisors_660 : primeDivisors 660 = {2, 3, 5, 11} := by
  ext p
  simp only [primeDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hd, _⟩, hp⟩
    rcases dvd_660 hp hd with h | h | h | h <;> simp [h]
  · intro hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩

theorem omega_504 : omega 504 = 3 := by
  rw [omega, primeDivisors_504]; decide

theorem omega_660 : omega 660 = 4 := by
  rw [omega, primeDivisors_660]; decide

theorem m4_ne_504 : m 4 ≠ 504 := by
  intro h
  have hs : {n | IsNonabelianSimpleOrder n ∧ omega n = 4}.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have h' : m 4 = 0 := by
      unfold m
      rw [hc]
      exact Nat.sInf_empty
    omega
  have mem := Nat.sInf_mem hs
  have h' : sInf {n | IsNonabelianSimpleOrder n ∧ omega n = 4} = 504 := h
  rw [h'] at mem
  obtain ⟨_, homega⟩ := mem
  rw [omega_504] at homega
  exact absurd homega (by decide)

theorem m5_ne_660 : m 5 ≠ 660 := by
  intro h
  have hs : {n | IsNonabelianSimpleOrder n ∧ omega n = 5}.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have h' : m 5 = 0 := by
      unfold m
      rw [hc]
      exact Nat.sInf_empty
    omega
  have mem := Nat.sInf_mem hs
  have h' : sInf {n | IsNonabelianSimpleOrder n ∧ omega n = 5} = 660 := h
  rw [h'] at mem
  obtain ⟨_, homega⟩ := mem
  rw [omega_660] at homega
  exact absurd homega (by decide)

/-- The value claims of Conjecture #1186. -/
def conjecture1186_values : Prop := m 3 = 60 ∧ m 4 = 504 ∧ m 5 = 660

theorem conjecture1186_false : ¬ conjecture1186_values := by
  rintro ⟨_, h4, _⟩
  exact m4_ne_504 h4


end TLMC1186
