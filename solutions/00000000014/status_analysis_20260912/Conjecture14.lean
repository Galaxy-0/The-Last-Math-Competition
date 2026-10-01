/-
  Conjecture 14 (TLMC-00000000014)
  ================================

  Statement:
    There exist infinitely many pairs (p, m), with p prime and m a positive
    integer, such that |p - m^2| <= (log p)^2.

  Status: OPEN (Landau-class).  See `main.tex` in this folder for the full
  status analysis.  No unconditional proof is known: the conjecture asks for
  primes in an explicit x^{1/2+o(1)}-thin set, while the thinnest explicit
  sets known to contain infinitely many primes are of size x^{2/3}
  (Heath-Brown).  It is implied by Landau's fourth problem (infinitely many
  primes of the form m^2 + 1).

  What IS proved in this file (machine-checked, no `sorry`):

    `cramerInterval_implies_conjecture14` : a Cramer-type prime-gap
    hypothesis in interval form — every sufficiently large interval
    [x, x + (3/2)(log x)^2] contains a prime — implies Conjecture 14.  In
    fact every sufficiently large m then admits a prime p with
    |p - m^2| <= (log p)^2.

  Toolchain: leanprover/lean4:v4.31.0, Mathlib v4.31.0.
-/

import Mathlib

/-- The faithful formalization of Conjecture TLMC-00000000014:
    infinitely many pairs (p, m), p prime, 1 <= m, with
    |p - m^2| <= (log p)^2.  (Unboundedness in p gives infinitely many
    distinct pairs, since each qualifying p has at least one witness m.) -/
def conjecture14 : Prop :=
  ∀ B : ℕ, ∃ p m : ℕ, B ≤ p ∧ p.Prime ∧ 1 ≤ m ∧
    |(p : ℝ) - (m : ℝ) ^ 2| ≤ (Real.log (p : ℝ)) ^ 2

/-- Cramér-type hypothesis (interval form): there is a threshold N such that
    every real x >= N admits a prime p in [x, x + (3/2)·(log x)^2].

    This follows from the gap form "p_{n+1} - p_n <= (3/2)(log p_n)^2
    eventually" by an elementary argument (see `main.tex`, Lemma 3.1).  Note
    Cramér's conjecture (limsup of gaps over log^2 equals 1) implies the gap
    form with any constant > 1. -/
def cramerInterval : Prop :=
  ∃ N : ℕ, ∀ x : ℝ, (N : ℝ) ≤ x →
    ∃ p : ℕ, x ≤ (p : ℝ) ∧ p.Prime ∧ (p : ℝ) ≤ x + (3 / 2) * (Real.log x) ^ 2

/-- Main conditional theorem: the Cramér-type interval hypothesis implies
    Conjecture 14. -/
theorem cramerInterval_implies_conjecture14 (H : cramerInterval) : conjecture14 := by
  obtain ⟨N, H⟩ := H
  -- Threshold with log m ≥ 8: take m ≥ ⌈exp 8⌉ + 1.
  set M : ℕ := max (max (Nat.ceil (Real.exp 8) + 1) 24) (max N 2) with hMdef
  intro B
  -- choose m above the threshold and above 2B + 2
  set m : ℕ := M + (2 * B + 2) with hmdef
  have hmM : M ≤ m := by omega
  have hexp8 : (Real.exp 8 : ℝ) ≤ (Nat.ceil (Real.exp 8) : ℝ) := Nat.le_ceil _
  have hceilm : (Nat.ceil (Real.exp 8) : ℕ) ≤ m := by omega
  have hMlog : (Nat.ceil (Real.exp 8) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hceilm
  have hm24 : (24 : ℝ) ≤ (m : ℝ) := by
    have h : (24 : ℕ) ≤ m := by omega
    exact_mod_cast h
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by linarith
  have hmN : (N : ℝ) ≤ (m : ℝ) := by
    have h : N ≤ m := by omega
    exact_mod_cast h
  set L : ℝ := Real.log (m : ℝ) with hLdef
  have hL8 : (8 : ℝ) ≤ L := by
    have h1 : Real.log (Real.exp 8) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (Real.exp_pos 8) (le_trans hexp8 hMlog)
    rw [Real.log_exp] at h1
    linarith
  -- L ≤ 2·√m  (since log t ≤ t and log m = 2·log √m)
  have hLsqrt : L = 2 * Real.log (Real.sqrt (m : ℝ)) := by
    rw [hLdef, Real.log_sqrt (by positivity)]
    ring
  have hlogsq : Real.log (Real.sqrt (m : ℝ)) ≤ Real.sqrt (m : ℝ) :=
    Real.log_le_self (by positivity)
  have hL2 : L ≤ 2 * Real.sqrt (m : ℝ) := by rw [hLsqrt]; linarith
  have hsqrtsqrt : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hLsq : L ^ 2 ≤ 4 * (m : ℝ) := by
    have h1 : L * L ≤ (2 * Real.sqrt (m : ℝ)) * (2 * Real.sqrt (m : ℝ)) :=
      mul_le_mul hL2 hL2 (by linarith) (by positivity)
    nlinarith [hsqrtsqrt]
  -- hence 3·L^2 ≤ m^2 / 2
  have h3L : 3 * L ^ 2 ≤ (m : ℝ) ^ 2 / 2 := by
    have h1 : 24 * (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [hm24, hm2]
    have h2 : 3 * L ^ 2 ≤ 12 * (m : ℝ) := by nlinarith [hLsq]
    linarith
  -- the search point x = m^2 - 3·L^2
  set x : ℝ := (m : ℝ) ^ 2 - 3 * L ^ 2 with hxdef
  have hxhalf : (m : ℝ) ^ 2 / 2 ≤ x := by rw [hxdef]; linarith
  have hxpos : (0 : ℝ) < x := by
    have h : (0 : ℝ) < (m : ℝ) ^ 2 / 2 := by positivity
    linarith
  have hxge1 : (1 : ℝ) ≤ x := by
    have h : (2 : ℝ) ≤ (m : ℝ) ^ 2 / 2 := by nlinarith [hm2]
    linarith
  have hxN : (N : ℝ) ≤ x := by
    have h1 : (m : ℝ) ≤ (m : ℝ) ^ 2 / 2 := by nlinarith [hm2]
    linarith
  obtain ⟨p, hplow, hprime, hpup⟩ := H x hxN
  -- log x ≤ 2L, so p ≤ m^2 + 3·L^2
  have hlogm2 : Real.log ((m : ℝ) ^ 2) = 2 * L := by
    have h1 : (m : ℝ) ^ 2 = (m : ℝ) * (m : ℝ) := by ring
    rw [h1, Real.log_mul (by positivity) (by positivity), hLdef]
    ring
  have hLnn : (0 : ℝ) ≤ L ^ 2 := sq_nonneg L
  have hleq : x ≤ (m : ℝ) ^ 2 := by rw [hxdef]; linarith [hLnn]
  have hlogx : Real.log x ≤ 2 * L := by
    have h1 : Real.log x ≤ Real.log ((m : ℝ) ^ 2) := Real.log_le_log hxpos hleq
    rw [hlogm2] at h1
    linarith
  have hlogxnonneg : (0 : ℝ) ≤ Real.log x :=
    Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)
  have hpup2 : (p : ℝ) ≤ (m : ℝ) ^ 2 + 3 * L ^ 2 := by
    have hs : (Real.log x) ^ 2 ≤ (2 * L) ^ 2 := by
      have hlow : -(2 * L) ≤ Real.log x := by linarith
      exact sq_le_sq' hlow hlogx
    have h1 : (3 / 2 : ℝ) * (Real.log x) ^ 2 ≤ 6 * L ^ 2 := by
      have h : (3 / 2 : ℝ) * (2 * L) ^ 2 = 6 * L ^ 2 := by ring
      nlinarith [hs]
    linarith [hpup, hxdef, h1]
  have hplow2 : (m : ℝ) ^ 2 - 3 * L ^ 2 ≤ (p : ℝ) := by
    rw [← hxdef]; exact hplow
  have hpgehalf : (m : ℝ) ^ 2 / 2 ≤ (p : ℝ) := by linarith
  -- log p ≥ 2L - 2
  have hlogp : 2 * L - 2 ≤ Real.log (p : ℝ) := by
    have h1 : Real.log ((m : ℝ) ^ 2 / 2) ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by positivity) hpgehalf
    rw [Real.log_div (ne_of_gt (by positivity)) (two_ne_zero)] at h1
    rw [hlogm2] at h1
    have h2 : Real.log (2 : ℝ) ≤ (2 : ℝ) := Real.log_le_self (by norm_num)
    linarith
  -- 3·L^2 ≤ (2L - 2)^2 ≤ (log p)^2
  have hkey : 3 * L ^ 2 ≤ (2 * L - 2) ^ 2 := by
    have h1 : (0 : ℝ) ≤ L * (L - 8) := mul_nonneg (by linarith) (by linarith)
    have h2 : (2 * L - 2) ^ 2 = 3 * L ^ 2 + (L * (L - 8) + 4) := by ring
    linarith
  have hsqmon : (0 : ℝ) ≤ 2 * L - 2 := by linarith
  have hfinal3 : 3 * L ^ 2 ≤ (Real.log (p : ℝ)) ^ 2 := by
    have hlow : -(Real.log (p : ℝ)) ≤ 2 * L - 2 := by linarith
    exact le_trans hkey (sq_le_sq' hlow hlogp)
  have habs : |(p : ℝ) - (m : ℝ) ^ 2| ≤ 3 * L ^ 2 := by
    apply abs_le.mpr
    constructor
    · linarith
    · linarith
  -- p ≥ B
  have hpB : (B : ℝ) ≤ (p : ℝ) := by
    have h1 : (m : ℝ) ≤ (m : ℝ) ^ 2 / 2 := by nlinarith [hm2]
    have h2 : (2 * (B : ℝ) + 2) ≤ (m : ℝ) := by
      have h : 2 * B + 2 ≤ m := by omega
      exact_mod_cast h
    linarith
  refine ⟨p, m, ?_, hprime, ?_, ?_⟩
  · exact_mod_cast hpB
  · have h : (1 : ℕ) ≤ m := by omega
    exact h
  · exact le_trans habs hfinal3
