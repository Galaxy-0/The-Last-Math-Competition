/-
  Conjecture 1206 (TLMC-00000001206) — the nim-sum period law
  ===========================================================

  Statement (conjectures/00000001206.md):
    "Nim-sum closure of Sprague–Grundy functions: the period of the
     pointwise nim-sum of two periodic Grundy sequences divides the lcm
     of the two periods."
    (Sprague–Grundy 函数的 nim-和封闭：两周期 Grundy 序列的逐点 nim-和的
     周期为两周期之 lcm 的因子。)

  We prove the statement for ALL ℕ-valued periodic sequences (Grundy
  sequences are ℕ-valued, so the conjecture follows a fortiori), and in
  fact for an arbitrary binary operation `op` in place of the nim-sum:
  only periodicity is used.

  Machine-checked, no `sorry`.
  Toolchain: leanprover/lean4:v4.31.0, Mathlib v4.31.0.
-/

import Mathlib

namespace TLMC1206

/-! ### Definitions -/

/-- `p` is a *period* of `f : ℕ → ℕ` if `f (n + p) = f n` for all `n`.
    A period in the sense of the conjecture is positive. -/
def IsPeriod (f : ℕ → ℕ) (p : ℕ) : Prop := ∀ n, f (n + p) = f n

/-- The *minimal period* of `f`: the least positive period, when one exists. -/
noncomputable def minPeriod (f : ℕ → ℕ) : ℕ := sInf {p | 0 < p ∧ IsPeriod f p}

/-! ### Step 1: multiples of a period are periods -/

theorem IsPeriod.mul {f : ℕ → ℕ} {p : ℕ} (h : IsPeriod f p) (k : ℕ) :
    IsPeriod f (k * p) := by
  induction k with
  | zero => intro n; simp
  | succ k ih =>
    intro n
    have h1 : (k + 1) * p = k * p + p := Nat.succ_mul k p
    rw [h1]
    have h2 := h (n + k * p)
    have h3 := ih n
    calc f (n + (k * p + p)) = f ((n + k * p) + p) := by congr 1; omega
      _ = f (n + k * p) := h2
      _ = f n := h3

/-! ### Basic facts about the minimal period -/

theorem minPeriod_spec (f : ℕ → ℕ) (h : ∃ p, 0 < p ∧ IsPeriod f p) :
    0 < minPeriod f ∧ IsPeriod f (minPeriod f) := by
  obtain ⟨p, hp, hf⟩ := h
  have hne : {p : ℕ | 0 < p ∧ IsPeriod f p}.Nonempty := ⟨p, hp, hf⟩
  exact Nat.sInf_mem hne

/-! ### Step 3: the minimal period divides every period -/

theorem minPeriod_dvd {f : ℕ → ℕ} {q : ℕ} (hq : IsPeriod f q)
    (h : ∃ p, 0 < p ∧ IsPeriod f p) : minPeriod f ∣ q := by
  obtain ⟨hpos, hper⟩ := minPeriod_spec f h
  set π := minPeriod f with hπ
  have hmod : q % π = 0 ∨ (0 < q % π ∧ IsPeriod f (q % π)) := by
    by_cases hz : q % π = 0
    · exact Or.inl hz
    · refine Or.inr ⟨by omega, ?_⟩
      intro n
      have hstrip := hper.mul (q / π)
      have key : n + q % π + (q / π) * π = n + q := by
        rw [Nat.mul_comm (q / π) π]
        have hdm := Nat.div_add_mod q π
        omega
      calc f (n + q % π) = f (n + q % π + (q / π) * π) := (hstrip (n + q % π)).symm
        _ = f (n + q) := by rw [key]
        _ = f n := hq n
  rcases hmod with hz | ⟨hlt, hmodp⟩
  · exact Nat.dvd_of_mod_eq_zero hz
  · exfalso
    have hle : π ≤ q % π := Nat.sInf_le ⟨hlt, hmodp⟩
    have : q % π < π := Nat.mod_lt _ hpos
    omega

/-! ### Step 2 and the theorem: the lcm of two periods is a period of any
     pointwise lift, so the minimal period of the lift divides the lcm.
     The proof works for an ARBITRARY binary operation `op`. -/

theorem pointwise_period_dvd (op : ℕ → ℕ → ℕ) (g₁ g₂ : ℕ → ℕ) {p₁ p₂ : ℕ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (h₁ : IsPeriod g₁ p₁) (h₂ : IsPeriod g₂ p₂) :
    minPeriod (fun n => op (g₁ n) (g₂ n)) ∣ Nat.lcm p₁ p₂ := by
  -- the lcm is a period of the pointwise lift
  have hlcm : IsPeriod (fun n => op (g₁ n) (g₂ n)) (Nat.lcm p₁ p₂) := by
    obtain ⟨a, ha⟩ := Nat.dvd_lcm_left p₁ p₂
    obtain ⟨b, hb⟩ := Nat.dvd_lcm_right p₁ p₂
    have ha' := h₁.mul a
    have hb' := h₂.mul b
    intro n
    show op (g₁ (n + Nat.lcm p₁ p₂)) (g₂ (n + Nat.lcm p₁ p₂)) = op (g₁ n) (g₂ n)
    have e1 : g₁ (n + Nat.lcm p₁ p₂) = g₁ n := by
      rw [ha, Nat.mul_comm p₁ a, ha' n]
    have e2 : g₂ (n + Nat.lcm p₁ p₂) = g₂ n := by
      rw [hb, Nat.mul_comm p₂ b, hb' n]
    rw [e1, e2]
  -- the minimal period exists (the lcm is a positive period) and divides it
  exact minPeriod_dvd hlcm ⟨Nat.lcm p₁ p₂, Nat.lcm_pos hp₁ hp₂, hlcm⟩

/-! ### The nim-sum specialization (TLMC-00000001206) -/

/-- **Theorem (nim-sum period law).** If `p₁` and `p₂` are periods of the
    ℕ-valued sequences `g₁` and `g₂`, then the minimal period of their
    pointwise nim-sum divides `lcm p₁ p₂`. -/
theorem nimsum_period (g₁ g₂ : ℕ → ℕ) {p₁ p₂ : ℕ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (h₁ : IsPeriod g₁ p₁) (h₂ : IsPeriod g₂ p₂) :
    minPeriod (fun n => g₁ n ^^^ g₂ n) ∣ Nat.lcm p₁ p₂ :=
  pointwise_period_dvd Nat.xor g₁ g₂ hp₁ hp₂ h₁ h₂

/-- The faithful statement of Conjecture TLMC-00000001206, read for
    ℕ-valued sequences (Grundy sequences are ℕ-valued, so this implies
    the conjecture for Grundy sequences a fortiori). -/
def conjecture1206 : Prop :=
  ∀ (g₁ g₂ : ℕ → ℕ) (p₁ p₂ : ℕ), 0 < p₁ → 0 < p₂ →
    IsPeriod g₁ p₁ → IsPeriod g₂ p₂ →
    minPeriod (fun n => g₁ n ^^^ g₂ n) ∣ Nat.lcm p₁ p₂

theorem conjecture1206_true : conjecture1206 :=
  fun _ _ _ _ hp₁ hp₂ h₁ h₂ => nimsum_period _ _ hp₁ hp₂ h₁ h₂

end TLMC1206
