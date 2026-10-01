/-
  TLMC #1203 DISPROOF (standalone)
-/

import Mathlib

namespace TLMC1203

/-- `p` is a *period* of `f : ℕ → ℕ` if `f (n + p) = f n` for all `n`. -/
def IsPeriod (f : ℕ → ℕ) (p : ℕ) : Prop := ∀ n, f (n + p) = f n

/-- The least positive period. -/
noncomputable def minPeriod (f : ℕ → ℕ) : ℕ := sInf {p | 0 < p ∧ IsPeriod f p}

theorem minPeriod_spec (f : ℕ → ℕ) (h : ∃ p, 0 < p ∧ IsPeriod f p) :
    0 < minPeriod f ∧ IsPeriod f (minPeriod f) := by
  obtain ⟨p, hp, hf⟩ := h
  have hne : {p : ℕ | 0 < p ∧ IsPeriod f p}.Nonempty := ⟨p, hp, hf⟩
  exact Nat.sInf_mem hne

theorem minPeriod_dvd {f : ℕ → ℕ} {q : ℕ} (hq : IsPeriod f q)
    (h : ∃ p, 0 < p ∧ IsPeriod f p) : minPeriod f ∣ q := by
  obtain ⟨hpos, hper⟩ := minPeriod_spec f h
  set π := minPeriod f with hπ
  have hmod : q % π = 0 ∨ (0 < q % π ∧ IsPeriod f (q % π)) := by
    by_cases hz : q % π = 0
    · exact Or.inl hz
    · refine Or.inr ⟨by omega, ?_⟩
      intro n
      have hstrip : IsPeriod f ((q / π) * π) := by
        induction (q / π) with
        | zero => intro n; simp
        | succ k ih =>
            intro n
            have h1 : (k + 1) * π = k * π + π := Nat.succ_mul k π
            have h2 := hper (n + k * π)
            have h3 := ih n
            rw [h1]
            calc f (n + (k * π + π)) = f ((n + k * π) + π) := by congr 1; omega
              _ = f (n + k * π) := h2
              _ = f n := h3
      have e1 : f (n + q % π) = f (n + q % π + (q / π) * π) := (hstrip (n + q % π)).symm
      have e2 : n + q % π + (q / π) * π = n + q := by
        rw [Nat.mul_comm (q / π) π]
        have hdm := Nat.div_add_mod q π
        omega
      rw [e1, e2]
      exact hq n
  rcases hmod with hz | ⟨hlt, hmodp⟩
  · exact Nat.dvd_of_mod_eq_zero hz
  · exfalso
    have hle : π ≤ q % π := Nat.sInf_le ⟨hlt, hmodp⟩
    have : q % π < π := Nat.mod_lt _ hpos
    omega

theorem minPeriod_parity : minPeriod (fun n : ℕ => n % 2) = 2 := by
  have hp2 : IsPeriod (fun n : ℕ => n % 2) 2 := fun n => by
    show (n + 2) % 2 = n % 2; omega
  obtain ⟨hpos, hper⟩ := minPeriod_spec (fun n : ℕ => n % 2) ⟨2, by norm_num, hp2⟩
  have hle : minPeriod (fun n : ℕ => n % 2) ≤ 2 := Nat.sInf_le ⟨by norm_num, hp2⟩
  rcases Nat.eq_or_lt_of_le hle with h | h
  · exact h
  · exfalso
    have h1 : minPeriod (fun n : ℕ => n % 2) = 1 := by omega
    rw [h1] at hper
    have hh : (0 + 1) % 2 = 0 % 2 := hper 0
    omega

/-! ## #1203 — the period law for subtraction games -/

noncomputable def mexFin (s : Finset ℕ) : ℕ := sInf {n | n ∉ s}

theorem mexFin_singleton (v : ℕ) : mexFin {v} = if v = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos v with h0 | hp
  · subst h0
    have hne : {n | n ∉ ({0} : Finset ℕ)}.Nonempty := ⟨1, by simp⟩
    have mem := Nat.sInf_mem hne
    have hle : sInf {n | n ∉ ({0} : Finset ℕ)} ≤ 1 :=
      Nat.sInf_le (show 1 ∈ {n | n ∉ ({0} : Finset ℕ)} by simp)
    have hne0 : sInf {n | n ∉ ({0} : Finset ℕ)} ≠ 0 := by
      intro hc
      exact mem (by rw [hc]; exact Finset.mem_singleton_self 0)
    have hite : (if (0:ℕ) = 0 then 1 else 0) = 1 := by simp
    rw [hite]
    unfold mexFin
    omega
  · have hne : {n | n ∉ ({v} : Finset ℕ)}.Nonempty := ⟨0, by simp [Ne.symm (Nat.ne_of_gt hp)]⟩
    have hle : sInf {n | n ∉ ({v} : Finset ℕ)} ≤ 0 :=
      Nat.sInf_le (show 0 ∈ {n | n ∉ ({v} : Finset ℕ)} by simp [Ne.symm (Nat.ne_of_gt hp)])
    have hite : (if v = 0 then 1 else 0) = 0 := by
      rw [if_neg (Nat.ne_of_gt hp)]
    rw [hite]
    unfold mexFin
    omega

/-- The Sprague–Grundy recursion for a subtraction game with move set `S`,
    stated extensionally: `g` satisfies it iff for every `n`,
    `g n = mex {g (n - s) : s ∈ S, 1 ≤ s ≤ n}`. -/
def SGSatisfies (S : Finset ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ n, g n = mexFin ((S.filter (fun s => 1 ≤ s ∧ s ≤ n)).image (fun s => g (n - s)))

/-- Conjecture #1203 (subtraction-game period law). -/
def conjecture1203 : Prop :=
  ∀ (S : Finset ℕ) (k : ℕ) (g : ℕ → ℕ),
    (∀ s ∈ S, 1 ≤ s ∧ s ≤ k) → SGSatisfies S g →
    ((minPeriod g ∣ 2^k - 1 ↔ (S.Nonempty ∧ ¬(k ∈ S))) ∧
     (k ∈ S → minPeriod g = k + 1))

/-- The SG sequence of the subtraction game S = {1}. -/
noncomputable def sg1 : ℕ → ℕ
  | 0 => 0
  | n + 1 => mexFin {sg1 n}

theorem sg1_eq : ∀ n, sg1 n = n % 2 := by
  intro n
  induction n with
  | zero => simp [sg1]
  | succ n ih =>
      show mexFin {sg1 n} = (n + 1) % 2
      rw [ih, mexFin_singleton]
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · rw [h, if_pos rfl]; omega
      · rw [h, if_neg (by decide)]; omega

theorem sg1_satisfies : SGSatisfies {1} sg1 := by
  intro n
  rcases n with _ | n
  · show sg1 0 = mexFin ((({1} : Finset ℕ).filter (fun s => 1 ≤ s ∧ s ≤ 0)).image
        (fun s => sg1 (0 - s)))
    simp [sg1, mexFin]
  · show sg1 (n + 1) = mexFin ((({1} : Finset ℕ).filter (fun s => 1 ≤ s ∧ s ≤ n + 1)).image
        (fun s => sg1 (n + 1 - s)))
    have hf : ({1} : Finset ℕ).filter (fun s => 1 ≤ s ∧ s ≤ n + 1) = {1} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hs, -, -⟩; exact hs
      · intro hs; subst hs; norm_num
    rw [hf]
    simp only [Finset.image_singleton, Nat.succ_sub_one, sg1]

theorem minPeriod_sg1 : minPeriod sg1 = 2 := by
  have h : sg1 = fun n => n % 2 := funext sg1_eq
  rw [h]
  exact minPeriod_parity

theorem conjecture1203_false : ¬ conjecture1203 := by
  intro h
  obtain ⟨hiff, _⟩ := h {1} 2 sg1
    (by intro s hs; simp at hs; omega) sg1_satisfies
  have hr := hiff.mpr ⟨⟨(1 : ℕ), by simp⟩, by simp⟩
  rw [minPeriod_sg1] at hr
  have hnd : ¬(2 ∣ 2 ^ 2 - 1) := by norm_num
  exact hnd hr

end TLMC1203

