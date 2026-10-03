import Mathlib

/-!
# Conjecture 00000007990: perfect Lee codes of radius 1 exist in every dimension

The Lee distance on `ℤⁿ` is `d(x,y) = ∑ᵢ |xᵢ − yᵢ|`. A perfect Lee code `PL(n,e)` of radius
`e` is a set `C ⊆ ℤⁿ` such that every point lies within Lee distance `e` of exactly one
codeword (the Lee balls of radius `e` around the codewords tile `ℤⁿ`).

Conjecture 00000007990 claims that perfect Lee codes exist only for `(n,e) = (2,2)`, for
`e = 2` with `n ≡ ±1 (mod 6)`, and for sparse exceptions of higher radius `e ≥ 3`. In
particular no perfect Lee code of radius `1` would exist. But for every `n ≥ 1` the
Golomb–Welch code

  `C = {x ∈ ℤⁿ : 1·x₁ + 2·x₂ + ⋯ + n·xₙ ≡ 0 (mod 2n+1)}`

is a perfect Lee code of radius `1`: the `2n + 1` points within distance `1` of any `x` are
`x` and `x ± eᵢ`, whose weights are `w(x)`, `w(x) ± i`, which run over all residues modulo
`2n + 1` exactly once.
-/

namespace Submission00000007990

open Finset

/-- Points of `ℤⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → ℤ

/-- The Lee distance `d(x,y) = ∑ᵢ |xᵢ − yᵢ|`. -/
def leeDist {n : ℕ} (x y : Pt n) : ℕ := ∑ i, (x i - y i).natAbs

/-- `C` is a perfect Lee code of radius `e`: every point has exactly one codeword within Lee
distance `e`. -/
def IsPerfectLeeCode (n e : ℕ) (C : Set (Pt n)) : Prop :=
  ∀ x : Pt n, ∃! c, c ∈ C ∧ leeDist x c ≤ e

/-- A perfect Lee code `PL(n,e)` exists. -/
def ExistsPL (n e : ℕ) : Prop := ∃ C : Set (Pt n), IsPerfectLeeCode n e C

/-- The first claim of the conjecture: `PL(n,e)` (with `n, e ≥ 1`) exists only for
`(n,e) = (2,2)`, for `e = 2` with `n ≡ ±1 (mod 6)`, or for radius `e ≥ 3`. Allowing every
`e ≥ 3` only weakens the claim. -/
def Claim1 : Prop :=
  ∀ n e : ℕ, 1 ≤ n → 1 ≤ e → ExistsPL n e →
    (n = 2 ∧ e = 2) ∨ (e = 2 ∧ (n % 6 = 1 ∨ n % 6 = 5)) ∨ 3 ≤ e

/-- The weight `w(x) = ∑ᵢ (i+1) xᵢ` (coordinates indexed from `0`). -/
def weight {n : ℕ} (x : Pt n) : ℤ := ∑ i : Fin n, ((i : ℕ) + 1 : ℤ) * x i

/-- The Golomb–Welch code: points whose weight is divisible by `2n + 1`. -/
def GW (n : ℕ) : Set (Pt n) := {x | (2 * n + 1 : ℤ) ∣ weight x}

/-- The unit steps `±eᵢ` and `0`, indexed by `Option (Fin n × Bool)`. -/
def step {n : ℕ} : Option (Fin n × Bool) → Pt n
  | none => 0
  | some (i, b) => Pi.single i (if b then 1 else -1)

/-- The weight of a step: `0` or `±(i+1)`. -/
def stepWeight {n : ℕ} : Option (Fin n × Bool) → ℤ
  | none => 0
  | some (i, b) => if b then (i : ℤ) + 1 else -((i : ℤ) + 1)

theorem weight_add {n : ℕ} (x y : Pt n) : weight (x + y) = weight x + weight y := by
  simp only [weight, Pi.add_apply, mul_add, sum_add_distrib]

theorem weight_step {n : ℕ} (o : Option (Fin n × Bool)) : weight (step o) = stepWeight o := by
  rcases o with _ | ⟨i, b⟩
  · simp [weight, step, stepWeight]
  · simp only [weight, step, stepWeight]
    rw [sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    split_ifs <;> simp

theorem stepWeight_abs {n : ℕ} (o : Option (Fin n × Bool)) : |stepWeight o| ≤ n := by
  rcases o with _ | ⟨i, b⟩
  · simp [stepWeight]
  · have := i.isLt
    cases b <;> simp only [stepWeight, Bool.false_eq_true, if_false, if_true] <;>
      rw [abs_le] <;> constructor <;> omega

/-- Different steps have different weights. -/
theorem stepWeight_injective {n : ℕ} : Function.Injective (stepWeight (n := n)) := by
  intro o o' h
  rcases o with _ | ⟨i, b⟩ <;> rcases o' with _ | ⟨j, c⟩
  · rfl
  · cases c <;> simp only [stepWeight, Bool.false_eq_true, if_false, if_true] at h <;> omega
  · cases b <;> simp only [stepWeight, Bool.false_eq_true, if_false, if_true] at h <;> omega
  · cases b <;> cases c <;> simp only [stepWeight, Bool.false_eq_true, if_false, if_true] at h
    · have : i = j := Fin.ext (by omega)
      subst this; rfl
    · omega
    · omega
    · have : i = j := Fin.ext (by omega)
      subst this; rfl

theorem leeDist_add_step {n : ℕ} (x : Pt n) (o : Option (Fin n × Bool)) :
    leeDist x (x + step o) ≤ 1 := by
  rcases o with _ | ⟨i, b⟩
  · simp [leeDist, step]
  · simp only [leeDist, step, Pi.add_apply, sub_add_cancel_left]
    rw [sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    split_ifs <;> simp

/-- Every point within Lee distance `1` of `x` is `x + step o` for some step `o`. -/
theorem eq_add_step {n : ℕ} {x y : Pt n} (h : leeDist x y ≤ 1) :
    ∃ o, y = x + step o := by
  by_cases hxy : y = x
  · exact ⟨none, by simp [hxy, step]⟩
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ x i := by
    by_contra hne
    push Not at hne
    exact hxy (funext hne)
  have hsplit : leeDist x y = (x i - y i).natAbs + ∑ j ∈ univ.erase i, (x j - y j).natAbs :=
    (add_sum_erase _ _ (mem_univ i)).symm
  have hpos : 1 ≤ (x i - y i).natAbs := by
    have : x i - y i ≠ 0 := sub_ne_zero.2 (Ne.symm hi)
    omega
  have hrest : ∑ j ∈ univ.erase i, (x j - y j).natAbs = 0 := by omega
  have hzero : ∀ j, j ≠ i → y j = x j := by
    intro j hj
    have := (sum_eq_zero_iff.1 hrest) j (mem_erase.2 ⟨hj, mem_univ j⟩)
    omega
  have hone : (x i - y i).natAbs = 1 := by omega
  refine ⟨some (i, decide (y i = x i + 1)), funext fun j => ?_⟩
  by_cases hj : j = i
  · subst hj
    simp only [step, Pi.add_apply, Pi.single_eq_same]
    rcases Int.natAbs_eq_iff.1 hone with h1 | h1 <;> split_ifs with hd <;> simp_all <;> omega
  · simp [step, hj, hzero j hj]

/-- **The Golomb–Welch code is a perfect Lee code of radius `1` in every dimension.** -/
theorem isPerfectLeeCode_GW (n : ℕ) : IsPerfectLeeCode n 1 (GW n) := by
  intro x
  set m : ℤ := 2 * n + 1 with hm
  have hm0 : 0 < m := by omega
  set s := weight x % m with hs
  have hs0 : 0 ≤ s := Int.emod_nonneg _ (by omega)
  have hs1 : s < m := Int.emod_lt_of_pos _ hm0
  have hdiv : m ∣ weight x - s := ⟨weight x / m, by rw [hs, Int.emod_def]; ring⟩
  -- existence: a step whose weight is `≡ −w(x)`
  obtain ⟨o, ho⟩ : ∃ o : Option (Fin n × Bool), m ∣ weight x + stepWeight o := by
    by_cases h0 : s = 0
    · exact ⟨none, by simpa [stepWeight, h0] using hdiv⟩
    by_cases hle : s ≤ n
    · refine ⟨some (⟨(s - 1).toNat, by omega⟩, false), ?_⟩
      simp only [stepWeight, Bool.false_eq_true, if_false]
      have : ((((s - 1).toNat : ℕ) : ℤ)) = s - 1 := Int.toNat_of_nonneg (by omega)
      rw [this]
      have : weight x + -(s - 1 + 1) = weight x - s := by ring
      rw [this]
      exact hdiv
    · refine ⟨some (⟨(m - s - 1).toNat, by omega⟩, true), ?_⟩
      simp only [stepWeight, if_true]
      have : ((((m - s - 1).toNat : ℕ) : ℤ)) = m - s - 1 := Int.toNat_of_nonneg (by omega)
      rw [this]
      have : weight x + (m - s - 1 + 1) = (weight x - s) + m := by ring
      rw [this]
      exact dvd_add hdiv (dvd_refl m)
  refine ⟨x + step o, ⟨?_, leeDist_add_step x o⟩, ?_⟩
  · show m ∣ weight (x + step o)
    rw [weight_add, weight_step]; exact ho
  -- uniqueness: two admissible steps have weights congruent mod `m` and of size `≤ n`
  rintro c ⟨hc, hcd⟩
  obtain ⟨o', rfl⟩ := eq_add_step hcd
  have ho' : m ∣ weight x + stepWeight o' := by
    have : m ∣ weight (x + step o') := hc
    rwa [weight_add, weight_step] at this
  have hd : m ∣ stepWeight o' - stepWeight o := by
    have := dvd_sub ho' ho
    simpa using this
  have hsmall : |stepWeight o' - stepWeight o| < m := by
    have h1 := stepWeight_abs o
    have h2 := stepWeight_abs o'
    rw [abs_le] at h1 h2
    rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hd hsmall
  rw [stepWeight_injective (sub_eq_zero.1 this)]

/-- **The first claim fails**: `PL(n,1)` exists for every `n ≥ 1`, but radius `1` is not on the
list. -/
theorem not_claim1 : ¬ Claim1 := by
  intro h
  rcases h 1 1 le_rfl le_rfl ⟨GW 1, isPerfectLeeCode_GW 1⟩ with ⟨-, h⟩ | ⟨h, -⟩ | h <;> omega

/-- The failure is not sparse: for every `n ≥ 1` the pair `(n,1)` violates the claimed list. -/
theorem claim1_fails_everywhere (n : ℕ) :
    ExistsPL n 1 ∧ ¬ ((n = 2 ∧ 1 = 2) ∨ (1 = 2 ∧ (n % 6 = 1 ∨ n % 6 = 5)) ∨ 3 ≤ 1) :=
  ⟨⟨GW n, isPerfectLeeCode_GW n⟩, by omega⟩

/-- **Conjecture 00000007990 is false**: its first claim fails. Whatever the other two claims
(`P`, `Q`) mean, the conjunction is false. -/
theorem conjecture_00000007990_false (P Q : Prop) : ¬ (Claim1 ∧ P ∧ Q) :=
  fun h => not_claim1 h.1

end Submission00000007990

#print axioms Submission00000007990.conjecture_00000007990_false
#print axioms Submission00000007990.isPerfectLeeCode_GW
