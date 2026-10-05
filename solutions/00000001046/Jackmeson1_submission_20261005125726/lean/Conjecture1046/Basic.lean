import Mathlib

/-!
# Conjecture 00000001046 (disproof)

Conjecture: the differential uniformity of `x ↦ x + x^(q-2)` over the finite field `F_q` is
`2` for large `q`.

For a map `g : F → F` on a finite field, the differential uniformity is
`δ(g) = max_{a ≠ 0, b} #{x ∈ F | g (x + a) - g x = b}`.

We prove: whenever `3 ∣ q - 1` (so `F_q` contains a primitive cube root of unity `ω`), the
equation `f (x + 1) - f x = 2` has the four distinct solutions `0, -1, ω, ω²`, hence
`δ(f) ≥ 4`.  This applies to `q = 4^k` (characteristic 2, `GaloisField 2 (2k)`) and to
`q = 7^k` (odd characteristic, `GaloisField 7 k`) for every `k ≥ 1`, so `δ(f) = 2` fails
for arbitrarily large `q` in each of these settings.
-/

open Finset

namespace C1046

section General

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The conjecture's map `x ↦ x + x^(q-2)` on `F_q`, `q = Fintype.card F`. -/
def f (x : F) : F := x + x ^ (Fintype.card F - 2)

/-- Number of solutions `x` of `g (x + a) - g x = b`. -/
def diffCount (g : F → F) (a b : F) : ℕ := #{x | g (x + a) - g x = b}

/-- Differential uniformity: `max_{a ≠ 0, b} #{x | g (x + a) - g x = b}`. -/
def diffUniformity (g : F → F) : ℕ :=
  ({a | a ≠ 0} : Finset F).sup fun a => univ.sup fun b => diffCount g a b

theorem diffCount_le_diffUniformity (g : F → F) {a : F} (ha : a ≠ 0) (b : F) :
    diffCount g a b ≤ diffUniformity g := by
  unfold diffUniformity
  refine le_trans ?_ (Finset.le_sup (f := fun a => univ.sup fun b => diffCount g a b)
    (by simpa using ha))
  exact Finset.le_sup (f := fun b => diffCount g a b) (mem_univ b)

/-- For `q ≥ 3`, `x^(q-2) = x⁻¹` for every `x` (with `0⁻¹ = 0`). -/
theorem pow_card_sub_two (hq : 3 ≤ Fintype.card F) (x : F) :
    x ^ (Fintype.card F - 2) = x⁻¹ := by
  by_cases hx : x = 0
  · subst hx
    rw [inv_zero, zero_pow (by omega)]
  · have h1 := FiniteField.pow_card_sub_one_eq_one x hx
    have : Fintype.card F - 1 = (Fintype.card F - 2) + 1 := by omega
    rw [this, pow_succ] at h1
    exact eq_inv_of_mul_eq_one_left h1

theorem f_eq_add_inv (hq : 3 ≤ Fintype.card F) (x : F) : f x = x + x⁻¹ := by
  rw [f, pow_card_sub_two hq]

/-- If `3 ∣ q - 1`, there is `ω ∈ F` with `ω ≠ 1` and `ω^3 = 1` (Cauchy's theorem in `Fˣ`). -/
theorem exists_cube_root (h3 : 3 ∣ Fintype.card F - 1) :
    ∃ ω : F, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := Fˣ) 3 (by rwa [Fintype.card_units])
  refine ⟨(u : F), ?_, ?_⟩
  · intro h
    have : u = 1 := Units.ext (by simpa using h)
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  · have : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    have := congrArg (fun v : Fˣ => (v : F)) this
    simpa using this

/-- Four distinct solutions of `f (x + 1) - f x = 2`: `0, -1, ω, ω²`. -/
theorem four_le_diffCount (hq : 3 ≤ Fintype.card F) {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) :
    4 ≤ diffCount (f (F := F)) 1 2 := by
  have hcub : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω3
  have hωm1 : ω ≠ -1 := by rintro rfl; norm_num at hcub
  have hω2m1 : ω ^ 2 ≠ -1 := by
    intro h
    apply hω0
    linear_combination hcub - h
  have hω2 : ω ^ 2 ≠ ω := by
    intro h
    apply hω1
    have : ω * (ω - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hω0
    · exact sub_eq_zero.mp h'
  have hω20 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
  have hinv : ω⁻¹ = ω ^ 2 := by
    apply inv_eq_of_mul_eq_one_right; linear_combination hω3
  have hinv2 : (ω ^ 2)⁻¹ = ω := by
    apply inv_eq_of_mul_eq_one_right; linear_combination hω3
  have hp1 : ω + 1 = -ω ^ 2 := by linear_combination hcub
  have hp2 : ω ^ 2 + 1 = -ω := by linear_combination hcub
  have hsub : ({0, -1, ω, ω ^ 2} : Finset F) ⊆ univ.filter fun x => f (x + 1) - f x = 2 := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    simp only [mem_filter, mem_univ, true_and, f_eq_add_inv hq]
    rcases hx with rfl | rfl | rfl | rfl
    · simp; norm_num
    · simp; norm_num
    · rw [hp1, inv_neg, hinv2, hinv]; linear_combination (-2 : F) * hcub
    · rw [hp2, inv_neg, hinv, hinv2]; linear_combination (-2 : F) * hcub
  have hcard : ({0, -1, ω, ω ^ 2} : Finset F).card = 4 := by
    have h01 : (0 : F) ≠ -1 := by simp
    rw [card_insert_of_notMem, card_insert_of_notMem, card_pair hω2.symm]
    · simp only [mem_insert, mem_singleton, not_or]; exact ⟨hωm1.symm, hω2m1.symm⟩
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨h01, hω0.symm, hω20.symm⟩
  unfold diffCount
  rw [← hcard]
  exact card_le_card hsub

/-- **General theorem.** If `3 ∣ q - 1`, the differential uniformity of `x ↦ x + x^(q-2)`
over `F_q` is at least `4`; in particular it is not `2`. -/
theorem four_le_diffUniformity (h3 : 3 ∣ Fintype.card F - 1) :
    4 ≤ diffUniformity (f (F := F)) := by
  have hq : 3 ≤ Fintype.card F := by
    have h1 := Fintype.one_lt_card (α := F)
    have : 0 < Fintype.card F - 1 := by omega
    have := Nat.le_of_dvd this h3
    omega
  obtain ⟨ω, hω1, hω3⟩ := exists_cube_root h3
  exact le_trans (four_le_diffCount hq hω1 hω3)
    (diffCount_le_diffUniformity _ one_ne_zero 2)

theorem diffUniformity_ne_two (h3 : 3 ∣ Fintype.card F - 1) :
    diffUniformity (f (F := F)) ≠ 2 := by
  have := four_le_diffUniformity h3; omega

end General

section Families

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- `q = p^n` with `3 ∣ q - 1`: the Galois field `GaloisField p n` has `δ(f) ≥ 4`. -/
theorem galoisField_four_le (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (h3 : 3 ∣ p ^ n - 1) :
    letI := Fintype.ofFinite (GaloisField p n)
    letI := Classical.decEq (GaloisField p n)
    4 ≤ diffUniformity (f (F := GaloisField p n)) := by
  let _ := Fintype.ofFinite (GaloisField p n)
  let _ := Classical.decEq (GaloisField p n)
  apply four_le_diffUniformity
  rw [Fintype.card_eq_nat_card, GaloisField.card p n hn]
  exact h3

theorem three_dvd_pow_sub_one {b : ℕ} (hb : b % 3 = 1) (k : ℕ) : 3 ∣ b ^ k - 1 := by
  have h : b ^ k % 3 = 1 := by rw [Nat.pow_mod, hb, one_pow]; rfl
  omega

/-- Characteristic 2: for every even `m = 2k ≥ 2`, over `F_{2^m}` we have `δ(f) ≥ 4`. -/
theorem char_two_even (k : ℕ) (hk : k ≠ 0) :
    letI := Fintype.ofFinite (GaloisField 2 (2 * k))
    letI := Classical.decEq (GaloisField 2 (2 * k))
    4 ≤ diffUniformity (f (F := GaloisField 2 (2 * k))) := by
  refine galoisField_four_le 2 (2 * k) (by omega) ?_
  rw [pow_mul]; exact three_dvd_pow_sub_one (by norm_num) k

/-- Odd characteristic: for every `k ≥ 1`, over `F_{7^k}` we have `δ(f) ≥ 4`. -/
theorem char_seven (k : ℕ) (hk : k ≠ 0) :
    letI := Fintype.ofFinite (GaloisField 7 k)
    letI := Classical.decEq (GaloisField 7 k)
    4 ≤ diffUniformity (f (F := GaloisField 7 k)) := by
  exact galoisField_four_le 7 k hk (three_dvd_pow_sub_one (by norm_num) k)

/-- **Disproof, all finite fields.** There is no `N` such that `δ(f) = 2` over every finite
field with more than `N` elements. -/
theorem not_eventually_two :
    ¬ ∃ N : ℕ, ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
      N < Fintype.card F → diffUniformity (f (F := F)) = 2 := by
  rintro ⟨N, hN⟩
  let _ := Fintype.ofFinite (GaloisField 2 (2 * (N + 1)))
  let _ := Classical.decEq (GaloisField 2 (2 * (N + 1)))
  have hc : Fintype.card (GaloisField 2 (2 * (N + 1))) = 2 ^ (2 * (N + 1)) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 _ (by omega)]
  have hlt : N < Fintype.card (GaloisField 2 (2 * (N + 1))) := by
    rw [hc]
    exact lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 := hN (GaloisField 2 (2 * (N + 1))) hlt
  have h4 := char_two_even (N + 1) (by omega)
  omega

/-- **Disproof, characteristic 2 (q = 2^m).** No `N` makes `δ(f) = 2` over every `F_{2^m}`
with `m ≥ N`. -/
theorem not_eventually_two_char_two :
    ¬ ∃ N : ℕ, ∀ m : ℕ, N ≤ m → m ≠ 0 →
      letI := Fintype.ofFinite (GaloisField 2 m)
      letI := Classical.decEq (GaloisField 2 m)
      diffUniformity (f (F := GaloisField 2 m)) = 2 := by
  rintro ⟨N, hN⟩
  have h2 := hN (2 * (N + 1)) (by omega) (by omega)
  have h4 := char_two_even (N + 1) (by omega)
  omega

/-- **Disproof, odd characteristic.** No `N` makes `δ(f) = 2` over every odd-order finite
field with more than `N` elements (witnesses `F_{7^k}`). -/
theorem not_eventually_two_odd :
    ¬ ∃ N : ℕ, ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
      Odd (Fintype.card F) → N < Fintype.card F → diffUniformity (f (F := F)) = 2 := by
  rintro ⟨N, hN⟩
  let _ := Fintype.ofFinite (GaloisField 7 (N + 1))
  let _ := Classical.decEq (GaloisField 7 (N + 1))
  have hc : Fintype.card (GaloisField 7 (N + 1)) = 7 ^ (N + 1) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 7 _ (by omega)]
  have hodd : Odd (Fintype.card (GaloisField 7 (N + 1))) := by
    rw [hc]; exact Odd.pow (by decide)
  have hlt : N < Fintype.card (GaloisField 7 (N + 1)) := by
    rw [hc]
    exact lt_of_lt_of_le (Nat.lt_pow_self (by norm_num)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 := hN (GaloisField 7 (N + 1)) hodd hlt
  have h4 := char_seven (N + 1) (by omega)
  omega

end Families

end C1046
