import Mathlib

/-!
# Conjecture 00000007976: the radius-1 covering density is not `1 + 2^{-n}`

A binary code `C ⊆ 𝔽₂ⁿ` *covers with radius `r`* if every word lies within Hamming distance
`r` of a codeword. Its covering density is `|C| · V(n,r) / 2ⁿ`, where
`V(n,r) = ∑_{i ≤ r} C(n,i)` is the volume of a Hamming ball. The optimal density is
`μ(n,r) = K(n,r) · V(n,r) / 2ⁿ`, with `K(n,r)` the least size of a covering code.

The third claim of Conjecture 00000007976 is `μ(n,1) = 1 + 2^{-n}`. This fails for every odd
`n`, and in fact for every code: `|C| · (n+1)` is even when `n` is odd, whereas
`2ⁿ · (1 + 2^{-n}) = 2ⁿ + 1` is odd. Concretely, `μ(3,1) = 1` (the repetition code) and
`μ(7,1) = 1` (the Hamming code), by the sphere-covering bound `K(n,1) (n+1) ≥ 2ⁿ`.
-/

namespace Submission00000007976

open Finset

/-- Binary words of length `n`. -/
abbrev Word (n : ℕ) := Fin n → ZMod 2

/-- `C` covers `𝔽₂ⁿ` with radius `r`: every word is within Hamming distance `r` of `C`. -/
def Covers {n : ℕ} (C : Finset (Word n)) (r : ℕ) : Prop :=
  ∀ x : Word n, ∃ c ∈ C, hammingDist x c ≤ r

/-- Volume of a Hamming ball of radius `r` in `𝔽₂ⁿ`. -/
def ballVolume (n r : ℕ) : ℕ := ∑ i ∈ range (r + 1), n.choose i

/-- Covering density of a code: `|C| · V(n,r) / 2ⁿ`. -/
noncomputable def density {n : ℕ} (C : Finset (Word n)) (r : ℕ) : ℝ :=
  (C.card * ballVolume n r : ℝ) / 2 ^ n

/-- `K(n,r)`: the least size of a binary covering code of length `n` and radius `r`. -/
noncomputable def coveringNumber (n r : ℕ) : ℕ :=
  sInf {k | ∃ C : Finset (Word n), C.card = k ∧ Covers C r}

/-- The optimal covering density `μ(n,r) = K(n,r) · V(n,r) / 2ⁿ`. -/
noncomputable def mu (n r : ℕ) : ℝ := (coveringNumber n r * ballVolume n r : ℝ) / 2 ^ n

/-- Third claim of the conjecture: `μ(n,1) = 1 + 2^{-n}` for every `n ≥ 1`. -/
def Claim3 : Prop := ∀ n : ℕ, 1 ≤ n → mu n 1 = 1 + 1 / 2 ^ n

/-- The same claim for all sufficiently large `n`. -/
def Claim3Eventually : Prop := ∃ N : ℕ, ∀ n : ℕ, N ≤ n → mu n 1 = 1 + 1 / 2 ^ n

theorem ballVolume_one (n : ℕ) : ballVolume n 1 = n + 1 := by
  simp [ballVolume, sum_range_succ, add_comm]

/-- If `k (n+1) / 2ⁿ = 1 + 1/2ⁿ` then `k (n+1) = 2ⁿ + 1`. -/
theorem nat_eq_of_density {n k : ℕ} (h : (k * (n + 1) : ℝ) / 2 ^ n = 1 + 1 / 2 ^ n) :
    k * (n + 1) = 2 ^ n + 1 := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have : (k * (n + 1) : ℝ) = 2 ^ n + 1 := by
    field_simp at h
    linarith
  exact_mod_cast this

/-- For odd `n`, `k (n+1)` is even while `2ⁿ + 1` is odd. -/
theorem parity_contra {n k : ℕ} (hn : Odd n) (h : k * (n + 1) = 2 ^ n + 1) : False := by
  have heven : Even (k * (n + 1)) := hn.add_one.mul_left k
  have hodd : Odd (2 ^ n + 1) :=
    (Nat.even_pow.2 ⟨even_two, by rintro rfl; exact (Nat.not_odd_zero hn)⟩).add_one
  rw [h] at heven
  exact Nat.not_even_iff_odd.2 hodd heven

/-- **Parity obstruction**: for odd `n`, no code has radius-1 density `1 + 2^{-n}`, because
`|C| (n+1)` is even and `2ⁿ + 1` is odd. -/
theorem density_ne {n : ℕ} (hn : Odd n) (C : Finset (Word n)) :
    density C 1 ≠ 1 + 1 / 2 ^ n := by
  intro h
  unfold density at h
  rw [ballVolume_one] at h
  have := nat_eq_of_density (by exact_mod_cast h)
  exact parity_contra hn this

/-- For odd `n`, `μ(n,1) ≠ 1 + 2^{-n}`. -/
theorem mu_ne {n : ℕ} (hn : Odd n) : mu n 1 ≠ 1 + 1 / 2 ^ n := by
  intro h
  unfold mu at h
  rw [ballVolume_one] at h
  have := nat_eq_of_density (by exact_mod_cast h)
  exact parity_contra hn this

/-- **The third claim fails** (at `n = 1`, and at every odd `n`). -/
theorem not_claim3 : ¬ Claim3 := fun h => mu_ne (n := 1) odd_one (h 1 le_rfl)

/-- **The third claim fails for all large `n` as well**: odd `n` are arbitrarily large. -/
theorem not_claim3Eventually : ¬ Claim3Eventually := by
  rintro ⟨N, h⟩
  exact mu_ne (n := 2 * N + 1) (odd_two_mul_add_one N) (h _ (by omega))

/-! ### The true values `μ(3,1) = μ(7,1) = 1` -/

/-- The radius-1 ball around `c` consists of `c` and the words `c + eᵢ`. -/
def ball1 {n : ℕ} (c : Word n) : Finset (Word n) :=
  (univ : Finset (Option (Fin n))).image fun o =>
    match o with
    | none => c
    | some i => c + Pi.single i 1

theorem mem_ball1 {n : ℕ} {x c : Word n} (h : hammingDist x c ≤ 1) : x ∈ ball1 c := by
  simp only [ball1, mem_image, mem_univ, true_and]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
  · exact ⟨none, (hammingDist_eq_zero.1 h0).symm⟩
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ c i := by
      by_contra hne
      push Not at hne
      have : x = c := funext hne
      rw [this, hammingDist_self] at h1
      exact zero_ne_one h1
    refine ⟨some i, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      have : x j = c j + 1 := by
        generalize x j = a at hi ⊢
        generalize c j = b at hi ⊢
        revert a b; decide
      simp [this]
    · have : x j = c j := by
        by_contra hxj
        have h2 : 2 ≤ hammingDist x c := by
          unfold hammingDist
          have : ({i, j} : Finset (Fin n)) ⊆ univ.filter fun k => x k ≠ c k := by
            intro k hk
            simp only [mem_insert, mem_singleton] at hk
            rcases hk with rfl | rfl <;> simpa
          calc 2 = ({i, j} : Finset (Fin n)).card := by
                rw [card_pair (Ne.symm hj)]
            _ ≤ _ := card_le_card this
        omega
      simp [hj, this]

/-- **Sphere-covering bound**: a radius-1 covering code of length `n` has at least
`2ⁿ / (n+1)` codewords. -/
theorem sphere_covering {n : ℕ} {C : Finset (Word n)} (h : Covers C 1) :
    2 ^ n ≤ C.card * (n + 1) := by
  have hsub : (univ : Finset (Word n)) ⊆ C.biUnion ball1 := by
    intro x _
    obtain ⟨c, hc, hd⟩ := h x
    exact mem_biUnion.2 ⟨c, hc, mem_ball1 hd⟩
  have hball : ∀ c : Word n, (ball1 c).card ≤ n + 1 := fun c => by
    calc (ball1 c).card ≤ (univ : Finset (Option (Fin n))).card := card_image_le
      _ = n + 1 := by simp
  calc 2 ^ n = (univ : Finset (Word n)).card := by simp
    _ ≤ (C.biUnion ball1).card := card_le_card hsub
    _ ≤ ∑ c ∈ C, (ball1 c).card := card_biUnion_le
    _ ≤ ∑ _c ∈ C, (n + 1) := sum_le_sum fun c _ => hball c
    _ = C.card * (n + 1) := by simp

/-- `μ(n,1) = 1` whenever some radius-1 covering code has exactly `2ⁿ / (n+1)` words. -/
theorem mu_eq_one_of_perfect {n : ℕ} (C : Finset (Word n)) (hC : Covers C 1)
    (hcard : C.card * (n + 1) = 2 ^ n) : mu n 1 = 1 := by
  have hmem : C.card ∈ {k | ∃ D : Finset (Word n), D.card = k ∧ Covers D 1} := ⟨C, rfl, hC⟩
  have hK : coveringNumber n 1 = C.card := by
    unfold coveringNumber
    apply le_antisymm (Nat.sInf_le hmem)
    refine le_csInf ⟨C.card, hmem⟩ fun k hk => ?_
    obtain ⟨D, hD, hcov⟩ := hk
    have := sphere_covering hcov
    rw [hD] at this
    by_contra hlt
    push Not at hlt
    have : k * (n + 1) < C.card * (n + 1) := Nat.mul_lt_mul_of_pos_right hlt (by omega)
    omega
  unfold mu
  rw [hK, ballVolume_one]
  have : ((C.card : ℝ) * ((n : ℝ) + 1)) = 2 ^ n := by exact_mod_cast hcard
  push_cast
  rw [this, div_self (by positivity)]

/-- The repetition code `{000, 111}`. -/
def rep3 : Finset (Word 3) := {![0, 0, 0], ![1, 1, 1]}

theorem rep3_covers : Covers rep3 1 := by
  unfold Covers rep3; decide

theorem mu_three : mu 3 1 = 1 := mu_eq_one_of_perfect rep3 rep3_covers (by decide)

/-- The Hamming code of length `7`: the words `x` with `H x = 0`, where column `j` of the
parity-check matrix `H` is the binary expansion of `j + 1`; the three rows of `H` are the
three parity checks below. -/
def hamming7 : Finset (Word 7) :=
  univ.filter fun x =>
    x 0 + x 2 + x 4 + x 6 = 0 ∧ x 1 + x 2 + x 5 + x 6 = 0 ∧ x 3 + x 4 + x 5 + x 6 = 0

theorem hamming7_card : hamming7.card = 16 := by decide +kernel

theorem hamming7_covers : Covers hamming7 1 := by
  unfold Covers; decide +kernel

theorem mu_seven : mu 7 1 = 1 :=
  mu_eq_one_of_perfect hamming7 hamming7_covers (by simp [hamming7_card])

/-- **Conjecture 00000007976 is false**: its third claim fails, both as stated for every `n` and
for all large `n`. Whatever the first two claims (`P`, `Q`) mean, the conjunction is false. -/
theorem conjecture_00000007976_false (P Q : Prop) :
    ¬ (P ∧ Q ∧ Claim3) ∧ ¬ (P ∧ Q ∧ Claim3Eventually) :=
  ⟨fun h => not_claim3 h.2.2, fun h => not_claim3Eventually h.2.2⟩

end Submission00000007976

#print axioms Submission00000007976.conjecture_00000007976_false
#print axioms Submission00000007976.mu_seven
