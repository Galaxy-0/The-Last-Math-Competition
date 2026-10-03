import Mathlib

/-!
# Conjecture 00000002042 is false

An *exact covering system* is a finite set of residue classes `aᵢ mod mᵢ` such that every
integer lies in exactly one of them. Conjecture 00000002042 asserts that the number of
exact covering systems with distinct moduli (moduli at most `N`) is asymptotically
`c · N^{1/2}`.

In fact the only exact covering system with distinct moduli is the trivial one,
`{0 mod 1}` (Mirsky–Newman), so the count is at most `1` for every `N`.

The proof uses roots of unity. Let `M` be the largest modulus and suppose `M ≥ 2`.
Let `ζ` be a primitive `M`-th root of unity and let `L` be the product of the moduli.
Summing `ζⁿ` over `0 ≤ n < L` gives `0`. Splitting the sum along the classes, a class
`a mod m` contributes `ζᵃ ∑_{j < L/m} (ζᵐ)ʲ`. This is `0` when `m < M`, because then
`ζᵐ ≠ 1` while `(ζᵐ)^{L/m} = 1`. The single class with modulus `M` contributes
`ζᵃ · L/M ≠ 0`. This is a contradiction, so `M = 1`.
-/

namespace Submission00000002042

open Finset Complex Filter Topology

/-- A finite system of residue classes, written as pairs `(m, a)` meaning `a mod m`, with
`0 < m` and `0 ≤ a < m`, is an *exact covering system* if every integer lies in exactly one
of its classes. -/
def IsExactCovering (S : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ S, 0 < p.1 ∧ p.2 < p.1) ∧ ∀ x : ℤ, ∃! p, p ∈ S ∧ x ≡ (p.2 : ℤ) [ZMOD (p.1 : ℤ)]

/-- The classes of `S` have pairwise distinct moduli. -/
def DistinctModuli (S : Finset (ℕ × ℕ)) : Prop := Set.InjOn Prod.fst (S : Set (ℕ × ℕ))

open Classical in
/-- The number of exact covering systems with distinct moduli, all moduli at most `N`. -/
noncomputable def count (N : ℕ) : ℕ :=
  ((Icc 1 N ×ˢ range N).powerset.filter fun S => IsExactCovering S ∧ DistinctModuli S).card

/-- Conjecture 00000002042: the count is asymptotically `c · N^{1/2}` for some `c > 0`. -/
def ConjectureHolds : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto (fun N : ℕ => (count N : ℝ) / (c * Real.sqrt N)) atTop (𝓝 1)

/-! ## Mirsky–Newman -/

/-- Re-indexing the elements of `[0, L)` in a residue class. -/
theorem sum_filter_mod (f : ℕ → ℂ) {L m a : ℕ} (hm : 0 < m) (ha : a < m) (hmL : m ∣ L) :
    ∑ n ∈ (range L).filter (fun n => n % m = a), f n =
      ∑ j ∈ range (L / m), f (a + m * j) := by
  obtain ⟨q, rfl⟩ := hmL
  rw [Nat.mul_div_cancel_left _ hm]
  refine sum_nbij' (fun n => n / m) (fun j => a + m * j) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [mem_filter, mem_range] at hn ⊢
    exact Nat.div_lt_of_lt_mul hn.1
  · intro j hj
    simp only [mem_filter, mem_range] at hj ⊢
    constructor
    · nlinarith
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · intro n hn
    simp only [mem_filter, mem_range] at hn
    have := Nat.mod_add_div n m
    rw [hn.2] at this
    exact this
  · intro j _
    rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt ha, zero_add]
  · intro n hn
    simp only [mem_filter, mem_range] at hn
    congr 1
    have := Nat.mod_add_div n m
    rw [hn.2] at this
    exact this.symm

/-- **Mirsky–Newman.** An exact covering system with distinct moduli is `{0 mod 1}`. -/
theorem eq_trivial {S : Finset (ℕ × ℕ)} (hS : IsExactCovering S) (hD : DistinctModuli S) :
    S = {(1, 0)} := by
  obtain ⟨hpos, hcov⟩ := hS
  have hne : S.Nonempty := by
    obtain ⟨p, ⟨hp, -⟩, -⟩ := hcov 0
    exact ⟨p, hp⟩
  -- the largest modulus
  set M := (S.image Prod.fst).max' (hne.image _) with hMdef
  obtain ⟨p₀, hp₀, hp₀M⟩ := mem_image.1 (max'_mem (S.image Prod.fst) (hne.image _))
  rw [← hMdef] at hp₀M
  have hle : ∀ p ∈ S, p.1 ≤ M := fun p hp => le_max' _ _ (mem_image_of_mem _ hp)
  have hM1 : M = 1 := by
    by_contra hM
    have hMpos : 0 < M := hp₀M ▸ (hpos p₀ hp₀).1
    have hM2 : 2 ≤ M := by omega
    set ζ : ℂ := exp (2 * Real.pi * I / M) with hζ
    have hprim : IsPrimitiveRoot ζ M := isPrimitiveRoot_exp M (by omega)
    set L := ∏ p ∈ S, p.1 with hL
    have hdvd : ∀ p ∈ S, p.1 ∣ L := fun p hp => dvd_prod_of_mem _ hp
    have hMdvd : M ∣ L := hp₀M ▸ hdvd p₀ hp₀
    have hLpos : 0 < L := prod_pos fun p hp => (hpos p hp).1
    -- the full sum vanishes
    have hfull : ∑ n ∈ range L, ζ ^ n = 0 := by
      rw [geom_sum_eq (hprim.ne_one (by omega)) L]
      obtain ⟨q, hq⟩ := hMdvd
      rw [hq, pow_mul, hprim.pow_eq_one, one_pow, sub_self, zero_div]
    -- every `n < L` lies in exactly one class
    have hsplit : ∑ n ∈ range L, ζ ^ n =
        ∑ p ∈ S, ∑ n ∈ (range L).filter (fun n => n % p.1 = p.2), ζ ^ n := by
      simp_rw [sum_filter]
      rw [sum_comm]
      refine sum_congr rfl fun n hn => ?_
      rw [← sum_filter]
      obtain ⟨p, ⟨hp, hpn⟩, huniq⟩ := hcov n
      have hmod : ∀ q ∈ S, (n % q.1 = q.2 ↔ q = p) := by
        intro q hq
        constructor
        · intro h
          apply huniq q
          refine ⟨hq, ?_⟩
          rw [Int.ModEq, ← h]
          push_cast
          exact (Int.emod_emod_of_dvd _ (dvd_refl _)).symm
        · rintro rfl
          have := hpn
          rw [Int.ModEq] at this
          have h2 : ((q.2 : ℕ) : ℤ) % (q.1 : ℤ) = q.2 := by
            exact_mod_cast Nat.mod_eq_of_lt (hpos q hp).2
          rw [h2] at this
          exact_mod_cast this
      rw [show S.filter (fun q => n % q.1 = q.2) = {p} by
        ext q
        simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hq, h⟩
          exact (hmod q hq).1 h
        · intro h
          rw [h]
          exact ⟨hp, (hmod p hp).2 rfl⟩]
      simp
    -- the classes with modulus `< M` contribute nothing
    have hclass : ∀ p ∈ S, p.1 ≠ M →
        ∑ n ∈ (range L).filter (fun n => n % p.1 = p.2), ζ ^ n = 0 := by
      intro p hp hpM
      rw [sum_filter_mod _ (hpos p hp).1 (hpos p hp).2 (hdvd p hp)]
      simp_rw [pow_add, pow_mul]
      rw [← mul_sum, geom_sum_eq (hprim.pow_ne_one_of_pos_of_lt (hpos p hp).1.ne'
        (lt_of_le_of_ne (hle p hp) hpM))]
      rw [← pow_mul, Nat.mul_div_cancel' (hdvd p hp)]
      obtain ⟨q, hq⟩ := hMdvd
      rw [hq, pow_mul, hprim.pow_eq_one, one_pow, sub_self, zero_div, mul_zero]
    -- the class with modulus `M` contributes `ζ^a · L / M`
    have hmain : ∑ n ∈ (range L).filter (fun n => n % p₀.1 = p₀.2), ζ ^ n =
        ζ ^ p₀.2 * (L / M : ℕ) := by
      rw [sum_filter_mod _ (hpos p₀ hp₀).1 (hpos p₀ hp₀).2 (hdvd p₀ hp₀)]
      simp_rw [pow_add, pow_mul, hp₀M, hprim.pow_eq_one, one_pow, mul_one]
      simp [mul_comm]
    have htotal : ∑ p ∈ S, ∑ n ∈ (range L).filter (fun n => n % p.1 = p.2), ζ ^ n =
        ζ ^ p₀.2 * (L / M : ℕ) := by
      rw [sum_eq_single_of_mem p₀ hp₀]
      · exact hmain
      · intro p hp hpp₀
        apply hclass p hp
        intro hpM
        exact hpp₀ (hD hp hp₀ (hpM.trans hp₀M.symm))
    rw [← hsplit, hfull] at htotal
    have hζ0 : ζ ≠ 0 := hprim.ne_zero (by omega)
    have hLM : (L / M : ℕ) ≠ 0 := by
      obtain ⟨q, hq⟩ := hMdvd
      rw [hq, Nat.mul_div_cancel_left _ hMpos]
      rintro rfl
      simp [hq] at hLpos
    have := mul_ne_zero (pow_ne_zero p₀.2 hζ0) (Nat.cast_ne_zero.2 hLM)
    exact this htotal.symm
  -- all moduli are `1`, so `S` has a single class `0 mod 1`
  have hall : ∀ p ∈ S, p = (1, 0) := by
    intro p hp
    have h1 : p.1 = 1 := le_antisymm (hM1 ▸ hle p hp) (hpos p hp).1
    have h2 : p.2 = 0 := by have := (hpos p hp).2; omega
    exact Prod.ext h1 h2
  ext p
  simp only [mem_singleton]
  constructor
  · exact hall p
  · rintro rfl
    obtain ⟨q, hq⟩ := hne
    rw [← hall q hq]
    exact hq

/-- Hence there is at most one exact covering system with distinct moduli. -/
theorem count_le_one (N : ℕ) : count N ≤ 1 := by
  classical
  unfold count
  rw [card_le_one]
  intro S hS T hT
  simp only [mem_filter] at hS hT
  rw [eq_trivial hS.2.1 hS.2.2, eq_trivial hT.2.1 hT.2.2]

/-- Conjecture 00000002042 is false: the count is at most `1`, so it is not asymptotic to
`c · N^{1/2}`. -/
theorem conjecture_00000002042_false : ¬ ConjectureHolds := by
  rintro ⟨c, hc, hlim⟩
  -- the ratio is at most `1 / (c √N) → 0`
  have hbound : ∀ᶠ N : ℕ in atTop, (count N : ℝ) / (c * Real.sqrt N) ≤ 1 / (c * Real.sqrt N) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hpos : 0 < c * Real.sqrt N := mul_pos hc (Real.sqrt_pos.2 (by exact_mod_cast hN))
    exact div_le_div_of_nonneg_right (by exact_mod_cast count_le_one N) hpos.le
  have hzero : Tendsto (fun N : ℕ => 1 / (c * Real.sqrt N)) atTop (𝓝 0) := by
    have h := (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc
    exact h.inv_tendsto_atTop.congr fun N => by simp [one_div]
  have hev := (hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)))
  have hev2 := (hzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  obtain ⟨N, hN⟩ := (hev.and (hev2.and hbound)).exists
  linarith [hN.1, hN.2.1, hN.2.2]

end Submission00000002042

#print axioms Submission00000002042.conjecture_00000002042_false
