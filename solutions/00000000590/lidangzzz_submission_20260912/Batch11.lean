/-
  Batch 11: machine-checked PROOF of TLMC #590
  ============================================

  Conjecture #590: for a numerical semigroup S with Frobenius number F,
  the theta series Θ_S(q) = Σ_{s∈S} q^s satisfies: Θ_S(q) − 1/(1−q) is
  a polynomial with at most F (Frobenius-many) monomials.

  We PROVE this (the conjecture is true).  The proof: the gaps G = ℕ ∖ S
  are exactly {g ≤ F : g ∉ S} (by the conductor property), so

    Θ_S(q) + G(q) = Σ_{n ≥ 0} q^n = 1/(1−q),

  hence Θ_S(q) − 1/(1−q) = −G(q), a polynomial whose monomials are
  exactly the gaps; since 0 ∈ S, all gaps lie in {1, …, F}, so there are
  at most F of them.

  Formalization: power series over ℚ; `ones` (all coefficients 1) is
  shown to be the multiplicative inverse of (1 − q) via the coefficient
  computation (1 − q) · ones = 1.  The gap polynomial is a Finset sum of
  monomials; its support cardinality is bounded by F by a Finset.card
  bound.  No `sorry`.
  Toolchain: leanprover/lean4:v4.31.0, Mathlib v4.31.0.
-/

import Mathlib

namespace TLMCBatch11

open PowerSeries

/-- The geometric series `1/(1−q)`, realized by its coefficients. -/
def ones : PowerSeries ℚ := PowerSeries.mk (fun _ => 1)

/-- The coefficient of `1 − q` at `a`. -/
theorem coeff_1_sub_X (a : ℕ) :
    (PowerSeries.coeff a) (1 - PowerSeries.X : PowerSeries ℚ) =
      if a = 0 then (1:ℚ) else if a = 1 then -1 else 0 := by
  match a with
  | 0 => simp [map_sub]
  | 1 => simp [map_sub]
  | (a + 2) =>
      have hx : (PowerSeries.coeff (a + 2)) (PowerSeries.X : PowerSeries ℚ) = 0 := by
        rw [PowerSeries.coeff_X, if_neg (by omega)]
      rw [map_sub, hx, sub_zero, PowerSeries.coeff_one,
        if_neg (by omega : a + 2 ≠ 0)]
      exact eq_comm.mp rfl

/-- `ones` is the inverse of `1 − q`: `(1 − q) · ones = 1`. -/
theorem one_sub_mul_ones : (1 - PowerSeries.X : PowerSeries ℚ) * ones = 1 := by
  ext n
  rcases n with _ | n
  · rw [PowerSeries.coeff_mul]
    rw [show Finset.antidiagonal 0 = {(0, 0)} from rfl]
    simp [coeff_1_sub_X, ones]
  · rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
    have h1 : (PowerSeries.coeff (0, n + 1).1) (1 - PowerSeries.X : PowerSeries ℚ)
        * (PowerSeries.coeff (0, n + 1).2) ones = 1 := by
      rw [coeff_1_sub_X]
      simp [ones]
    rw [h1]
    have h2 : ∀ p ∈ Finset.antidiagonal n,
        (PowerSeries.coeff (p.1 + 1)) (1 - PowerSeries.X : PowerSeries ℚ)
          * (PowerSeries.coeff p.2) ones = if p.1 = 0 then -1 else 0 := by
      intro p hp
      rcases p with ⟨a, b⟩
      rw [coeff_1_sub_X]
      cases a with
      | zero => simp [ones]
      | succ c => rw [if_neg (by omega), if_neg (by omega)]; simp
    rw [Finset.sum_congr rfl fun p hp => h2 p hp]
    rw [Finset.sum_eq_single (0, n)]
    · simp
    · intro p hmem hp
      rcases p with ⟨a, b⟩
      have hab : a + b = n := by
        simpa [Finset.mem_antidiagonal] using hmem
      rw [if_neg (fun hh => by
        rcases hh with ⟨rfl, hb⟩
        exact hp (by
          have hbn : b = n := by rw [← Nat.zero_add b]; exact hab
          simp [hbn]))]
    · intro h
      simp [Finset.mem_antidiagonal] at h

/-- The theta series of a cofinite submonoid `S ⊆ ℕ` (its `0 ∈ S`,
  `F`-conductor structure). -/
def thetaS (S : Set ℕ) [DecidablePred (· ∈ S)] : PowerSeries ℚ :=
  PowerSeries.mk fun n => if decide (n ∈ S) then 1 else 0

/-- The gap polynomial: monomial `q^g` for every gap `g ≤ F`. -/
noncomputable def gapPoly (S : Set ℕ) [DecidablePred (· ∈ S)] (F : ℕ) : Polynomial ℚ :=
  ∑ g ∈ (Finset.range (F + 1)).filter (fun g => g ∉ S),
    Polynomial.monomial g 1

variable {S : Set ℕ} [DecidablePred (· ∈ S)] {F : ℕ}

/-- The gap polynomial has coefficient `1` exactly at the gaps below `F`. -/
theorem coeff_gapPoly (n : ℕ) :
    Polynomial.coeff (gapPoly S F) n =
      if decide (n ≤ F ∧ n ∉ S) then 1 else 0 := by
  classical
  rw [gapPoly, Polynomial.finsetSum_coeff]
  by_cases hmem : n ∈ (Finset.range (F + 1)).filter (fun g => g ∉ S)
  · have hcond : n ≤ F ∧ n ∉ S := by
      simpa [Finset.mem_filter, Finset.mem_range] using hmem
    rw [Finset.sum_eq_single_of_mem n hmem]
    · rw [Polynomial.coeff_monomial, if_pos rfl, if_pos (by simpa using hcond)]
    · intro g hg hgne
      by_cases hgm : g = n
      · exact absurd hgm hgne
      · rw [Polynomial.coeff_monomial, if_neg hgm]
  · rw [Finset.sum_eq_zero]
    · have hcond : ¬(n ≤ F ∧ n ∉ S) := by
        intro hc
        exact hmem (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega),
          by simpa using hc.2⟩)
      rw [if_neg (by simpa using hcond)]
    · intro g hg
      by_cases hgm : g = n
      · exact absurd (hgm ▸ hg) hmem
      · rw [Polynomial.coeff_monomial, if_neg hgm]

/-- **TLMC #590 is true** (proved).  For a numerical semigroup `S` with
    `0 ∈ S`, Frobenius number `F` (i.e. `F ∉ S`) and conductor property
    (`n > F → n ∈ S`), the theta series satisfies

      Θ_S(q) − 1/(1−q) = −(gapPoly S F),

    where `1/(1−q)` is realized by `ones` (with `(1 − q) · ones = 1`),
    and the gap polynomial has at most `F` monomials. -/
theorem tlm590 (h0mem : 0 ∈ S) (_hF : F ∉ S) (hcond : ∀ n, F < n → n ∈ S) :
    thetaS S + (gapPoly S F : PowerSeries ℚ) = ones ∧
      (gapPoly S F).support.card ≤ F := by
  constructor
  · ext n
    have hsplit : (PowerSeries.coeff n) (thetaS S + (gapPoly S F : PowerSeries ℚ))
        = (PowerSeries.coeff n) (thetaS S)
          + (PowerSeries.coeff n) ((gapPoly S F : PowerSeries ℚ)) :=
      map_add (PowerSeries.coeff n) _ _
    rw [hsplit]
    have hcoe : (PowerSeries.coeff n) ((gapPoly S F : PowerSeries ℚ))
        = Polynomial.coeff (gapPoly S F) n := by
      simp only [Polynomial.toPowerSeries, PowerSeries.coeff_mk]
    by_cases hs : n ∈ S
    · have hgap : Polynomial.coeff (gapPoly S F) n = 0 := by
        rw [coeff_gapPoly, if_neg (by
          show ¬decide (n ≤ F ∧ n ∉ S) = true
          intro hc
          rw [decide_eq_true_eq] at hc
          exact hc.2 hs)]
      simp [thetaS, hs, hgap, ones]
    · have hnF : n ≤ F := by
        by_contra hc
        exact hs (hcond n (by omega))
      have hgap : Polynomial.coeff (gapPoly S F) n = 1 := by
        rw [coeff_gapPoly, if_pos (by
          show decide (n ≤ F ∧ n ∉ S) = true
          simp only [decide_eq_true_eq]
          exact ⟨hnF, hs⟩)]
      simp [thetaS, hs, hgap, ones]
  · have hsub : (gapPoly S F).support ⊆ (Finset.range (F + 1)).filter (fun g => g ∉ S) := by
      intro g hg
      have hne : Polynomial.coeff (gapPoly S F) g ≠ 0 :=
        Polynomial.mem_support_iff.1 hg
      rw [coeff_gapPoly] at hne
      rcases Nat.lt_or_ge g F with hlt | hge
      · refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (le_of_lt hlt)), ?_⟩
        intro hgS
        rw [if_neg (by
          show ¬decide (g ≤ F ∧ g ∉ S) = true
          simp only [decide_eq_true_eq]
          exact fun hc => hc.2 hgS)] at hne
        exact hne rfl
      · by_contra hmem
        have hfalse : ¬decide (g ≤ F ∧ g ∉ S) = true := by
          intro hc
          have hh : g ≤ F ∧ g ∉ S := of_decide_eq_true hc
          exact hmem (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hh.2⟩)
        exact hne (if_neg hfalse)
    set hcard0 : Finset ℕ := (Finset.range (F + 1)).filter (fun g => g ∉ S) with hcard0def
    have h1 : hcard0.card ≤ F := by
      have hsub2 : hcard0 ⊆ Finset.range (F + 1) := Finset.filter_subset _ _
      have hle : hcard0.card ≤ (Finset.range (F + 1)).card := Finset.card_le_card hsub2
      rw [Finset.card_range] at hle
      have h02 : (0:ℕ) ∉ hcard0 := by
        intro hc
        have hh := Finset.mem_filter.1 hc
        exact hh.2 h0mem
      have hne : hcard0 ≠ Finset.range (F + 1) := by
        intro heq
        have h0' : (0:ℕ) ∈ hcard0 := by
          rw [heq]
          exact Finset.mem_range.2 (Nat.succ_pos F)
        exact h02 h0'
      by_contra hgt
      have heq2 : hcard0.card = (Finset.range (F + 1)).card := by
        rw [Finset.card_range]
        omega
      exact hne (Finset.eq_of_subset_of_card_le hsub2 (le_of_eq heq2.symm))
    exact Nat.le_trans (Finset.card_le_card hsub) h1

end TLMCBatch11
