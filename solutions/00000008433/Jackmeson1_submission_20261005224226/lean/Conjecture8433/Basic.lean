import Mathlib

/-!
# Conjecture 00000008433 is false

Statement (English text of the conjecture): "Once v is at least exp(exp(t)), existence is decided
solely by the divisibility conditions; and the bound can be improved to v at least t^{ct} with c an
absolute constant."

The threshold depends on `t` only, so it is uniform in the block size `k` and the index `λ`.
We refute it with the family of parameters, for every `m ≥ 3`,

  `t = 2`, `λ = 1`, `v = (m-1)^2 (m+1)`, `k = m (m-1)`.

All divisibility conditions hold (`r = (v-1)/(k-1) = m`, `b = v(v-1)/(k(k-1)) = m^2 - 1`), but a
`2`-`(v,k,1)` design with `k < v` forces `k (k-1) ≤ v - 1` (the `λ = 1` case of Fisher's inequality,
proved below by double counting), and `k (k-1) > v - 1 = m (k-1)` because `k = m(m-1) > m`.
Since `v → ∞` along the family, no threshold `T(t)` depending on `t` alone works.
-/

namespace Conjecture8433

open Finset

/-- `blk : ι → Finset α` is a `t`-`(v,k,λ)` design on the finite point set `α` (`v = |α|`): every
block has exactly `k` points and every `t`-element set of points is contained in exactly `lam`
blocks. Blocks are counted by index, so repeated blocks are allowed (simple designs are the special
case of an injective `blk`; see `not_hasSimpleDesign`). -/
def IsDesign {α ι : Type*} [DecidableEq α] [Fintype ι] (t k lam : ℕ) (blk : ι → Finset α) :
    Prop :=
  (∀ i, (blk i).card = k) ∧
    ∀ T : Finset α, T.card = t → (univ.filter fun i => T ⊆ blk i).card = lam

/-- A `t`-`(v,k,λ)` design exists: a finite family of `b` blocks (for some `b`) on `Fin v`,
repeated blocks allowed. -/
def HasDesign (t v k lam : ℕ) : Prop :=
  ∃ (b : ℕ) (blk : Fin b → Finset (Fin v)), IsDesign t k lam blk

/-- A simple `t`-`(v,k,λ)` design exists: a set `D` of `k`-subsets of `Fin v` such that every
`t`-subset lies in exactly `lam` members of `D`. -/
def HasSimpleDesign (t v k lam : ℕ) : Prop :=
  ∃ D : Finset (Finset (Fin v)),
    (∀ B ∈ D, B.card = k) ∧ ∀ T : Finset (Fin v), T.card = t → (D.filter (T ⊆ ·)).card = lam

/-- The divisibility conditions: `C(k-i, t-i) ∣ λ C(v-i, t-i)` for `i = 0, 1, …, t`. -/
def DivCond (t v k lam : ℕ) : Prop :=
  ∀ i ≤ t, (k - i).choose (t - i) ∣ lam * (v - i).choose (t - i)

/-- Non-degenerate parameters: `2 ≤ t < k`, `k + t < v`, and `1 ≤ λ ≤ C(v-t, k-t)`. -/
def Admissible (t v k lam : ℕ) : Prop :=
  2 ≤ t ∧ t < k ∧ k + t < v ∧ 1 ≤ lam ∧ lam ≤ (v - t).choose (k - t)

/-- First clause: for `v ≥ exp(exp t)`, a design exists iff the divisibility conditions hold. -/
def Clause1 : Prop :=
  ∀ t v k lam : ℕ, Admissible t v k lam → Real.exp (Real.exp t) ≤ v →
    (HasDesign t v k lam ↔ DivCond t v k lam)

/-- Second clause: for some absolute constant `c`, the same holds for `v ≥ t^(c t)`. -/
def Clause2 : Prop :=
  ∃ c : ℝ, ∀ t v k lam : ℕ, Admissible t v k lam → (t : ℝ) ^ (c * t) ≤ v →
    (HasDesign t v k lam ↔ DivCond t v k lam)

section General

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] {k : ℕ} {blk : ι → Finset α}

omit [Fintype α] in
lemma exists_blk (hd : IsDesign 2 k 1 blk) {x y : α} (hxy : x ≠ y) :
    ∃ i, x ∈ blk i ∧ y ∈ blk i := by
  have h := hd.2 {x, y} (card_pair hxy)
  obtain ⟨i, hi⟩ := card_pos.mp (by rw [h]; exact one_pos)
  rw [mem_filter, insert_subset_iff, singleton_subset_iff] at hi
  exact ⟨i, hi.2⟩

omit [Fintype α] in
lemma blk_unique (hd : IsDesign 2 k 1 blk) {x y : α} (hxy : x ≠ y) {i j : ι}
    (hi : x ∈ blk i ∧ y ∈ blk i) (hj : x ∈ blk j ∧ y ∈ blk j) : i = j := by
  have h := hd.2 {x, y} (card_pair hxy)
  exact card_le_one.mp h.le i (by simp [insert_subset_iff, hi]) j
    (by simp [insert_subset_iff, hj])

/-- The `λ = 1` case of Fisher's inequality, in the form `k (k-1) ≤ v - 1`: in a `2`-`(v,k,1)`
design with `2 ≤ k < v`, a point `x` outside a block `B₀` lies in at least `k` blocks (one through
each point of `B₀`) and in at most `(v-1)/(k-1)` blocks (these blocks are disjoint off `x`). -/
theorem fisher_bound (hd : IsDesign 2 k 1 blk) (hk : 2 ≤ k) (hv : k < Fintype.card α) :
    k * (k - 1) ≤ Fintype.card α - 1 := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card α)
  obtain ⟨i0, -⟩ := exists_blk hd hab
  obtain ⟨x, -, hx⟩ := exists_mem_notMem_of_card_lt_card
    (s := blk i0) (t := univ) (by rw [hd.1 i0, card_univ]; exact hv)
  set S := univ.filter fun i => x ∈ blk i with hS
  -- lower bound: each point `y` of `B₀` gives a block through `x, y`, all distinct
  have h1 : (blk i0).card * 1 ≤ S.card * 1 := by
    apply card_mul_le_card_mul (fun y i => y ∈ blk i)
    · intro y hy
      have hxy : x ≠ y := fun h => hx (h ▸ hy)
      obtain ⟨i, hxi, hyi⟩ := exists_blk hd hxy
      exact card_pos.mpr ⟨i, by simp [mem_bipartiteAbove, hS, hxi, hyi]⟩
    · intro i hi
      rw [card_le_one]
      intro y hy z hz
      simp only [mem_bipartiteBelow] at hy hz
      by_contra hyz
      have hxi : x ∈ blk i := (mem_filter.mp hi).2
      have := blk_unique hd hyz ⟨hy.1, hz.1⟩ ⟨hy.2, hz.2⟩
      exact hx (this ▸ hxi)
  -- upper bound: the blocks through `x` cover each other point at most once
  have h2 : S.card * (k - 1) ≤ (univ.erase x).card * 1 := by
    apply card_mul_le_card_mul (fun i y => y ∈ blk i)
    · intro i hi
      have hxi : x ∈ blk i := (mem_filter.mp hi).2
      have : (univ.erase x).bipartiteAbove (fun i y => y ∈ blk i) i = (blk i).erase x := by
        ext y; simp [mem_bipartiteAbove, and_comm]
      rw [this, card_erase_of_mem hxi, hd.1 i]
    · intro y hy
      have hxy : x ≠ y := fun h => (mem_erase.mp hy).1 h.symm
      rw [card_le_one]
      intro i hi j hj
      simp only [mem_bipartiteBelow, hS, mem_filter, mem_univ, true_and] at hi hj
      exact blk_unique hd hxy hi hj
  rw [hd.1 i0, mul_one, mul_one] at h1
  rw [card_erase_of_mem (mem_univ x), card_univ, mul_one] at h2
  calc k * (k - 1) ≤ S.card * (k - 1) := Nat.mul_le_mul_right _ h1
    _ ≤ _ := h2

end General

/-- The family `v = (m-1)^2 (m+1)`. -/
def vF (m : ℕ) : ℕ := (m - 1) ^ 2 * (m + 1)

/-- The family `k = m (m-1)`. -/
def kF (m : ℕ) : ℕ := m * (m - 1)

lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]

/-- Closed forms of the family for `m = p + 3`. -/
lemma family_eqs (p : ℕ) :
    vF (p + 3) = (p + 2) ^ 2 * (p + 4) ∧ kF (p + 3) = (p + 3) * (p + 2) ∧
      vF (p + 3) - 1 = (p + 3) * (p ^ 2 + 5 * p + 5) ∧ kF (p + 3) - 1 = p ^ 2 + 5 * p + 5 := by
  have hv : vF (p + 3) = (p + 2) ^ 2 * (p + 4) := by
    simp only [vF, show p + 3 - 1 = p + 2 by omega]
  have hk : kF (p + 3) = (p + 3) * (p + 2) := by
    simp only [kF, show p + 3 - 1 = p + 2 by omega]
  refine ⟨hv, hk, ?_, ?_⟩
  · rw [hv]
    have : (p + 2) ^ 2 * (p + 4) = (p + 3) * (p ^ 2 + 5 * p + 5) + 1 := by ring
    omega
  · rw [hk]
    have : (p + 3) * (p + 2) = p ^ 2 + 5 * p + 5 + 1 := by ring
    omega

theorem family_admissible (m : ℕ) (hm : 3 ≤ m) : Admissible 2 (vF m) (kF m) 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 3 := ⟨m - 3, by omega⟩
  obtain ⟨hv, hk, -, -⟩ := family_eqs p
  have h1 : 2 < kF (p + 3) := by rw [hk]; nlinarith
  have h2 : kF (p + 3) + 2 < vF (p + 3) := by rw [hk, hv]; nlinarith
  exact ⟨le_rfl, h1, h2, le_rfl, Nat.choose_pos (by omega)⟩

theorem family_divCond (m : ℕ) (hm : 3 ≤ m) : DivCond 2 (vF m) (kF m) 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 3 := ⟨m - 3, by omega⟩
  obtain ⟨hv, hk, hv1, hk1⟩ := family_eqs p
  intro i hi
  interval_cases i
  · -- `i = 0`: `C(k,2) ∣ C(v,2)`, quotient `b = m^2 - 1 = (p+2)(p+4)`
    refine ⟨(p + 2) * (p + 4), ?_⟩
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    simp only [one_mul, Nat.sub_zero]
    rw [two_mul_choose_two, ← mul_assoc, two_mul_choose_two, hv1, hk1, hv, hk]
    ring
  · -- `i = 1`: `k - 1 ∣ v - 1`, quotient `r = m = p + 3`
    simp only [Nat.choose_one_right, one_mul, show 2 - 1 = 1 from rfl]
    exact ⟨p + 3, by rw [hv1, hk1, mul_comm]⟩
  · simp

/-- No `2`-`(v,k,1)` design exists for the family, for any `m ≥ 3`. -/
theorem family_no_design (m : ℕ) (hm : 3 ≤ m) : ¬ HasDesign 2 (vF m) (kF m) 1 := by
  rintro ⟨b, blk, hd⟩
  obtain ⟨-, hkt, hkv, -⟩ := family_admissible m hm
  have hF := fisher_bound hd (by omega) (by rw [Fintype.card_fin]; omega)
  rw [Fintype.card_fin] at hF
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 3 := ⟨m - 3, by omega⟩
  obtain ⟨-, hk, hv1, hk1⟩ := family_eqs p
  rw [hv1, hk1, hk] at hF
  -- `k (k-1) ≤ m (k-1)` with `k - 1 > 0` gives `k ≤ m`, false since `k = m (m-1)`
  have hle : (p + 3) * (p + 2) ≤ p + 3 :=
    Nat.le_of_mul_le_mul_right hF (by positivity)
  nlinarith

/-- Simple designs are indexed designs, so they do not exist either. -/
theorem family_no_simple_design (m : ℕ) (hm : 3 ≤ m) :
    ¬ HasSimpleDesign 2 (vF m) (kF m) 1 := by
  rintro ⟨D, hcard, hT⟩
  obtain ⟨-, hkt, hkv, -⟩ := family_admissible m hm
  have hd : IsDesign 2 (kF m) 1 (fun B : D => B.1) := by
    refine ⟨fun B => hcard B.1 B.2, fun T hT2 => ?_⟩
    rw [← hT T hT2, ← card_map (Function.Embedding.subtype _)]
    congr 1
    ext B
    simp [and_comm]
  have hF := fisher_bound hd (by omega) (by rw [Fintype.card_fin]; omega)
  rw [Fintype.card_fin] at hF
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 3 := ⟨m - 3, by omega⟩
  obtain ⟨-, hk, hv1, hk1⟩ := family_eqs p
  rw [hv1, hk1, hk] at hF
  have hle : (p + 3) * (p + 2) ≤ p + 3 :=
    Nat.le_of_mul_le_mul_right hF (by positivity)
  nlinarith

/-- For every threshold function `T : ℕ → ℝ` (depending on `t` only) there are admissible
parameters with `v > T t`, all divisibility conditions satisfied, and no design, simple or not. -/
theorem exists_counterexample (T : ℕ → ℝ) :
    ∃ t v k lam : ℕ, Admissible t v k lam ∧ T t < v ∧ DivCond t v k lam ∧
      ¬ HasDesign t v k lam ∧ ¬ HasSimpleDesign t v k lam := by
  obtain ⟨N, hN⟩ := exists_nat_gt (T 2)
  refine ⟨2, vF (N + 3), kF (N + 3), 1, family_admissible _ (by omega), ?_,
    family_divCond _ (by omega), family_no_design _ (by omega),
    family_no_simple_design _ (by omega)⟩
  have hv : N ≤ vF (N + 3) := by
    rw [(family_eqs N).1]; nlinarith
  calc T 2 < N := hN
    _ ≤ _ := by exact_mod_cast hv

/-- No threshold depending on `t` alone makes the divisibility conditions sufficient. -/
theorem threshold_fails (T : ℕ → ℝ) :
    ¬ ∀ t v k lam : ℕ, Admissible t v k lam → T t ≤ v → DivCond t v k lam →
      HasDesign t v k lam := by
  intro h
  obtain ⟨t, v, k, lam, hA, hT, hD, hN, -⟩ := exists_counterexample T
  exact hN (h t v k lam hA hT.le hD)

theorem not_clause1 : ¬ Clause1 := fun h =>
  threshold_fails (fun t => Real.exp (Real.exp t)) fun t v k lam hA hT hD =>
    (h t v k lam hA hT).2 hD

theorem not_clause2 : ¬ Clause2 := by
  rintro ⟨c, h⟩
  exact threshold_fails (fun t => (t : ℝ) ^ (c * t)) fun t v k lam hA hT hD =>
    (h t v k lam hA hT).2 hD

/-- Conjecture 00000008433 is false: both the `exp(exp t)` clause and the `t^(ct)` clause
(for every real constant `c`) fail. -/
theorem conjecture8433_false : ¬ Clause1 ∧ ¬ Clause2 := ⟨not_clause1, not_clause2⟩

/-- The member `m = 13` of the family is the `2`-`(2016,156,1)` parameter set. -/
theorem witness_13 : vF 13 = 2016 ∧ kF 13 = 156 ∧ DivCond 2 2016 156 1 ∧
    ¬ HasDesign 2 2016 156 1 := by
  have hv : vF 13 = 2016 := by norm_num [vF]
  have hk : kF 13 = 156 := by norm_num [kF]
  refine ⟨hv, hk, ?_, ?_⟩
  · simpa [hv, hk] using family_divCond 13 (by norm_num)
  · simpa [hv, hk] using family_no_design 13 (by norm_num)

end Conjecture8433
