import Mathlib

/-!
# Conjecture 00000000307 is false (under the two readings stated below)

Conjecture (verbatim): "Weighted bad approximation Bad(i,j) is the set of pairs simultaneously
badly approximable when the two coordinates are weighted by q^{1+i} and q^{1+j}. Conjecture: For
i+j = 0, Bad(i,j) is a full-dimensional winning set; moreover, for every weighting with i+j < 0,
the intersection remains full-dimensional, with winning given explicitly by a Schmidt-game
strategy."

The phrase "weighted by q^{1+i}" admits two literal readings, both formalized here.

* Reading A (`BadA`): the weight multiplies the approximation error `|x - p/q|`:
  `(x, y) ∈ BadA i j` iff there is `c > 0` such that for all integers `q ≥ 1`, `p`, `r`,
  `max (q^{1+i} |x - p/q|, q^{1+j} |y - r/q|) ≥ c`.
* Reading B (`BadB`): the weight multiplies `‖q x‖ = min_p |q x - p|`:
  `(x, y) ∈ BadB i j` iff there is `c > 0` such that for all integers `q ≥ 1`, `p`, `r`,
  `max (q^{1+i} |q x - p|, q^{1+j} |q y - r|) ≥ c`.

The maximum is written as a disjunction; requiring both inequalities, or a strict inequality,
gives a smaller set, which is then empty as well.  The pairs live in the Euclidean plane
`EuclideanSpace ℝ (Fin 2)` (as in the accepted solution of conjecture 00000000310, whose
`dimH_empty` pattern is reused here); `q^{1+i}` is the real power `Real.rpow`, and `i, j` range
over the reals (integer weights are a special case).

Key fact: a two-dimensional Dirichlet theorem proved below by pigeonhole (`dirichlet_two`).
Consequences:
* `BadA i j = ∅` whenever `i ≤ 0` and `j ≤ 0`; in particular `BadA 0 0 = ∅`, so the first clause
  (i+j = 0) fails under reading A, and every subset of `BadA (-1/2) (-1/2)` (for example any
  intersection involving it) is empty, so the second clause fails as well.
* `BadB i j = ∅` whenever `i ≤ -3/4` and `j ≤ -3/4`; so the second clause (i+j < 0) fails under
  reading B.  The first clause under reading B is NOT refuted here.
The empty set has Hausdorff dimension `0 ≠ 2`.  The "winning" conjuncts are not formalized; the
failure of the full-dimension conjunct suffices.
-/

noncomputable section

namespace Conjecture307

open Set

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Reading A: the weights `q^{1+i}`, `q^{1+j}` multiply the errors `|x - p/q|`, `|y - r/q|`. -/
def BadA (i j : ℝ) : Set Plane :=
  {v | ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 0 < q → ∀ p r : ℤ,
    c ≤ (q : ℝ) ^ (1 + i) * |v 0 - p / q| ∨ c ≤ (q : ℝ) ^ (1 + j) * |v 1 - r / q|}

/-- Reading B: the weights `q^{1+i}`, `q^{1+j}` multiply `‖q x‖`, `‖q y‖`; the distance to the
nearest integer is written as the quantifier over all integers `p`, `r`. -/
def BadB (i j : ℝ) : Set Plane :=
  {v | ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 0 < q → ∀ p r : ℤ,
    c ≤ (q : ℝ) ^ (1 + i) * |q * v 0 - p| ∨ c ≤ (q : ℝ) ^ (1 + j) * |q * v 1 - r|}

/-- If two reals `k t`, `l t` have fractional parts in the same box of width `1/N`, then
`(k - l) t` is within `1/N` of an integer. -/
theorem close_of_floor_eq {N : ℕ} (hN : 0 < N) (k l : ℕ) (t : ℝ) (hlk : l < k)
    (h : ⌊Int.fract ((k : ℝ) * t) * N⌋ = ⌊Int.fract ((l : ℝ) * t) * N⌋) :
    |((k - l : ℕ) : ℝ) * t - ((⌊(k : ℝ) * t⌋ - ⌊(l : ℝ) * t⌋ : ℤ) : ℝ)| < 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  have e : ((k - l : ℕ) : ℝ) * t - ((⌊(k : ℝ) * t⌋ - ⌊(l : ℝ) * t⌋ : ℤ) : ℝ)
      = Int.fract ((k : ℝ) * t) - Int.fract ((l : ℝ) * t) := by
    rw [Nat.cast_sub hlk.le]; push_cast; simp only [Int.fract]; ring
  rw [e, lt_div_iff₀ hNr]
  calc |Int.fract ((k : ℝ) * t) - Int.fract ((l : ℝ) * t)| * N
      = |Int.fract ((k : ℝ) * t) * N - Int.fract ((l : ℝ) * t) * N| := by
        rw [← sub_mul, abs_mul, abs_of_pos hNr]
    _ < 1 := h1

/-- **Two-dimensional Dirichlet theorem** (pigeonhole on `N^2 + 1` points in `N^2` boxes):
for all reals `x, y` and every `N ≥ 1` there are `1 ≤ q ≤ N^2` and integers `p, r` with
`|q x - p| < 1/N` and `|q y - r| < 1/N`. -/
theorem dirichlet_two (x y : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ^ 2 ∧ ∃ p r : ℤ,
      |(q : ℝ) * x - p| < 1 / N ∧ |(q : ℝ) * y - r| < 1 / N := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let f : ℕ → ℤ × ℤ := fun k =>
    (⌊Int.fract ((k : ℝ) * x) * N⌋, ⌊Int.fract ((k : ℝ) * y) * N⌋)
  have hbox : ∀ t : ℝ, ⌊Int.fract t * N⌋ ∈ Finset.Ico (0 : ℤ) N := by
    intro t
    rw [Finset.mem_Ico]
    constructor
    · exact Int.floor_nonneg.mpr (mul_nonneg (Int.fract_nonneg t) hNr.le)
    · rw [Int.floor_lt]
      push_cast
      exact mul_lt_of_lt_one_left hNr (Int.fract_lt_one t)
  have hmaps : Set.MapsTo f (Finset.range (N ^ 2 + 1) : Set ℕ)
      (Finset.Ico (0 : ℤ) N ×ˢ Finset.Ico (0 : ℤ) N : Finset (ℤ × ℤ)) := by
    intro k _
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, f]
    exact ⟨hbox _, hbox _⟩
  have hcard : (Finset.Ico (0 : ℤ) N ×ˢ Finset.Ico (0 : ℤ) N).card
      < (Finset.range (N ^ 2 + 1)).card := by
    rw [Finset.card_product, Int.card_Ico, Finset.card_range]
    simp [sq]
  obtain ⟨a, ha, b, hb, hab, hfab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have main : ∀ k l : ℕ, k ∈ Finset.range (N ^ 2 + 1) → l < k → f k = f l →
      ∃ q : ℕ, 0 < q ∧ q ≤ N ^ 2 ∧ ∃ p r : ℤ,
        |(q : ℝ) * x - p| < 1 / N ∧ |(q : ℝ) * y - r| < 1 / N := by
    intro k l hk hlk hf
    simp only [f, Prod.mk.injEq] at hf
    rw [Finset.mem_range] at hk
    exact ⟨k - l, by omega, by omega, _, _, close_of_floor_eq hN k l x hlk hf.1,
      close_of_floor_eq hN k l y hlk hf.2⟩
  rcases lt_or_gt_of_ne hab with h | h
  · exact main b a hb h hfab.symm
  · exact main a b ha h hfab

/-- For every `c > 0` there is a natural number `M ≥ 1` with `1/M < c`. -/
theorem exists_inv_lt {c : ℝ} (hc : 0 < c) : ∃ M : ℕ, 0 < M ∧ 1 / (M : ℝ) < c := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
  exact ⟨n + 1, n.succ_pos, by exact_mod_cast hn⟩

/-- `q * |x - p/q| = |q x - p|` for `q > 0`. -/
theorem mul_abs_sub_div (q : ℕ) (hq : 0 < q) (x : ℝ) (p : ℤ) :
    (q : ℝ) * |x - p / q| = |(q : ℝ) * x - p| := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [← abs_of_pos hq', ← abs_mul, abs_of_pos hq']
  congr 1
  field_simp

/-- For `q ≥ 1` and `e ≤ 1`, `q^e ≤ q`. -/
theorem rpow_le_self_of_le_one (q : ℕ) (hq : 0 < q) {e : ℝ} (he : e ≤ 1) :
    (q : ℝ) ^ e ≤ q := by
  have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  calc (q : ℝ) ^ e ≤ (q : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 he
    _ = q := Real.rpow_one _

/-- **Reading A**: `BadA i j` is empty whenever `i ≤ 0` and `j ≤ 0`. -/
theorem badA_eq_empty {i j : ℝ} (hi : i ≤ 0) (hj : j ≤ 0) : BadA i j = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro v ⟨c, hc, hv⟩
  obtain ⟨M, hM, hMc⟩ := exists_inv_lt hc
  obtain ⟨q, hq, -, p, r, hp, hr⟩ := dirichlet_two (v 0) (v 1) hM
  have key : ∀ (e : ℝ) (t : ℝ) (s : ℤ), e ≤ 1 → |(q : ℝ) * t - s| < 1 / M →
      (q : ℝ) ^ e * |t - s / q| < c := by
    intro e t s he hts
    calc (q : ℝ) ^ e * |t - s / q| ≤ (q : ℝ) * |t - s / q| :=
          mul_le_mul_of_nonneg_right (rpow_le_self_of_le_one q hq he) (abs_nonneg _)
      _ = |(q : ℝ) * t - s| := mul_abs_sub_div q hq t s
      _ < 1 / M := hts
      _ < c := hMc
  rcases hv q hq p r with h | h
  · exact absurd h (not_le.mpr (key _ _ _ (by linarith) hp))
  · exact absurd h (not_le.mpr (key _ _ _ (by linarith) hr))

/-- For `1 ≤ q ≤ M^4` and `e ≤ 1/4`, `q^e ≤ M`. -/
theorem rpow_le_of_le_pow_four (q M : ℕ) (hq : 0 < q) (hqM : q ≤ (M ^ 2) ^ 2) {e : ℝ}
    (he : e ≤ 1 / 4) : (q : ℝ) ^ e ≤ M := by
  have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqM' : (q : ℝ) ≤ (M : ℝ) ^ 4 := by
    have : q ≤ M ^ 4 := by rw [← pow_mul] at hqM; exact hqM
    exact_mod_cast this
  have hM4 : ((M : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = M := by
    have := Real.pow_rpow_inv_natCast (x := (M : ℝ)) (n := 4) (by positivity) (by norm_num)
    rw [show ((1 : ℝ) / 4) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact this
  calc (q : ℝ) ^ e ≤ (q : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le h1 he
    _ ≤ ((M : ℝ) ^ 4) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) hqM' (by norm_num)
    _ = M := hM4

/-- **Reading B**: `BadB i j` is empty whenever `i ≤ -3/4` and `j ≤ -3/4`. -/
theorem badB_eq_empty {i j : ℝ} (hi : i ≤ -3 / 4) (hj : j ≤ -3 / 4) : BadB i j = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro v ⟨c, hc, hv⟩
  obtain ⟨M, hM, hMc⟩ := exists_inv_lt hc
  have hM2 : 0 < M ^ 2 := by positivity
  obtain ⟨q, hq, hqM, p, r, hp, hr⟩ := dirichlet_two (v 0) (v 1) hM2
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have key : ∀ (e : ℝ) (t : ℝ) (s : ℤ), e ≤ 1 / 4 →
      |(q : ℝ) * t - s| < 1 / ((M ^ 2 : ℕ) : ℝ) → (q : ℝ) ^ e * |(q : ℝ) * t - s| < c := by
    intro e t s he hts
    calc (q : ℝ) ^ e * |(q : ℝ) * t - s| ≤ (M : ℝ) * |(q : ℝ) * t - s| :=
          mul_le_mul_of_nonneg_right (rpow_le_of_le_pow_four q M hq hqM he) (abs_nonneg _)
      _ < (M : ℝ) * (1 / ((M ^ 2 : ℕ) : ℝ)) := mul_lt_mul_of_pos_left hts hMr
      _ = 1 / M := by push_cast; field_simp
      _ < c := hMc
  rcases hv q hq p r with h | h
  · exact absurd h (not_le.mpr (key _ _ _ (by linarith) hp))
  · exact absurd h (not_le.mpr (key _ _ _ (by linarith) hr))

/-! ### The two clauses of the conjecture -/

/-- First clause, reading A: "for i+j = 0, Bad(i,j) is full-dimensional" fails (at `(0,0)`). -/
theorem clause1_false_readingA : ¬ ∀ i j : ℝ, i + j = 0 → dimH (BadA i j) = 2 := by
  intro h
  have h0 := h 0 0 (by norm_num)
  rw [badA_eq_empty le_rfl le_rfl, dimH_empty] at h0
  norm_num at h0

/-- Second clause, reading A: for any choice of "intersections" `I i j ⊆ BadA i j`, the claim that
`I i j` is full-dimensional for every weighting with `i + j < 0` fails (at `(-1/2, -1/2)`). -/
theorem clause2_false_readingA (I : ℝ → ℝ → Set Plane) (hI : ∀ i j, I i j ⊆ BadA i j) :
    ¬ ∀ i j : ℝ, i + j < 0 → dimH (I i j) = 2 := by
  intro h
  have h0 := h (-1 / 2) (-1 / 2) (by norm_num)
  rw [Set.subset_eq_empty (hI _ _) (badA_eq_empty (by norm_num) (by norm_num)), dimH_empty] at h0
  norm_num at h0

/-- Second clause, reading B: for any choice of "intersections" `I i j ⊆ BadB i j`, the claim that
`I i j` is full-dimensional for every weighting with `i + j < 0` fails (at `(-3/4, -3/4)`). -/
theorem clause2_false_readingB (I : ℝ → ℝ → Set Plane) (hI : ∀ i j, I i j ⊆ BadB i j) :
    ¬ ∀ i j : ℝ, i + j < 0 → dimH (I i j) = 2 := by
  intro h
  have h0 := h (-3 / 4) (-3 / 4) (by norm_num)
  rw [Set.subset_eq_empty (hI _ _) (badB_eq_empty le_rfl le_rfl), dimH_empty] at h0
  norm_num at h0

/-- The intersection over all weightings with `i + j < 0` (reading A) has dimension `0`. -/
theorem dimH_iInter_badA :
    dimH (⋂ w : {w : ℝ × ℝ // w.1 + w.2 < 0}, BadA w.1.1 w.1.2) = 0 := by
  have hsub : (⋂ w : {w : ℝ × ℝ // w.1 + w.2 < 0}, BadA w.1.1 w.1.2) ⊆ BadA (-1 / 2) (-1 / 2) :=
    Set.iInter_subset_of_subset ⟨(-1 / 2, -1 / 2), by norm_num⟩ le_rfl
  rw [Set.subset_eq_empty hsub (badA_eq_empty (by norm_num) (by norm_num)), dimH_empty]

/-- The intersection over all weightings with `i + j < 0` (reading B) has dimension `0`. -/
theorem dimH_iInter_badB :
    dimH (⋂ w : {w : ℝ × ℝ // w.1 + w.2 < 0}, BadB w.1.1 w.1.2) = 0 := by
  have hsub : (⋂ w : {w : ℝ × ℝ // w.1 + w.2 < 0}, BadB w.1.1 w.1.2) ⊆ BadB (-3 / 4) (-3 / 4) :=
    Set.iInter_subset_of_subset ⟨(-3 / 4, -3 / 4), by norm_num⟩ le_rfl
  rw [Set.subset_eq_empty hsub (badB_eq_empty le_rfl le_rfl), dimH_empty]

/-- **Main theorem.** Under reading A both clauses fail; under reading B the second clause fails. -/
theorem conjecture307_false :
    (¬ ∀ i j : ℝ, i + j = 0 → dimH (BadA i j) = 2) ∧
    (∀ I : ℝ → ℝ → Set Plane, (∀ i j, I i j ⊆ BadA i j) →
      ¬ ∀ i j : ℝ, i + j < 0 → dimH (I i j) = 2) ∧
    (∀ I : ℝ → ℝ → Set Plane, (∀ i j, I i j ⊆ BadB i j) →
      ¬ ∀ i j : ℝ, i + j < 0 → dimH (I i j) = 2) :=
  ⟨clause1_false_readingA, clause2_false_readingA, clause2_false_readingB⟩

end Conjecture307
