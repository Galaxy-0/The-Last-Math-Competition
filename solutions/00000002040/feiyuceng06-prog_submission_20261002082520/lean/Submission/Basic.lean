import Mathlib

/-!
# Conjecture 00000002040 is false

A set `A` is *3-independent* if it contains no solution of `x + y = z`, i.e. it is
sum-free. Conjecture 00000002040 asserts that the density of the largest
3-independent subset of `[n] = {1, …, n}` has a limit, that the limit is at most
`1/4`, and that it is exactly `1/4`.

The largest 3-independent subset of `[n]` has exactly `⌈n/2⌉ = ⌊(n+1)/2⌋`
elements, so the density tends to `1/2`.

* The odd numbers of `[n]` form a 3-independent set, since a sum of two odd
  numbers is even.
* Let `A ⊆ [n]` be 3-independent with largest element `m`. For `a ∈ A`, `a < m`,
  the number `m - a` is not in `A`, since otherwise `a + (m - a) = m` would be a
  solution. So `A` and `{m - a : a ∈ A, a < m}` are disjoint subsets of `[m]`,
  which gives `2|A| - 1 ≤ m ≤ n`.
-/

namespace Submission00000002040

open Filter Topology

/-- `A` is 3-independent: it contains no solution of `x + y = z` (with `x, y, z ∈ A`,
not necessarily distinct). -/
def IsThreeIndependent (A : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y ≠ z

instance : DecidablePred IsThreeIndependent := fun A => by
  unfold IsThreeIndependent
  infer_instance

/-- The size of a largest 3-independent subset of `[n] = {1, …, n}`. -/
def maxSize (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter IsThreeIndependent).sup Finset.card

/-- The density `maxSize n / n` of the largest 3-independent subset of `[n]`. -/
noncomputable def density (n : ℕ) : ℝ := (maxSize n : ℝ) / n

/-- Conjecture 00000002040: the density limit exists and is at most `1/4`, and the
limit is exactly `1/4`. -/
def ConjectureHolds : Prop :=
  (∃ L : ℝ, L ≤ 1 / 4 ∧ Tendsto density atTop (𝓝 L)) ∧ Tendsto density atTop (𝓝 (1 / 4))

/-! ## The odd numbers -/

/-- The odd numbers in `[n]`. -/
def odds (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter Odd

theorem card_odds (n : ℕ) : (odds n).card = (n + 1) / 2 := by
  have h : odds n = (Finset.range ((n + 1) / 2)).image (fun k => 2 * k + 1) := by
    ext x
    simp only [odds, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range,
      Nat.odd_iff]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨x / 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [h, Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range]

/-- A sum of two odd numbers is even, hence never odd. -/
theorem isThreeIndependent_odds (n : ℕ) : IsThreeIndependent (odds n) := by
  intro x hx y hy z hz hxyz
  simp only [odds, Finset.mem_filter] at hx hy hz
  have : Even (x + y) := hx.2.add_odd hy.2
  rw [hxyz] at this
  exact Nat.not_even_iff_odd.2 hz.2 this

/-! ## The upper bound -/

/-- A 3-independent subset of `[n]` has at most `⌊(n+1)/2⌋` elements. -/
theorem card_le_of_isThreeIndependent {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 n)
    (hind : IsThreeIndependent A) : A.card ≤ (n + 1) / 2 := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  set m := A.max' hne with hm
  have hmA : m ∈ A := A.max'_mem hne
  set B := (A.erase m).image (fun a => m - a) with hB
  have hBcard : B.card = A.card - 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem hmA]
    intro a ha b hb hab
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at ha hb
    have ha' := A.le_max' a ha.1
    have hb' := A.le_max' b hb.1
    simp only at hab
    omega
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hxB
    have haA := Finset.mem_of_mem_erase ha
    have hale : a ≤ m := A.le_max' a haA
    exact hind a haA (m - a) hxA m hmA (by omega)
  have hsub : A ∪ B ⊆ Finset.Icc 1 m := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · have := hA h
      rw [Finset.mem_Icc] at this ⊢
      exact ⟨this.1, A.le_max' x h⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      have haA := Finset.mem_of_mem_erase ha
      have ham : a ≠ m := Finset.ne_of_mem_erase ha
      have hale : a ≤ m := A.le_max' a haA
      have ha1 := (Finset.mem_Icc.1 (hA haA)).1
      rw [Finset.mem_Icc]
      omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hBcard, Nat.card_Icc] at hcard
  have hmn : m ≤ n := (Finset.mem_Icc.1 (hA hmA)).2
  have hpos : 0 < A.card := Finset.card_pos.2 hne
  omega

/-- The largest 3-independent subset of `[n]` has exactly `⌊(n+1)/2⌋ = ⌈n/2⌉`
elements. -/
theorem maxSize_eq (n : ℕ) : maxSize n = (n + 1) / 2 := by
  apply le_antisymm
  · refine Finset.sup_le fun A hA => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    exact card_le_of_isThreeIndependent hA.1 hA.2
  · rw [← card_odds n]
    refine Finset.le_sup (f := Finset.card) ?_
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _, isThreeIndependent_odds n⟩

/-! ## The density tends to `1/2` -/

theorem half_le_density {n : ℕ} (hn : 1 ≤ n) : 1 / 2 ≤ density n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * ((n + 1) / 2) := by omega
    exact_mod_cast this
  rw [density, maxSize_eq, le_div_iff₀ hnpos]
  linarith

theorem density_le {n : ℕ} (hn : 1 ≤ n) : density n ≤ 1 / 2 + 1 / (2 * n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : 2 * (((n + 1) / 2 : ℕ) : ℝ) ≤ n + 1 := by
    have : 2 * ((n + 1) / 2) ≤ n + 1 := by omega
    exact_mod_cast this
  rw [density, maxSize_eq, div_le_iff₀ hnpos]
  field_simp
  linarith

/-- The density of the largest 3-independent subset of `[n]` tends to `1/2`. -/
theorem tendsto_density : Tendsto density atTop (𝓝 (1 / 2)) := by
  have hupper : Tendsto (fun n : ℕ => (1 / 2 : ℝ) + 1 / (2 * n)) atTop (𝓝 (1 / 2)) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ)
    rw [mul_zero] at h
    have h' := h.const_add (1 / 2 : ℝ)
    rw [add_zero] at h'
    refine h'.congr fun n => ?_
    rw [one_div_mul_eq_div, div_div, mul_comm]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn using half_le_density hn
  · filter_upwards [eventually_ge_atTop 1] with n hn using density_le hn

/-- Conjecture 00000002040 is false: the density tends to `1/2`, so it has no limit
`≤ 1/4`, and in particular it does not tend to `1/4`. -/
theorem conjecture_00000002040_false : ¬ ConjectureHolds := by
  rintro ⟨⟨L, hL, hlim⟩, -⟩
  have := tendsto_nhds_unique hlim tendsto_density
  linarith

end Submission00000002040

#print axioms Submission00000002040.conjecture_00000002040_false
