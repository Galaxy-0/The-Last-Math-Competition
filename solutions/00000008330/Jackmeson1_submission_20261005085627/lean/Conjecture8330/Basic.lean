import Mathlib

/-!
# Conjecture 00000008330: the "double gap law" for `C - C` is false

`C` is the middle-thirds Cantor set (Mathlib's `cantorSet`, the intersection of the
pre-Cantor sets obtained from `[0,1]` by repeatedly removing open middle thirds).
The difference set is `C - C = {x - y | x ∈ C, y ∈ C}` (pointwise subtraction).

The conjecture's second clause says that the complete list of gaps (complementary
intervals) of `C - C` is the "double gap" `(-2,-1) ∪ (1,2)`.  Since `C ⊆ [0,1]`, we have
`C - C ⊆ [-1,1]` and `±1 ∈ C - C`; hence `(1,2)` and `(-2,-1)` are not complementary
intervals of `C - C` under any of the readings formalized below:

* (R1) complement reading: `(C - C)ᶜ = (-2,-1) ∪ (1,2)` -- false, `3` is in the complement;
* (R2) gap = bounded connected component of `ℝ \ (C - C)` -- `(1,2)` and `(-2,-1)` are not
  connected components of the complement at all (the component of `3/2` contains `3`);
* (R3) gap = connected component of `[-2,2] \ (C - C)` -- the component of `3/2` contains `2`;
* (R4) gap = connected component of `[inf, sup] \ (C - C) = [-1,1] \ (C - C)` (bounded
  complementary intervals inside the convex hull) -- `3/2` is not even in `[-1,1]`.
-/

open Set Pointwise

namespace C8330

/-- `1` lies in every pre-Cantor set (`1 = (2 + 1) / 3`). -/
lemma one_mem_preCantorSet (n : ℕ) : (1 : ℝ) ∈ preCantorSet n := by
  induction n with
  | zero => simp
  | succ n ih => exact Or.inr ⟨1, ih, by norm_num⟩

lemma one_mem_cantorSet : (1 : ℝ) ∈ cantorSet := Set.mem_iInter.mpr one_mem_preCantorSet

/-- `C - C ⊆ [-1,1]`, because `C ⊆ [0,1]`. -/
lemma sub_subset_Icc : cantorSet - cantorSet ⊆ Icc (-1 : ℝ) 1 := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have hx' := cantorSet_subset_unitInterval hx
  have hy' := cantorSet_subset_unitInterval hy
  simp only [mem_Icc] at hx' hy' ⊢
  constructor <;> linarith

lemma one_mem_sub : (1 : ℝ) ∈ cantorSet - cantorSet :=
  ⟨1, one_mem_cantorSet, 0, zero_mem_cantorSet, by norm_num⟩

lemma neg_one_mem_sub : (-1 : ℝ) ∈ cantorSet - cantorSet :=
  ⟨0, zero_mem_cantorSet, 1, one_mem_cantorSet, by norm_num⟩

/-- `C - C` is bounded above by `1` and below by `-1`, and attains both: its convex hull
(the interval between its infimum and supremum) is `[-1,1]`. -/
lemma sSup_sub : sSup (cantorSet - cantorSet : Set ℝ) = 1 :=
  IsGreatest.csSup_eq ⟨one_mem_sub, fun _ h => (sub_subset_Icc h).2⟩

lemma sInf_sub : sInf (cantorSet - cantorSet : Set ℝ) = -1 :=
  IsLeast.csInf_eq ⟨neg_one_mem_sub, fun _ h => (sub_subset_Icc h).1⟩

/-- Everything to the right of `1` (or left of `-1`) lies in `ℝ \ (C - C)`. -/
lemma Ioi_subset_compl : Ioi (1 : ℝ) ⊆ (cantorSet - cantorSet)ᶜ := fun _ hx hmem =>
  absurd (sub_subset_Icc hmem).2 (not_le.mpr hx)

lemma Iio_subset_compl : Iio (-1 : ℝ) ⊆ (cantorSet - cantorSet)ᶜ := fun _ hx hmem =>
  absurd (sub_subset_Icc hmem).1 (not_le.mpr hx)

/-- (R1) The complement of `C - C` is not `(-2,-1) ∪ (1,2)`. -/
theorem compl_ne_double_gap :
    (cantorSet - cantorSet : Set ℝ)ᶜ ≠ Ioo (-2) (-1) ∪ Ioo 1 2 := by
  intro h
  have h3 : (3 : ℝ) ∈ (cantorSet - cantorSet : Set ℝ)ᶜ := Ioi_subset_compl (by norm_num)
  rw [h] at h3
  rcases h3 with h3 | h3 <;> norm_num at h3

/-- (R2) `(1,2)` is not a connected component of `ℝ \ (C - C)`: the component through any of
its points contains `3`. -/
theorem Ioo_one_two_not_component (x : ℝ) :
    connectedComponentIn (cantorSet - cantorSet : Set ℝ)ᶜ x ≠ Ioo 1 2 := by
  intro h
  have hx : x ∈ Ioo (1 : ℝ) 2 := h ▸ mem_connectedComponentIn (by
    by_contra hx
    rw [connectedComponentIn_eq_empty hx] at h
    exact (nonempty_Ioo.mpr (by norm_num : (1 : ℝ) < 2)).ne_empty h.symm)
  have hsub : Ioi (1 : ℝ) ⊆ connectedComponentIn (cantorSet - cantorSet : Set ℝ)ᶜ x :=
    isPreconnected_Ioi.subset_connectedComponentIn hx.1 Ioi_subset_compl
  have : (3 : ℝ) ∈ Ioo (1 : ℝ) 2 := h ▸ hsub (by norm_num : (1 : ℝ) < 3)
  norm_num at this

/-- (R2) `(-2,-1)` is not a connected component of `ℝ \ (C - C)`. -/
theorem Ioo_neg_two_neg_one_not_component (x : ℝ) :
    connectedComponentIn (cantorSet - cantorSet : Set ℝ)ᶜ x ≠ Ioo (-2) (-1) := by
  intro h
  have hx : x ∈ Ioo (-2 : ℝ) (-1) := h ▸ mem_connectedComponentIn (by
    by_contra hx
    rw [connectedComponentIn_eq_empty hx] at h
    exact (nonempty_Ioo.mpr (by norm_num : (-2 : ℝ) < -1)).ne_empty h.symm)
  have hsub : Iio (-1 : ℝ) ⊆ connectedComponentIn (cantorSet - cantorSet : Set ℝ)ᶜ x :=
    isPreconnected_Iio.subset_connectedComponentIn hx.2 Iio_subset_compl
  have : (-3 : ℝ) ∈ Ioo (-2 : ℝ) (-1) := h ▸ hsub (by norm_num : (-3 : ℝ) < -1)
  norm_num at this

/-- (R3) Relative to the ambient interval `[-2,2]`, the component of `[-2,2] \ (C - C)`
through any point of `(1,2)` contains `2`, so it is not `(1,2)`. -/
theorem Ioo_one_two_not_component_in_Icc (x : ℝ) :
    connectedComponentIn (Icc (-2 : ℝ) 2 \ (cantorSet - cantorSet)) x ≠ Ioo 1 2 := by
  intro h
  have hx : x ∈ Ioo (1 : ℝ) 2 := h ▸ mem_connectedComponentIn (by
    by_contra hx
    rw [connectedComponentIn_eq_empty hx] at h
    exact (nonempty_Ioo.mpr (by norm_num : (1 : ℝ) < 2)).ne_empty h.symm)
  have hsub : Ioc (1 : ℝ) 2 ⊆
      connectedComponentIn (Icc (-2 : ℝ) 2 \ (cantorSet - cantorSet)) x := by
    refine isPreconnected_Ioc.subset_connectedComponentIn ⟨hx.1, hx.2.le⟩ ?_
    intro y hy
    exact ⟨⟨by linarith [hy.1], hy.2⟩, Ioi_subset_compl hy.1⟩
  have : (2 : ℝ) ∈ Ioo (1 : ℝ) 2 := h ▸ hsub ⟨by norm_num, le_rfl⟩
  norm_num at this

/-- (R4) Gaps in the convex-hull sense are subsets of `[sInf (C-C), sSup (C-C)] = [-1,1]`;
`(1,2)` is not contained in this interval. -/
theorem Ioo_one_two_not_subset_hull :
    ¬ Ioo (1 : ℝ) 2 ⊆ Icc (sInf (cantorSet - cantorSet)) (sSup (cantorSet - cantorSet)) := by
  rw [sInf_sub, sSup_sub]
  intro h
  have := (h (by norm_num : (3 / 2 : ℝ) ∈ Ioo (1 : ℝ) 2)).2
  norm_num at this

/-- A *gap* of a set `S ⊆ ℝ` (standard meaning): a bounded connected component of `ℝ \ S`. -/
def IsGap (S I : Set ℝ) : Prop :=
  (∃ x ∈ Sᶜ, connectedComponentIn Sᶜ x = I) ∧ Bornology.IsBounded I

/-- **Main theorem.** The double gap law fails for the middle-thirds Cantor set:
neither `(1,2)` nor `(-2,-1)` is a gap of `C - C` (R2), the complement of `C - C` is not
`(-2,-1) ∪ (1,2)` (R1), `(1,2)` is not a complementary component of `C - C` inside `[-2,2]`
(R3), and `(1,2)` does not lie in the hull `[inf (C-C), sup (C-C)]` (R4). -/
theorem double_gap_law_false :
    ¬ IsGap (cantorSet - cantorSet) (Ioo 1 2) ∧
    ¬ IsGap (cantorSet - cantorSet) (Ioo (-2) (-1)) ∧
    (cantorSet - cantorSet : Set ℝ)ᶜ ≠ Ioo (-2) (-1) ∪ Ioo 1 2 ∧
    (∀ x, connectedComponentIn (Icc (-2 : ℝ) 2 \ (cantorSet - cantorSet)) x ≠ Ioo 1 2) ∧
    ¬ Ioo (1 : ℝ) 2 ⊆ Icc (sInf (cantorSet - cantorSet)) (sSup (cantorSet - cantorSet)) :=
  ⟨fun ⟨⟨x, _, hx⟩, _⟩ => Ioo_one_two_not_component x hx,
   fun ⟨⟨x, _, hx⟩, _⟩ => Ioo_neg_two_neg_one_not_component x hx,
   compl_ne_double_gap, Ioo_one_two_not_component_in_Icc, Ioo_one_two_not_subset_hull⟩

end C8330
