import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

open Set Finset
namespace Mahler240

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cross (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {x | ∑ i, |x i| ≤ 1}
def cube (ι : Type*) : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Icc (-1) 1

def signVal (b : Bool) : ℝ := if b then 1 else -1

noncomputable def axis (p : Bool × ι) : ι → ℝ := Pi.single p.2 (signVal p.1)

lemma signVal_abs (b : Bool) : |signVal b| = 1 := by cases b <;> norm_num [signVal]
lemma signVal_ne_zero (b : Bool) : signVal b ≠ 0 := by cases b <;> norm_num [signVal]
lemma signVal_injective : Function.Injective signVal := by
  intro a b h
  cases a <;> cases b <;> norm_num [signVal] at *

lemma axis_mem_cross (p : Bool × ι) : axis p ∈ cross ι := by
  simp [axis, cross, Pi.single_apply, apply_ite, signVal_abs]

omit [DecidableEq ι] in
lemma abs_coord_le {x : ι → ℝ} (hx : x ∈ cross ι) (i : ι) : |x i| ≤ 1 :=
  le_trans (Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)) hx

omit [DecidableEq ι] in
lemma convex_cross : Convex ℝ (cross ι) := by
  intro x hx y hy a b ha hb hab
  change ∑ i, |a * x i + b * y i| ≤ 1
  calc
    _ ≤ ∑ i, (a * |x i| + b * |y i|) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a * (∑ i, |x i|) + b * (∑ i, |y i|) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by linarith

omit [Fintype ι] in
lemma zero_mem_hull_axes [Nonempty ι] : (0 : ι → ℝ) ∈ convexHull ℝ (Set.range (axis (ι := ι))) := by
  let i : ι := Classical.arbitrary ι
  have h := (convex_convexHull ℝ (Set.range (axis (ι := ι))))
    (subset_convexHull ℝ _ (Set.mem_range_self (true, i)))
    (subset_convexHull ℝ _ (Set.mem_range_self (false, i)))
    (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ext j
  by_cases hij : j = i <;> simp [axis, Pi.single_apply, signVal, hij]

lemma cross_eq_hull_axes [Nonempty ι] : cross ι = convexHull ℝ (Set.range (axis (ι := ι))) := by
  apply Set.Subset.antisymm
  · intro x hx
    let w : Option ι → ℝ := fun o => match o with
      | none => 1 - ∑ i, |x i|
      | some i => |x i|
    let z : Option ι → (ι → ℝ) := fun o => match o with
      | none => 0
      | some i => axis (decide (0 ≤ x i), i)
    have hw : ∀ i ∈ (Finset.univ : Finset (Option ι)), 0 ≤ w i := by
      intro i _
      cases i with
      | none => exact sub_nonneg.mpr hx
      | some i => exact abs_nonneg _
    have hsum : ∑ i, w i = 1 := by simp [w, Fintype.sum_option]
    have hz : ∀ i ∈ (Finset.univ : Finset (Option ι)), z i ∈ convexHull ℝ (Set.range (axis (ι := ι))) := by
      intro i _
      cases i with
      | none => exact zero_mem_hull_axes
      | some i => exact subset_convexHull ℝ _ (Set.mem_range_self _)
    have h := (convex_convexHull ℝ _).sum_mem hw hsum hz
    have heq : (∑ i, w i • z i) = x := by
      ext j
      simp only [Fintype.sum_option, w, z, smul_zero, zero_add, Finset.sum_apply,
        Pi.smul_apply, Pi.zero_apply, mul_zero, smul_eq_mul, axis, Pi.single_apply]
      rw [Finset.sum_eq_single j]
      · by_cases h : 0 ≤ x j <;> simp [h, signVal, abs_of_nonneg, abs_of_neg (lt_of_not_ge h)]
      · intro b _ hbj
        simp [hbj, Ne.symm hbj]
      · simp
    rwa [heq] at h
  · exact convexHull_min (Set.range_subset_iff.mpr axis_mem_cross) convex_cross

lemma coord_one_unique {x : ι → ℝ} (hx : x ∈ cross ι) (i : ι) (hi : x i = 1) :
    x = Pi.single i 1 := by
  ext j
  by_cases hji : j = i
  · subst j; simpa
  · have hh := Finset.sum_le_sum_of_subset_of_nonneg (s := {i,j}) (t := Finset.univ)
      (f := fun k => |x k|) (by simp) (by intros; positivity)
    have hij : i ≠ j := Ne.symm hji
    simp only [Finset.sum_pair hij, hi, abs_one] at hh
    change ∑ k, |x k| ≤ 1 at hx
    have hj0 : x j = 0 := abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg _))
    simp [Pi.single_apply, hji, hj0]

lemma axis_extreme (p : Bool × ι) : axis p ∈ (cross ι).extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨axis_mem_cross p, ?_⟩
  intro x hx y hy hxy
  rcases hxy with ⟨a,b,ha,hb,hab,heq⟩
  have hi := congrFun heq p.2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, axis, Pi.single_eq_same] at hi
  have hxi := abs_coord_le hx p.2
  have hyi := abs_coord_le hy p.2
  rcases p with ⟨s,i⟩
  cases s
  · have hxi1 : x i = -1 := by simp [signVal] at hi; rw [abs_le] at hxi hyi; nlinarith
    have hxneg : (-x) ∈ cross ι := by simpa [cross] using hx
    have hh := coord_one_unique hxneg i (by simp [hxi1])
    ext j
    have hj := congrFun hh j
    by_cases hji : j = i <;> simp [axis, signVal, Pi.single_apply, hji] at hj ⊢ <;> linarith
  · have hxi1 : x i = 1 := by simp [signVal] at hi; rw [abs_le] at hxi hyi; nlinarith
    simpa [axis, signVal] using coord_one_unique hx i hxi1

lemma extreme_cross [Nonempty ι] : (cross ι).extremePoints ℝ = Set.range (axis (ι := ι)) := by
  apply Set.Subset.antisymm
  · rw [cross_eq_hull_axes]
    exact extremePoints_convexHull_subset
  · exact Set.range_subset_iff.mpr axis_extreme

omit [Fintype ι] in
lemma axis_injective : Function.Injective (axis (ι := ι)) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ h
  have hij : i = j := by
    by_contra hij
    have hh := congrFun h i
    simp only [axis, Pi.single_apply, if_pos rfl, if_neg hij] at hh
    exact signVal_ne_zero a hh
  subst j
  have hh := congrFun h i
  simp only [axis, Pi.single_eq_same] at hh
  exact Prod.ext (signVal_injective hh) rfl

lemma ncard_extreme_cross [Nonempty ι] : ((cross ι).extremePoints ℝ).ncard = 2 * Fintype.card ι := by
  rw [extreme_cross, ← Set.image_univ, Set.ncard_image_of_injective _ axis_injective]
  simp [Set.ncard_univ, Nat.card_eq_fintype_card]

lemma extreme_interval : (Set.Icc (-1 : ℝ) 1).extremePoints ℝ = {-1,1} := by
  ext x
  constructor
  · intro hx
    by_cases hxneg : x = -1
    · simp [hxneg]
    by_cases hxpos : x = 1
    · simp [hxpos]
    have hm : x ∈ openSegment ℝ (-1) 1 := by
      rw [openSegment_eq_Ioo (by norm_num : (-1 : ℝ) < 1)]
      exact ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hxneg), lt_of_le_of_ne hx.1.2 hxpos⟩
    have hh := hx.2 (by norm_num : (-1 : ℝ) ∈ Set.Icc (-1) 1)
      (by norm_num : (1 : ℝ) ∈ Set.Icc (-1) 1) hm
    exact False.elim (hxneg hh.1.symm)
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    all_goals
      apply mem_extremePoints_iff_left.mpr
      refine ⟨by norm_num, ?_⟩
      intro x hx y hy hxy
      rcases hxy with ⟨a,b,ha,hb,hab,heq⟩
      simp only [smul_eq_mul] at heq
      nlinarith [hx.1, hx.2, hy.1, hy.2]

omit [Fintype ι] [DecidableEq ι] in
lemma extreme_cube : (cube ι).extremePoints ℝ =
    Set.range (fun b : ι → Bool => fun i => signVal (b i)) := by
  rw [cube, extremePoints_pi]
  simp_rw [extreme_interval]
  ext x
  constructor
  · intro hx
    refine ⟨fun i => decide (x i = 1), ?_⟩
    ext i
    have hi := hx i (Set.mem_univ i)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with hi | hi <;> norm_num [signVal, hi]
  · rintro ⟨b,rfl⟩ i _
    cases h : b i <;> simp [h, signVal]

lemma ncard_extreme_cube : ((cube ι).extremePoints ℝ).ncard = 2 ^ Fintype.card ι := by
  rw [extreme_cube, ← Set.image_univ, Set.ncard_image_of_injective]
  · simp [Set.ncard_univ, Nat.card_eq_fintype_card]
  · intro a b h
    exact funext fun i => signVal_injective (congrFun h i)

end
end Mahler240
