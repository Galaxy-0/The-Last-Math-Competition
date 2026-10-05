import Geometry240
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set MeasureTheory
namespace Mahler240
noncomputable section

abbrev E := ℝ × (Fin 3 → ℝ)
abbrev Four := Option (Fin 3)

def coords : (Four → ℝ) ≃ₗ[ℝ] E := LinearEquiv.piOptionEquivProd ℝ

def K : Set E := Set.Icc (-1) 1 ×ˢ cross (Fin 3)
def P : Set E := {x | ∀ i : Fin 3, |x.1| + |x.2 i| ≤ 1}
def Cube : Set E := coords '' cube Four
def Cross : Set E := coords '' cross Four

noncomputable def dot (x y : E) : ℝ := x.1 * y.1 + ∑ i, x.2 i * y.2 i

def polar (S : Set E) : Set E := {y | ∀ x ∈ S, dot x y ≤ 1}

def SymmetricConvexBody (S : Set E) : Prop :=
  IsCompact S ∧ Convex ℝ S ∧ (interior S).Nonempty ∧ ∀ x ∈ S, -x ∈ S

lemma ambient_dimension : Module.finrank ℝ E = 4 := by
  simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]

lemma signVal_mul (r : ℝ) : signVal (decide (0 ≤ r)) * r = |r| := by
  by_cases h : 0 ≤ r
  · simp [signVal, h, abs_of_nonneg h]
  · simp [signVal, h, abs_of_neg (lt_of_not_ge h)]

lemma polar_K : polar K = P := by
  ext y
  constructor
  · intro hy i
    let x : E := (signVal (decide (0 ≤ y.1)), axis (decide (0 ≤ y.2 i), i))
    have hx : x ∈ K := by
      refine ⟨?_, axis_mem_cross _⟩
      exact abs_le.mp (le_of_eq (signVal_abs _))
    have hh := hy x hx
    simpa [dot, x, axis, Pi.single_apply, signVal_mul] using hh
  · intro hy x hx
    have hyt : |y.1| ≤ 1 := le_trans (le_add_of_nonneg_right (abs_nonneg (y.2 0))) (hy 0)
    have hyr : 0 ≤ 1 - |y.1| := sub_nonneg.mpr hyt
    have hxt : |x.1| ≤ 1 := abs_le.mpr hx.1
    have hxs : ∑ i, |x.2 i| ≤ 1 := hx.2
    calc
      dot x y ≤ |x.1| * |y.1| + ∑ i, |x.2 i| * |y.2 i| := by
        apply add_le_add
        · simpa only [abs_mul] using le_abs_self (x.1 * y.1)
        · apply Finset.sum_le_sum
          intro i _
          simpa only [abs_mul] using le_abs_self (x.2 i * y.2 i)
      _ ≤ 1 * |y.1| + ∑ i, |x.2 i| * (1 - |y.1|) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hxt (abs_nonneg _)
        · apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (by linarith [hy i]) (abs_nonneg _)
      _ = |y.1| + (∑ i, |x.2 i|) * (1 - |y.1|) := by
        rw [one_mul, Finset.sum_mul]
      _ ≤ |y.1| + 1 * (1 - |y.1|) := add_le_add_left (mul_le_mul_of_nonneg_right hxs hyr) _
      _ = 1 := by ring

lemma continuous_l1 {ι : Type*} [Fintype ι] : Continuous (fun x : ι → ℝ => ∑ i, |x i|) := by
  fun_prop

lemma compact_cross {ι : Type*} [Fintype ι] [DecidableEq ι] : IsCompact (cross ι) := by
  apply (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := (-1 : ℝ)) (b := 1))).of_isClosed_subset
  · exact isClosed_le continuous_l1 continuous_const
  · intro x hx i _
    exact abs_le.mp (abs_coord_le hx i)

lemma K_body : SymmetricConvexBody K := by
  refine ⟨isCompact_Icc.prod compact_cross, (convex_Icc (-1 : ℝ) 1).prod convex_cross, ?_, ?_⟩
  · let O : Set E := {x | |x.1| < 1 ∧ ∑ i, |x.2 i| < 1}
    have ho : IsOpen O := (isOpen_lt (continuous_fst.abs) continuous_const).inter
      (isOpen_lt (continuous_l1.comp continuous_snd) continuous_const)
    have hz : (0 : E) ∈ O := by simp [O]
    have hs : O ⊆ K := by
      intro x hx
      exact ⟨abs_le.mp (le_of_lt hx.1), le_of_lt hx.2⟩
    exact ⟨0, interior_mono hs (by simpa only [ho.interior_eq] using hz)⟩
  · intro x hx
    constructor
    · change -x.1 ∈ Set.Icc (-1 : ℝ) 1
      constructor <;> linarith [hx.1.1, hx.1.2]
    · simpa [cross] using hx.2

lemma ncard_product {α β : Type*} (s : Set α) (t : Set β) :
    (s ×ˢ t).ncard = s.ncard * t.ncard := by
  simp only [Set.ncard, Set.encard, ENat.card_congr (Equiv.Set.prod s t),
    ENat.card_prod, ENat.toNat_mul]

lemma ncard_extreme_K : (K.extremePoints ℝ).ncard = 12 := by
  rw [K, extremePoints_prod, ncard_product, extreme_interval, ncard_extreme_cross]
  norm_num

lemma ncard_extreme_Cube : (Cube.extremePoints ℝ).ncard = 16 := by
  rw [Cube, ← image_extremePoints coords, Set.ncard_image_of_injective _ coords.injective,
    ncard_extreme_cube]
  norm_num [Four]

lemma ncard_extreme_Cross : (Cross.extremePoints ℝ).ncard = 8 := by
  rw [Cross, ← image_extremePoints coords, Set.ncard_image_of_injective _ coords.injective,
    ncard_extreme_cross]
  norm_num [Four]

lemma bijective_of_image_K {S : Set E} (f : E →ₗ[ℝ] E) (hf : f '' S = K) :
    Function.Bijective f := by
  have hs : K ⊆ (LinearMap.range f : Set E) := by
    rw [← hf]
    rintro y ⟨x, _, rfl⟩
    exact ⟨x,rfl⟩
  have ht : LinearMap.range f = ⊤ :=
    (LinearMap.range f).eq_top_of_nonempty_interior' (K_body.2.2.1.mono (interior_mono hs))
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp ht
  exact ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩

lemma not_linear_image_Cube : ¬ ∃ f : E →ₗ[ℝ] E, f '' Cube = K := by
  rintro ⟨f,hf⟩
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective f (bijective_of_image_K f hf)
  have hn := congrArg Set.ncard (image_extremePoints e Cube)
  rw [Set.ncard_image_of_injective _ e.injective, ncard_extreme_Cube] at hn
  change 16 = ((f '' Cube).extremePoints ℝ).ncard at hn
  rw [hf, ncard_extreme_K] at hn
  norm_num at hn

lemma not_linear_image_Cross : ¬ ∃ f : E →ₗ[ℝ] E, f '' Cross = K := by
  rintro ⟨f,hf⟩
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective f (bijective_of_image_K f hf)
  have hn := congrArg Set.ncard (image_extremePoints e Cross)
  rw [Set.ncard_image_of_injective _ e.injective, ncard_extreme_Cross] at hn
  change 8 = ((f '' Cross).extremePoints ℝ).ncard at hn
  rw [hf, ncard_extreme_K] at hn
  norm_num at hn

lemma coords_apply (x : Four → ℝ) :
    coords x = (x none, fun i => x (some i)) := rfl

lemma dot_coords (x y : Four → ℝ) :
    dot (coords x) (coords y) = ∑ i, x i * y i := by
  simp [coords_apply, dot, Fintype.sum_option, add_comm]

lemma mem_Cube (x : E) :
    x ∈ Cube ↔ |x.1| ≤ 1 ∧ ∀ i, |x.2 i| ≤ 1 := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    constructor
    · exact abs_le.mpr (hv none (Set.mem_univ none))
    · intro i
      exact abs_le.mpr (hv (some i) (Set.mem_univ _))
  · intro hx
    refine ⟨coords.symm x, ?_, coords.apply_symm_apply x⟩
    intro i _
    cases i with
    | none => exact abs_le.mp hx.1
    | some i => exact abs_le.mp (hx.2 i)

lemma mem_Cross (x : E) :
    x ∈ Cross ↔ |x.1| + ∑ i, |x.2 i| ≤ 1 := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    simpa [cross, coords_apply, Fintype.sum_option] using hv
  · intro hx
    refine ⟨coords.symm x, ?_, coords.apply_symm_apply x⟩
    simpa [cross, Fintype.sum_option, coords, LinearEquiv.piOptionEquivProd] using hx

end
end Mahler240
