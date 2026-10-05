import Mathlib

/-!
# Conjecture 00000007993 (obstacle problem): the singular set can be `(n-1)`-dimensional

The conjecture claims, for solutions of the classical obstacle problem `Δu = χ_{u>0}`, `u ≥ 0`,
that the regular part of the free boundary `FB = ∂{u>0}` is dense in `FB` and that the singular
part has Hausdorff dimension `≤ n - 3` for `n ≥ 3`. Regular and singular points follow
Figalli–Ros-Oton–Serra (arXiv:1912.00714, §3): `x₀` is regular if
`r⁻² u(x₀ + r x) → ½ (max{0, e·x})²` for a unit `e`, singular if `r⁻² u(x₀ + r x) → p` with
`p` a convex 2-homogeneous polynomial with `Δp ≡ 1`. The witness `u₀(x) = x₁²/2` in the unit
ball `B₁ ⊆ ℝⁿ` solves the problem, its free boundary is `B₁ ∩ {x₁ = 0}`, every free-boundary
point is singular and none is regular, so `dim_H Sing = n - 1 > n - 3` and `Reg = ∅`.
`Δ` is Mathlib's Laplacian `∑ᵢ D²u(x)[eᵢ, eᵢ]`; `dimH` is Mathlib's Hausdorff dimension.
-/

open InnerProductSpace MeasureTheory Filter Topology Set Metric Module
open scoped ENNReal ContDiff Laplacian

noncomputable section

namespace C7993

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- `u` solves the classical obstacle problem `Δu = χ_{u>0}`, `u ≥ 0` in `Ω`. We require more
than the standard `C^{1,1}` setting: `u` is `C^∞`, `Δu = 1` at every point of `{u > 0} ∩ Ω`, and
`Δu = χ_{u>0}` holds Lebesgue-a.e. in `Ω` (the sense in which the equation is meant for
`C^{1,1}` solutions). A stronger definition only weakens the refuted universal claims. -/
def IsObstacleSolution (Ω : Set (E n)) (u : E n → ℝ) : Prop :=
  ContDiff ℝ ∞ u ∧ (∀ x ∈ Ω, 0 ≤ u x) ∧ (∀ x ∈ Ω, 0 < u x → Δ u x = 1) ∧
    ∀ᵐ x ∂(volume : Measure (E n)), x ∈ Ω → Δ u x = Set.indicator {y | 0 < u y} 1 x

/-- The free boundary `FB(u) = Ω ∩ ∂{u > 0}`. -/
def freeBoundary (Ω : Set (E n)) (u : E n → ℝ) : Set (E n) := Ω ∩ frontier {x | 0 < u x}

/-- Quadratic rescaling `u_{x₀,r}(x) = r⁻² u(x₀ + r x)`. -/
def rescale (u : E n → ℝ) (x₀ : E n) (r : ℝ) (x : E n) : ℝ := u (x₀ + r • x) / r ^ 2

/-- Half-space solution `½ (max{0, e·x})²`. -/
def halfSpaceSol (e : E n) (x : E n) : ℝ := (max 0 (inner ℝ e x)) ^ 2 / 2

/-- Regular point: `lim_{r→0⁺} r⁻² u(x₀ + r x) = ½ (max{0, e·x})²` for some unit `e`
(pointwise limit, the weakest topology). -/
def IsRegularPt (Ω : Set (E n)) (u : E n → ℝ) (x₀ : E n) : Prop :=
  x₀ ∈ freeBoundary Ω u ∧ ∃ e : E n, ‖e‖ = 1 ∧
    ∀ x, Tendsto (fun r => rescale u x₀ r x) (𝓝[>] 0) (𝓝 (halfSpaceSol e x))

/-- The class `𝒫` of convex 2-homogeneous polynomials `p` with `Δp ≡ 1`. -/
def polyClass : Set (E n → ℝ) :=
  {p | (∃ Q : E n →L[ℝ] E n →L[ℝ] ℝ, ∀ x, p x = Q x x) ∧ ConvexOn ℝ univ p ∧ ∀ x, Δ p x = 1}

/-- Singular point: the limit `r⁻² u(x₀ + r ·) → p` exists (locally uniformly) and `p ∈ 𝒫`. -/
def IsSingularPt (Ω : Set (E n)) (u : E n → ℝ) (x₀ : E n) : Prop :=
  x₀ ∈ freeBoundary Ω u ∧
    ∃ p ∈ (polyClass : Set (E n → ℝ)), TendstoLocallyUniformly (rescale u x₀) p (𝓝[>] 0)

/-- The regular part `Reg(u)` of the free boundary. -/
def regularSet (Ω : Set (E n)) (u : E n → ℝ) : Set (E n) := {x | IsRegularPt Ω u x}

/-- The singular part `Sing(u)` of the free boundary. -/
def singularSet (Ω : Set (E n)) (u : E n → ℝ) : Set (E n) := {x | IsSingularPt Ω u x}

variable [NeZero n]

/-- The first coordinate `x ↦ x₁` (index `0`). -/
def L : E n →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin n)

/-- The witness `u₀(x) = x₁²/2`. -/
def u₀ (x : E n) : ℝ := (x 0) ^ 2 / 2

def e₀ : E n := EuclideanSpace.single 0 1

lemma L_apply (x : E n) : L x = x 0 := rfl

lemma L_e₀ : L (e₀ : E n) = 1 := by simp [L_apply, e₀]

lemma u₀_eq : (u₀ : E n → ℝ) = fun x => (1 / 2 : ℝ) * (L x * L x) := by
  funext x; simp only [u₀, L_apply]; ring

/-- The constant Hessian bilinear form `B v w = v₁ w₁`. -/
def B : E n →L[ℝ] E n →L[ℝ] ℝ := (L : E n →L[ℝ] ℝ).smulRight (L : E n →L[ℝ] ℝ)

lemma B_apply (v w : E n) : B v w = L v * L w := by simp [B]

lemma hasFDerivAt_u₀ (x : E n) : HasFDerivAt (u₀ : E n → ℝ) (B x) x := by
  rw [u₀_eq]
  have h := (((L : E n →L[ℝ] ℝ).hasFDerivAt (x := x)).mul
    ((L : E n →L[ℝ] ℝ).hasFDerivAt (x := x))).const_mul (1 / 2 : ℝ)
  have hB : (1 / 2 : ℝ) • (L x • (L : E n →L[ℝ] ℝ) + L x • L) = B x := by
    ext v; simp [B_apply]; ring
  rwa [hB] at h

lemma fderiv_u₀ : fderiv ℝ (u₀ : E n → ℝ) = (B : E n → E n →L[ℝ] ℝ) := by
  funext x; exact (hasFDerivAt_u₀ x).fderiv

lemma iteratedFDeriv_u₀ (x : E n) (m : Fin 2 → E n) :
    iteratedFDeriv ℝ 2 (u₀ : E n → ℝ) x m = L (m 0) * L (m 1) := by
  rw [iteratedFDeriv_two_apply, fderiv_u₀, ContinuousLinearMap.fderiv, B_apply]

lemma laplacian_u₀ (x : E n) : Δ (u₀ : E n → ℝ) x = 1 := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [iteratedFDeriv_u₀]
  simp [L_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]

lemma contDiff_u₀ : ContDiff ℝ ∞ (u₀ : E n → ℝ) := by
  rw [u₀_eq]
  exact contDiff_const.mul ((L : E n →L[ℝ] ℝ).contDiff.mul (L : E n →L[ℝ] ℝ).contDiff)

lemma u₀_nonneg (x : E n) : 0 ≤ u₀ x := by unfold u₀; positivity

lemma u₀_pos_iff (x : E n) : 0 < u₀ x ↔ L x ≠ 0 := by
  rw [L_apply]; unfold u₀
  constructor
  · intro h h0; rw [h0] at h; norm_num at h
  · intro h; have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; linarith

/-- The hyperplane `{x₁ = 0}`. -/
def plane : Submodule ℝ (E n) := LinearMap.ker (L : E n →L[ℝ] ℝ).toLinearMap

lemma mem_plane (x : E n) : x ∈ (plane : Submodule ℝ (E n)) ↔ L x = 0 := by
  simp [plane]

lemma plane_ne_top : (plane : Submodule ℝ (E n)) ≠ ⊤ := by
  intro h
  have : (e₀ : E n) ∈ (plane : Submodule ℝ (E n)) := h ▸ Submodule.mem_top
  rw [mem_plane, L_e₀] at this; exact one_ne_zero this

lemma volume_plane : volume ((plane : Submodule ℝ (E n)) : Set (E n)) = 0 :=
  Measure.addHaar_submodule _ _ plane_ne_top

lemma posSet_eq : {x : E n | 0 < u₀ x} = ((plane : Submodule ℝ (E n)) : Set (E n))ᶜ := by
  ext x; simp [u₀_pos_iff, mem_plane]

lemma interior_plane : interior ((plane : Submodule ℝ (E n)) : Set (E n)) = ∅ := by
  by_contra h
  exact plane_ne_top (Submodule.eq_top_of_nonempty_interior' _ (nonempty_iff_ne_empty.mpr h))

lemma frontier_posSet : frontier {x : E n | 0 < u₀ x} = ((plane : Submodule ℝ (E n)) : Set (E n)) := by
  rw [posSet_eq, frontier_compl, IsClosed.frontier_eq, interior_plane, sdiff_empty]
  exact (L : E n →L[ℝ] ℝ).isClosed_ker

lemma isObstacleSolution_u₀ (Ω : Set (E n)) : IsObstacleSolution Ω (u₀ : E n → ℝ) := by
  refine ⟨contDiff_u₀, fun x _ => u₀_nonneg x, fun x _ _ => laplacian_u₀ x, ?_⟩
  have h0 : ∀ᵐ x ∂(volume : Measure (E n)), x ∉ ((plane : Submodule ℝ (E n)) : Set (E n)) :=
    measure_eq_zero_iff_ae_notMem.mp volume_plane
  filter_upwards [h0] with x hx _
  have : x ∈ {y : E n | 0 < u₀ y} := by rw [posSet_eq]; exact hx
  rw [Set.indicator_of_mem this, laplacian_u₀]; rfl

lemma freeBoundary_u₀ (Ω : Set (E n)) :
    freeBoundary Ω (u₀ : E n → ℝ) = Ω ∩ ((plane : Submodule ℝ (E n)) : Set (E n)) := by
  rw [freeBoundary, frontier_posSet]

lemma rescale_u₀ {x₀ : E n} (hx₀ : L x₀ = 0) {r : ℝ} (hr : r ≠ 0) :
    rescale (u₀ : E n → ℝ) x₀ r = u₀ := by
  funext x
  simp only [rescale, u₀, ← L_apply, map_add, map_smul, hx₀, smul_eq_mul, zero_add]
  field_simp

lemma u₀_mem_polyClass : (u₀ : E n → ℝ) ∈ (polyClass : Set (E n → ℝ)) := by
  refine ⟨⟨(1 / 2 : ℝ) • B, fun x => ?_⟩, ?_, laplacian_u₀⟩
  · simp [B_apply, u₀_eq]
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [u₀, ← L_apply, map_add, map_smul, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [sq_nonneg (L x - L y), mul_nonneg ha hb]

lemma not_regular_u₀ (Ω : Set (E n)) (x₀ : E n) : ¬ IsRegularPt Ω (u₀ : E n → ℝ) x₀ := by
  rintro ⟨hfb, e, he, hlim⟩
  rw [freeBoundary_u₀] at hfb
  have hx₀ : L x₀ = 0 := (mem_plane x₀).mp hfb.2
  have key : ∀ x, u₀ x = halfSpaceSol e x := by
    intro x
    have h1 : Tendsto (fun r => rescale (u₀ : E n → ℝ) x₀ r x) (𝓝[>] 0) (𝓝 (u₀ x)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [rescale_u₀ hx₀ (ne_of_gt hr)]
    exact tendsto_nhds_unique h1 (hlim x)
  have h2 := key (-e)
  simp only [halfSpaceSol, inner_neg_right, real_inner_self_eq_norm_sq, he] at h2
  norm_num at h2
  have h3 := key e₀
  have hi : inner ℝ e (e₀ : E n) = L e := by
    simp [e₀, EuclideanSpace.inner_single_right, L_apply]
  simp only [halfSpaceSol, hi] at h3
  simp only [u₀, ← L_apply, map_neg, L_e₀] at h2 h3
  have hLe : L e = 0 := by nlinarith [sq_nonneg (L e)]
  rw [hLe] at h3; norm_num at h3

lemma singular_u₀ (Ω : Set (E n)) {x₀ : E n} (hx : x₀ ∈ freeBoundary Ω (u₀ : E n → ℝ)) :
    IsSingularPt Ω (u₀ : E n → ℝ) x₀ := by
  refine ⟨hx, u₀, u₀_mem_polyClass, ?_⟩
  rw [freeBoundary_u₀] at hx
  have hx₀ : L x₀ = 0 := (mem_plane x₀).mp hx.2
  intro U hU x
  refine ⟨univ, univ_mem, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr y _
  rw [rescale_u₀ hx₀ (ne_of_gt hr)]
  exact refl_mem_uniformity hU

lemma regularSet_u₀ (Ω : Set (E n)) : regularSet Ω (u₀ : E n → ℝ) = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun x hx => not_regular_u₀ Ω x hx

lemma singularSet_u₀ (Ω : Set (E n)) :
    singularSet Ω (u₀ : E n → ℝ) = Ω ∩ ((plane : Submodule ℝ (E n)) : Set (E n)) := by
  rw [← freeBoundary_u₀]
  ext x
  exact ⟨fun h => h.1, fun h => singular_u₀ Ω h⟩

lemma contactSet_u₀ : {x : E n | u₀ x = 0} = ((plane : Submodule ℝ (E n)) : Set (E n)) := by
  ext x
  have h1 := u₀_pos_iff x
  have h2 := u₀_nonneg x
  simp only [mem_ofPred_eq, SetLike.mem_coe, mem_plane]
  constructor
  · intro h; by_contra h'; have := h1.mpr h'; linarith
  · intro h; by_contra h'; exact (h1.mp (lt_of_le_of_ne h2 (Ne.symm h'))) h

/-- The contact set `{u₀ = 0}` has Lebesgue density `0` in every ball. -/
lemma contact_density_zero (x₀ : E n) (r : ℝ) :
    volume ({x : E n | u₀ x = 0} ∩ ball x₀ r) / volume (ball x₀ r) = 0 := by
  have h0 : volume {x : E n | u₀ x = 0} = 0 := by rw [contactSet_u₀]; exact volume_plane
  rw [measure_mono_null inter_subset_left h0, ENNReal.zero_div]

lemma finrank_plane : finrank ℝ (plane : Submodule ℝ (E n)) = n - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (L : E n →L[ℝ] ℝ).toLinearMap
  have hr : LinearMap.range (L : E n →L[ℝ] ℝ).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr fun c => ⟨c • e₀, by simp [L_e₀]⟩
  rw [hr, finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at h
  change finrank ℝ (LinearMap.ker (L : E n →L[ℝ] ℝ).toLinearMap) = n - 1
  omega

lemma dimH_inter_plane {Ω : Set (E n)} (hΩ : IsOpen Ω)
    (hne : (Ω ∩ ((plane : Submodule ℝ (E n)) : Set (E n))).Nonempty) :
    dimH (Ω ∩ ((plane : Submodule ℝ (E n)) : Set (E n))) = ((n - 1 : ℕ) : ℝ≥0∞) := by
  set K := (plane : Submodule ℝ (E n))
  have himg : Ω ∩ (K : Set (E n)) = ((↑) : K → E n) '' ((↑) ⁻¹' Ω) := by
    rw [Set.image_preimage_eq_inter_range]; simp
  rw [himg, isometry_subtype_coe.dimH_image, Real.dimH_of_nonempty_interior, finrank_plane]
  rw [(hΩ.preimage continuous_subtype_val).interior_eq]
  obtain ⟨x, hxΩ, hxK⟩ := hne
  exact ⟨⟨x, hxK⟩, hxΩ⟩

lemma zero_mem_fb : (0 : E n) ∈ freeBoundary (ball 0 1) (u₀ : E n → ℝ) := by
  rw [freeBoundary_u₀]; exact ⟨mem_ball_self one_pos, zero_mem _⟩

/-- For every `n ≥ 1`, `u₀ = x₁²/2` in `B₁ ⊆ ℝⁿ`: a solution whose free boundary is the
hyperplane piece `B₁ ∩ {x₁ = 0}`, all of it singular, no regular point, contact set of
Lebesgue density `0`, and `dim_H Sing = n - 1`. -/
theorem witness :
    IsObstacleSolution (ball 0 1) (u₀ : E n → ℝ) ∧
    freeBoundary (ball 0 1) (u₀ : E n → ℝ) = {x | x ∈ ball 0 1 ∧ x 0 = 0} ∧
    regularSet (ball 0 1) (u₀ : E n → ℝ) = ∅ ∧
    singularSet (ball 0 1) (u₀ : E n → ℝ) = freeBoundary (ball 0 1) u₀ ∧
    singularSet (ball 0 1) (u₀ : E n → ℝ) =
      freeBoundary (ball 0 1) u₀ \ regularSet (ball 0 1) u₀ ∧
    (∀ x₀ r, volume ({x : E n | u₀ x = 0} ∩ ball x₀ r) / volume (ball x₀ r) = 0) ∧
    dimH (singularSet (ball 0 1) (u₀ : E n → ℝ)) = ((n - 1 : ℕ) : ℝ≥0∞) := by
  have hfb : freeBoundary (ball 0 1) (u₀ : E n → ℝ) = {x | x ∈ ball 0 1 ∧ x 0 = 0} := by
    rw [freeBoundary_u₀]; ext x; simp [mem_plane, L_apply]
  have hs : singularSet (ball 0 1) (u₀ : E n → ℝ) = freeBoundary (ball 0 1) u₀ := by
    rw [singularSet_u₀, freeBoundary_u₀]
  refine ⟨isObstacleSolution_u₀ _, hfb, regularSet_u₀ _, hs, ?_, contact_density_zero, ?_⟩
  · rw [hs, regularSet_u₀, sdiff_empty]
  · rw [singularSet_u₀, dimH_inter_plane isOpen_ball]
    rw [← freeBoundary_u₀]; exact ⟨0, zero_mem_fb⟩

/-- Clause of the conjecture: for `n ≥ 3`, every solution of the obstacle problem in an open
`Ω ⊆ ℝⁿ` has singular set of Hausdorff dimension at most `n - 3`. -/
def SingDimBound : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ Ω : Set (E n), IsOpen Ω → ∀ u : E n → ℝ, IsObstacleSolution Ω u →
    dimH (singularSet Ω u) ≤ ((n - 3 : ℕ) : ℝ≥0∞)

/-- Clause of the conjecture: the regular part is dense in the free boundary
(`FB ⊆ closure Reg`), for every dimension `n ≥ 2`. -/
def RegDenseInFB : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ Ω : Set (E n), IsOpen Ω → ∀ u : E n → ℝ, IsObstacleSolution Ω u →
    freeBoundary Ω u ⊆ closure (regularSet Ω u)

/-- Infinite family: for every `n ≥ 3` there is a solution in `B₁ ⊆ ℝⁿ`, namely
`u(x) = x₁²/2`, whose singular set has Hausdorff dimension `n - 1 > n - 3`. -/
theorem family (n : ℕ) (hn : 3 ≤ n) :
    ∃ u : E n → ℝ, (∀ x, u x = (x ⟨0, by omega⟩) ^ 2 / 2) ∧
      IsObstacleSolution (ball 0 1) u ∧ regularSet (ball 0 1) u = ∅ ∧
      dimH (singularSet (ball 0 1) u) = ((n - 1 : ℕ) : ℝ≥0∞) ∧
      ((n - 3 : ℕ) : ℝ≥0∞) < dimH (singularSet (ball 0 1) u) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨h1, -, h3, -, -, -, h7⟩ := witness (n := n)
  refine ⟨u₀, fun x => rfl, h1, h3, h7, ?_⟩
  rw [h7]; exact_mod_cast (by omega : n - 3 < n - 1)

/-- Main theorem: the dimension clause `dim_H Sing ≤ n - 3` is false. -/
theorem not_singDimBound : ¬ SingDimBound := by
  intro h
  obtain ⟨u, -, hu, -, -, hlt⟩ := family 3 le_rfl
  exact absurd (h 3 le_rfl _ isOpen_ball u hu) (not_le.mpr hlt)

/-- Main theorem: the clause "the regular part is dense in FB" is false. -/
theorem not_regDenseInFB : ¬ RegDenseInFB := by
  intro h
  have := h 3 (by norm_num) _ isOpen_ball u₀ (isObstacleSolution_u₀ _) zero_mem_fb
  rw [regularSet_u₀, closure_empty] at this
  exact this

theorem not_conjecture : ¬ (SingDimBound ∧ RegDenseInFB) := fun h => not_singDimBound h.1

end C7993
