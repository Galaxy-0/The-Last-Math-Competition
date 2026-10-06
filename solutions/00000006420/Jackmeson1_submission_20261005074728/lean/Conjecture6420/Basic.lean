import Mathlib

/-!
# Conjecture 00000006420: same isoperimetric deficit, different Fraenkel asymmetry

Two unions of two disjoint closed unit disks in the Euclidean plane `ℝ²`:
* `Enear` : centres `(0,0)` and `(5/2,0)`,
* `Efar`  : centres `(0,0)` and `(10,0)`.

Both have area `2π` and the same perimeter (one-dimensional Hausdorff measure of the
topological boundary, which is two unit circles), hence the same isoperimetric deficit
(`√2 - 1`).  Their Fraenkel asymmetries differ: `α(Enear) < 1 ≤ α(Efar)`.
-/

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

namespace C6420

/-- The Euclidean plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Lebesgue measure (area) on the plane. -/
noncomputable abbrev vol : Measure Plane := volume

/-- Perimeter: the one-dimensional Hausdorff measure (length) of the topological boundary. -/
noncomputable def perimeter (E : Set Plane) : ℝ≥0∞ := μH[1] (frontier E)

/-- Area of `E` as a real number. -/
noncomputable def area (E : Set Plane) : ℝ := vol.real E

/-- Radius of the disk having the same area as `E`. -/
noncomputable def eqRadius (E : Set Plane) : ℝ := Real.sqrt (area E / Real.pi)

/-- Isoperimetric deficit `δ(E) = P(E) / P(B_E) - 1`, where `B_E` is a disk with `|B_E| = |E|`. -/
noncomputable def deficit (E : Set Plane) : ℝ :=
  (perimeter E).toReal / (perimeter (closedBall (0 : Plane) (eqRadius E))).toReal - 1

/-- Fraenkel asymmetry `α(E) = inf_x |E Δ (x + B_E)| / |E|`, `B_E` the disk with `|B_E| = |E|`. -/
noncomputable def asymmetry (E : Set Plane) : ℝ :=
  ⨅ x : Plane, vol.real (symmDiff E (closedBall x (eqRadius E))) / area E

/-- The point `(a, 0)`. -/
noncomputable def pt (a : ℝ) : Plane := EuclideanSpace.single 0 a

/-- The closed unit disk centred at `(a, 0)`. -/
noncomputable def D (a : ℝ) : Set Plane := closedBall (pt a) 1

/-- The two-disk union with centre distance `5/2`. -/
noncomputable def Enear : Set Plane := D 0 ∪ D (5 / 2)

/-- The two-disk union with centre distance `10`. -/
noncomputable def Efar : Set Plane := D 0 ∪ D 10

/-! ### Basic facts -/

lemma dist_pt (a b : ℝ) : dist (pt a) (pt b) = |a - b| := by
  simp [pt, Real.dist_eq]

lemma vol_ball (x : Plane) {r : ℝ} (hr : 0 ≤ r) : vol.real (closedBall x r) = r ^ 2 * Real.pi := by
  simp [Measure.real, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_pos.le]

lemma vol_ball_ne_top (x : Plane) (r : ℝ) : vol (closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne

lemma disj (a : ℝ) (ha : 2 < |a|) : Disjoint (D 0) (D a) := by
  apply closedBall_disjoint_closedBall
  rw [dist_pt, zero_sub, abs_neg]; linarith

lemma vol_two (a : ℝ) (ha : 2 < |a|) : vol.real (D 0 ∪ D a) = 2 * Real.pi := by
  rw [measureReal_union (disj a ha) measurableSet_closedBall (vol_ball_ne_top _ _)
    (vol_ball_ne_top _ _)]
  simp only [D, vol_ball _ zero_le_one]; ring

lemma two_lt_near : (2 : ℝ) < |5 / 2| := by norm_num [abs_of_pos]
lemma two_lt_far : (2 : ℝ) < |10| := by norm_num [abs_of_pos]

lemma area_near : area Enear = 2 * Real.pi := vol_two _ two_lt_near
lemma area_far : area Efar = 2 * Real.pi := vol_two _ two_lt_far

lemma eqRadius_of_area {E : Set Plane} (h : area E = 2 * Real.pi) : eqRadius E = Real.sqrt 2 := by
  rw [eqRadius, h, mul_div_assoc, div_self Real.pi_pos.ne', mul_one]

lemma eqRadius_near : eqRadius Enear = Real.sqrt 2 := eqRadius_of_area area_near
lemma eqRadius_far : eqRadius Efar = Real.sqrt 2 := eqRadius_of_area area_far

/-- The comparison disk `B_E` has exactly the area of `E`. -/
lemma vol_comparison (x : Plane) : vol.real (closedBall x (Real.sqrt 2)) = 2 * Real.pi := by
  rw [vol_ball x (Real.sqrt_nonneg 2), Real.sq_sqrt (by norm_num)]

/-! ### Perimeter -/

lemma frontier_union_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (h : Disjoint A B) :
    frontier (A ∪ B) = frontier A ∪ frontier B := by
  have key : ∀ {S T : Set X}, IsClosed S → IsClosed T → Disjoint S T →
      frontier S ⊆ frontier (S ∪ T) := by
    intro S T hS hT hST p hp
    have hpS : p ∈ S := hS.frontier_subset hp
    refine ⟨subset_closure (Or.inl hpS), fun hint => hp.2 ?_⟩
    have hU : IsOpen (interior (S ∪ T) ∩ Tᶜ) := isOpen_interior.inter hT.isOpen_compl
    have hpU : p ∈ interior (S ∪ T) ∩ Tᶜ := ⟨hint, fun hpT => hST.ne_of_mem hpS hpT rfl⟩
    have hsub : interior (S ∪ T) ∩ Tᶜ ⊆ S := fun q ⟨hq1, hq2⟩ =>
      (interior_subset hq1).resolve_right hq2
    exact interior_maximal hsub hU hpU
  apply Subset.antisymm
  · intro p hp
    rcases frontier_union_subset A B hp with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Or.inl h1
    · exact Or.inr h2
  · rintro p (hp | hp)
    · exact key hA hB h hp
    · rw [union_comm]; exact key hB hA h.symm hp

/-- Length of the unit circle (left abstract; only `0 < L < ∞` is used). -/
noncomputable def L : ℝ≥0∞ := μH[1] (sphere (0 : Plane) 1)

lemma hm_sphere (x : Plane) (r : ℝ) : μH[1] (sphere x r) = μH[1] (sphere (0 : Plane) r) := by
  calc μH[1] (sphere x r) = μH[1] (IsometryEquiv.addRight x '' sphere (0 : Plane) r) := by
        rw [IsometryEquiv.image_sphere]; simp
    _ = _ := IsometryEquiv.hausdorffMeasure_image _ _ _

lemma perimeter_two (a : ℝ) (ha : 2 < |a|) : perimeter (D 0 ∪ D a) = 2 * L := by
  show μH[1] (frontier (closedBall (pt 0) 1 ∪ closedBall (pt a) 1)) = 2 * L
  rw [frontier_union_of_closed isClosed_closedBall isClosed_closedBall (disj a ha),
    frontier_closedBall _ one_ne_zero, frontier_closedBall _ one_ne_zero,
    measure_union ((disj a ha).mono sphere_subset_closedBall sphere_subset_closedBall)
      isClosed_sphere.measurableSet,
    hm_sphere (pt 0), hm_sphere (pt a), L, two_mul]

/-- The isometry `ℂ ≃ ℝ²`. -/
noncomputable def cplx : ℂ ≃ᵢ Plane := Complex.orthonormalBasisOneI.repr.toIsometryEquiv

lemma L_eq_complex : L = μH[1] (sphere (0 : ℂ) 1) := by
  rw [L, ← IsometryEquiv.hausdorffMeasure_image cplx, IsometryEquiv.image_sphere]
  congr 2
  simp [cplx]

lemma lipschitz_exp : LipschitzWith 1 (fun θ : ℝ => Complex.exp (θ * Complex.I)) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  have h : Complex.exp (s * Complex.I) =
      Complex.exp (t * Complex.I) * Complex.exp (Complex.I * ((s - t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [dist_eq_norm, h, ← mul_sub_one, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    NNReal.coe_one, one_mul, Real.dist_eq]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

lemma L_lt_top : L < ⊤ := by
  rw [L_eq_complex]
  have hsub : sphere (0 : ℂ) 1 ⊆
      (fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Icc (-Real.pi) Real.pi := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using hz
    refine ⟨Complex.arg z, ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_⟩
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz1] at this; simpa using this
  calc μH[1] (sphere (0 : ℂ) 1)
      ≤ μH[1] ((fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Icc (-Real.pi) Real.pi) :=
        measure_mono hsub
    _ ≤ (1 : NNReal) ^ (1 : ℝ) * μH[1] (Icc (-Real.pi) Real.pi) :=
        lipschitz_exp.hausdorffMeasure_image_le zero_le_one _
    _ < ⊤ := by
        rw [hausdorffMeasure_real, Real.volume_Icc]; simp

lemma L_pos : 0 < L := by
  rw [L_eq_complex]
  have hlip : LipschitzWith 1 Complex.re := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have hsub : Icc (-1 : ℝ) 1 ⊆ Complex.re '' sphere (0 : ℂ) 1 := by
    intro a ha
    refine ⟨a + Real.sqrt (1 - a ^ 2) * Complex.I, ?_, by simp⟩
    have h1 : 0 ≤ 1 - a ^ 2 := by nlinarith [ha.1, ha.2]
    simp only [mem_sphere, dist_zero_right]
    rw [Complex.norm_add_mul_I, Real.sq_sqrt h1]
    norm_num
  have h2 : (2 : ℝ≥0∞) ≤ μH[1] (sphere (0 : ℂ) 1) := by
    calc (2 : ℝ≥0∞) = μH[1] (Icc (-1 : ℝ) 1) := by
          rw [hausdorffMeasure_real, Real.volume_Icc]; norm_num
      _ ≤ μH[1] (Complex.re '' sphere (0 : ℂ) 1) := measure_mono hsub
      _ ≤ (1 : NNReal) ^ (1 : ℝ) * μH[1] (sphere (0 : ℂ) 1) :=
          hlip.hausdorffMeasure_image_le zero_le_one _
      _ = μH[1] (sphere (0 : ℂ) 1) := by simp
  exact lt_of_lt_of_le (by norm_num) h2

/-- Length of the circle of radius `√2`. -/
lemma perimeter_comparison :
    perimeter (closedBall (0 : Plane) (Real.sqrt 2)) = ENNReal.ofReal (Real.sqrt 2) * L := by
  have hs : (Real.sqrt 2 : ℝ) • sphere (0 : Plane) 1 = sphere (0 : Plane) (Real.sqrt 2) := by
    rw [_root_.smul_sphere _ _ zero_le_one, smul_zero, Real.norm_of_nonneg (Real.sqrt_nonneg 2), mul_one]
  rw [perimeter, frontier_closedBall _ (by positivity), ← hs,
    Measure.hausdorffMeasure_smul₀ zero_le_one (by positivity), L]
  simp [Real.nnnorm_of_nonneg (Real.sqrt_nonneg 2), ENNReal.ofReal,
    Real.toNNReal_of_nonneg (Real.sqrt_nonneg 2)]

lemma deficit_two (a : ℝ) (ha : 2 < |a|) : deficit (D 0 ∪ D a) = Real.sqrt 2 - 1 := by
  rw [deficit, eqRadius_of_area (vol_two a ha), perimeter_comparison, perimeter_two a ha,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg 2)]
  have hL : 0 < L.toReal := ENNReal.toReal_pos L_pos.ne' L_lt_top.ne
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  simp only [ENNReal.toReal_ofNat]
  field_simp
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  linear_combination -h

/-! ### Fraenkel asymmetry -/

lemma vol_D (a : ℝ) : vol.real (D a) = Real.pi := by
  rw [D, vol_ball _ zero_le_one]; ring

lemma fin_two (a : ℝ) (x : Plane) (r : ℝ) :
    vol (symmDiff (D 0 ∪ D a) (closedBall x r)) ≠ ⊤ :=
  measure_ne_top_of_subset symmDiff_subset_union
    (measure_union_lt_top (measure_union_lt_top measure_closedBall_lt_top
      measure_closedBall_lt_top) measure_closedBall_lt_top).ne

lemma sqrt2_lt : Real.sqrt 2 < 3 / 2 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `|(P ∪ Q) Δ B| ≥ |Q| + |B| - |P|` whenever `B` misses `Q`. -/
lemma symmDiff_lower {P Q B : Set Plane} (hPm : MeasurableSet P) (hP : vol P ≠ ⊤)
    (hQf : vol Q ≠ ⊤) (hB : MeasurableSet B) (hBf : vol B ≠ ⊤) (hBQ : Disjoint B Q)
    (hfin : vol (symmDiff (P ∪ Q) B) ≠ ⊤) :
    vol.real Q + (vol.real B - vol.real P) ≤ vol.real (symmDiff (P ∪ Q) B) := by
  have hsub : Q ∪ (B \ P) ⊆ symmDiff (P ∪ Q) B := by
    rintro y (hy | ⟨hyB, hyP⟩)
    · exact Or.inl ⟨Or.inr hy, fun hyB => hBQ.ne_of_mem hyB hy rfl⟩
    · refine Or.inr ⟨hyB, ?_⟩
      rintro (h | h)
      · exact hyP h
      · exact hBQ.ne_of_mem hyB h rfl
  have hdisj : Disjoint Q (B \ P) :=
    Set.disjoint_left.2 fun y hyQ hyBP => hBQ.ne_of_mem hyBP.1 hyQ rfl
  have hBPf : vol (B \ P) ≠ ⊤ := measure_ne_top_of_subset sdiff_subset hBf
  have h1 := measureReal_union (μ := vol) hdisj (hB.diff hPm) hQf hBPf
  have h2 : vol.real B - vol.real P ≤ vol.real (B \ P) := le_measureReal_sdiff hP
  have h3 := measureReal_mono (μ := vol) hsub hfin
  linarith

/-- For every centre `x`, the disk `B_x` of radius `√2` misses one of the far disks. -/
lemma far_cases (x : Plane) :
    Disjoint (closedBall x (Real.sqrt 2)) (D 10) ∨ Disjoint (closedBall x (Real.sqrt 2)) (D 0) := by
  by_contra h
  rw [not_or, Set.not_disjoint_iff, Set.not_disjoint_iff] at h
  obtain ⟨⟨y, hyB, hyD⟩, ⟨z, hzB, hzD⟩⟩ := h
  simp only [D, mem_closedBall] at hyB hyD hzB hzD
  have h : dist (pt 0) (pt 10) ≤ dist (pt 0) z + (dist z x + dist x y + dist y (pt 10)) :=
    calc dist (pt 0) (pt 10) ≤ dist (pt 0) z + dist z (pt 10) := dist_triangle _ _ _
      _ ≤ _ := by gcongr; exact dist_triangle4 _ _ _ _
  rw [dist_pt, dist_comm (pt 0) z, dist_comm x y] at h
  norm_num at h
  linarith [sqrt2_lt]

lemma asymmetry_far : 1 ≤ asymmetry Efar := by
  rw [asymmetry, eqRadius_far, area_far]
  refine le_ciInf fun x => ?_
  rw [le_div_iff₀ (by positivity), one_mul]
  have hB := vol_comparison x
  rcases far_cases x with h | h
  · have := symmDiff_lower measurableSet_closedBall (vol_ball_ne_top _ _) (vol_ball_ne_top _ _)
      measurableSet_closedBall (vol_ball_ne_top _ _) h (fin_two 10 x _)
    simp only [vol_ball _ zero_le_one, one_pow, one_mul, hB] at this
    simp only [Efar, D]; linarith
  · have hfin : vol (symmDiff (D 10 ∪ D 0) (closedBall x (Real.sqrt 2))) ≠ ⊤ := by
      rw [union_comm]; exact fin_two 10 x _
    have := symmDiff_lower measurableSet_closedBall (vol_ball_ne_top _ _) (vol_ball_ne_top _ _)
      measurableSet_closedBall (vol_ball_ne_top _ _) h hfin
    simp only [vol_ball _ zero_le_one, one_pow, one_mul, hB] at this
    rw [union_comm] at this
    simp only [Efar, D]; linarith

/-- The explicit centre `(2/5, 0)` gives `|Enear Δ B| ≤ 2π - π/50`. -/
lemma near_value :
    vol.real (symmDiff Enear (closedBall (pt (2 / 5)) (Real.sqrt 2))) ≤ 2 * Real.pi - Real.pi / 50 := by
  set B := closedBall (pt (2 / 5)) (Real.sqrt 2) with hBdef
  set S := closedBall (pt (8 / 5)) (1 / 10) with hSdef
  have hSD : S ⊆ D (5 / 2) := closedBall_subset_closedBall' (by rw [dist_pt]; norm_num)
  have hDB : D 0 ⊆ B := closedBall_subset_closedBall' (by
    rw [dist_pt]; apply Real.le_sqrt_of_sq_le; norm_num)
  have hSB : S ⊆ B := closedBall_subset_closedBall' (by
    rw [dist_pt]; apply Real.le_sqrt_of_sq_le; norm_num)
  have hdisj : Disjoint (D 0) S := (disj _ two_lt_near).mono_right hSD
  have hKE : D 0 ∪ S ⊆ Enear := union_subset subset_union_left (hSD.trans subset_union_right)
  have hKB : D 0 ∪ S ⊆ B := union_subset hDB hSB
  have hK : vol.real (D 0 ∪ S) = Real.pi + Real.pi / 100 := by
    rw [measureReal_union hdisj measurableSet_closedBall (vol_ball_ne_top _ _)
      (vol_ball_ne_top _ _), vol_D, hSdef, vol_ball _ (by norm_num)]; ring
  have hKm : MeasurableSet (D 0 ∪ S) := measurableSet_closedBall.union measurableSet_closedBall
  have hEf : vol Enear ≠ ⊤ := (measure_union_lt_top measure_closedBall_lt_top
    measure_closedBall_lt_top).ne
  have hsub : symmDiff Enear B ⊆ (Enear \ (D 0 ∪ S)) ∪ (B \ (D 0 ∪ S)) := by
    rw [Set.symmDiff_def]
    exact union_subset_union (sdiff_subset_sdiff_right hKB) (sdiff_subset_sdiff_right hKE)
  have h1 := measureReal_mono (μ := vol) hsub
    (measure_union_lt_top (measure_lt_top_of_subset sdiff_subset hEf)
      (measure_lt_top_of_subset sdiff_subset (vol_ball_ne_top _ _))).ne
  have h2 := measureReal_union_le (μ := vol) (Enear \ (D 0 ∪ S)) (B \ (D 0 ∪ S))
  rw [measureReal_sdiff hKE hKm hEf, measureReal_sdiff hKB hKm (vol_ball_ne_top _ _), hK] at h2
  have hB2 := vol_comparison (pt (2 / 5))
  rw [← hBdef] at hB2
  have hA : vol.real Enear = 2 * Real.pi := area_near
  linarith

lemma asymmetry_near_le : asymmetry Enear ≤ 99 / 100 := by
  rw [asymmetry, eqRadius_near, area_near]
  refine (ciInf_le ⟨0, ?_⟩ (pt (2 / 5))).trans ?_
  · rintro _ ⟨x, rfl⟩
    exact div_nonneg measureReal_nonneg (by positivity)
  · rw [div_le_iff₀ (by positivity)]
    linarith [near_value, Real.pi_pos]

lemma asymmetry_near : asymmetry Enear < 1 := asymmetry_near_le.trans_lt (by norm_num)

/-! ### Main theorem -/

/-- **Conjecture 00000006420.** The two explicit two-disk unions `Enear` and `Efar` (each a
union of two disjoint closed unit disks) have the same area `2π`, the same finite positive
perimeter, the same isoperimetric deficit `√2 - 1`, and different Fraenkel asymmetries:
`α(Enear) < 1 ≤ α(Efar)`. -/
theorem separation :
    (Enear = closedBall (pt 0) 1 ∪ closedBall (pt (5 / 2)) 1 ∧ Disjoint (D 0) (D (5 / 2))) ∧
    (Efar = closedBall (pt 0) 1 ∪ closedBall (pt 10) 1 ∧ Disjoint (D 0) (D 10)) ∧
    area Enear = 2 * Real.pi ∧ area Efar = 2 * Real.pi ∧
    perimeter Enear = perimeter Efar ∧ 0 < perimeter Enear ∧ perimeter Enear < ⊤ ∧
    deficit Enear = Real.sqrt 2 - 1 ∧ deficit Efar = Real.sqrt 2 - 1 ∧
    asymmetry Enear < 1 ∧ 1 ≤ asymmetry Efar ∧ asymmetry Enear ≠ asymmetry Efar := by
  have hp : perimeter Enear = 2 * L := perimeter_two _ two_lt_near
  refine ⟨⟨rfl, disj _ two_lt_near⟩, ⟨rfl, disj _ two_lt_far⟩, area_near, area_far,
    hp.trans (perimeter_two _ two_lt_far).symm, ?_, ?_, deficit_two _ two_lt_near,
    deficit_two _ two_lt_far, asymmetry_near, asymmetry_far,
    (asymmetry_near.trans_le asymmetry_far).ne⟩
  · rw [hp]; exact ENNReal.mul_pos (by norm_num) L_pos.ne'
  · rw [hp]; exact ENNReal.mul_lt_top (by norm_num) L_lt_top

/-- Existential form: two unions of two closed disks with equal deficit, different asymmetry. -/
theorem conjecture6420 :
    ∃ E F : Set Plane,
      (∃ c₁ c₂ : Plane, ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ 0 < r₂ ∧
        Disjoint (closedBall c₁ r₁) (closedBall c₂ r₂) ∧ E = closedBall c₁ r₁ ∪ closedBall c₂ r₂) ∧
      (∃ c₁ c₂ : Plane, ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ 0 < r₂ ∧
        Disjoint (closedBall c₁ r₁) (closedBall c₂ r₂) ∧ F = closedBall c₁ r₁ ∪ closedBall c₂ r₂) ∧
      deficit E = deficit F ∧ asymmetry E ≠ asymmetry F := by
  obtain ⟨-, -, -, -, -, -, -, h1, h2, -, -, h3⟩ := separation
  exact ⟨Enear, Efar, ⟨_, _, 1, 1, one_pos, one_pos, disj _ two_lt_near, rfl⟩,
    ⟨_, _, 1, 1, one_pos, one_pos, disj _ two_lt_far, rfl⟩, h1.trans h2.symm, h3⟩

/-- Normalisation independence: any deficit computed from (perimeter, area) agrees, and any
positive rescaling of the asymmetry still separates. -/
theorem normalisations (f : ℝ≥0∞ → ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    f (perimeter Enear) (area Enear) = f (perimeter Efar) (area Efar) ∧
    c * asymmetry Enear < c * asymmetry Efar := by
  obtain ⟨-, -, ha1, ha2, hp, -, -, -, -, h1, h2, -⟩ := separation
  exact ⟨by rw [hp, ha1, ha2], mul_lt_mul_of_pos_left (h1.trans_le h2) hc⟩

/-- Perimeter-convention independence: any perimeter functional that is translation invariant
and additive on disjoint compact sets (as the De Giorgi perimeter is) takes the same value on
`Enear` and `Efar`, so every deficit built from that perimeter and the area agrees. -/
theorem perimeter_axiomatic (Per : Set Plane → ℝ≥0∞)
    (htr : ∀ (v : Plane) (E : Set Plane), Per ((· + v) '' E) = Per E)
    (hadd : ∀ A B : Set Plane, IsCompact A → IsCompact B → Disjoint A B →
      Per (A ∪ B) = Per A + Per B) (f : ℝ≥0∞ → ℝ → ℝ) :
    Per Enear = Per Efar ∧ f (Per Enear) (area Enear) = f (Per Efar) (area Efar) := by
  have hD : ∀ a, Per (D a) = Per (D 0) := by
    intro a
    have h := IsometryEquiv.image_closedBall (IsometryEquiv.addRight (pt a)) (pt 0) 1
    have h0 : pt 0 = 0 := by simp [pt]
    rw [IsometryEquiv.addRight_apply, h0, zero_add] at h
    rw [D, ← h, D, h0]
    exact htr _ _
  have key : ∀ a, 2 < |a| → Per (D 0 ∪ D a) = Per (D 0) + Per (D 0) := fun a ha => by
    rw [hadd (D 0) (D a) (isCompact_closedBall _ _) (isCompact_closedBall _ _) (disj a ha), hD a]
  have h1 := key _ two_lt_near
  have h2 := key _ two_lt_far
  refine ⟨h1.trans h2.symm, ?_⟩
  rw [area_near, area_far]
  simp only [Enear, Efar] at *
  rw [h1, h2]

end C6420
