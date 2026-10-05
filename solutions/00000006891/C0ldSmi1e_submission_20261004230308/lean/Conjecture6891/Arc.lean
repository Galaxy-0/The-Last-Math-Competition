import Conjecture6891.Projective
import Mathlib.Topology.Algebra.MvPolynomial

set_option synthInstance.maxHeartbeats 80000

noncomputable section
namespace Conjecture6891

/-- The three terms with exactly two second-basis factors. -/
def U : Tensor := pure e0 e1 e1 + pure e1 e0 e1 + pure e1 e1 e0

/-- The polynomial arc obtained by removing the constant term of a Segre curve. -/
def arc (t : ℂ) : Tensor := W + t • U + t ^ 2 • pure e1 e1 e1

@[simp] theorem coords_U (i j k : Fin 2) :
    coords U (i, (j, k)) =
      e0 i * e1 j * e1 k + e1 i * e0 j * e1 k + e1 i * e1 j * e0 k := by
  simp [U]

@[simp] theorem coords_arc (t : ℂ) (i j k : Fin 2) :
    coords (arc t) (i, (j, k)) = coords W (i, (j, k)) +
      t * coords U (i, (j, k)) + t ^ 2 * (e1 i * e1 j * e1 k) := by
  simp [arc]

@[simp] theorem arc_zero : arc 0 = W := by simp [arc]

theorem arc_ne_zero (t : ℂ) : arc t ≠ 0 := by
  intro h
  have he := congrArg (fun x => coords x (0, (1, 0))) h
  norm_num [e0, e1] at he

/-- A point on the underlying affine Segre curve. -/
def segreCurve (t : ℂ) : Tensor :=
  pure (e0 + t • e1) (e0 + t • e1) (e0 + t • e1)

/-- The fixed endpoint of the secant lines. -/
def baseTensor : Tensor := pure e0 e0 e0

theorem segreCurve_ne_zero (t : ℂ) : segreCurve t ≠ 0 := by
  intro h
  have he := congrArg (fun x => coords x (0, (0, 0))) h
  simp only [segreCurve, coords_pure, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    map_zero, Pi.zero_apply] at he
  norm_num [e0, e1] at he

theorem baseTensor_ne_zero : baseTensor ≠ 0 := by
  simpa [segreCurve, baseTensor] using segreCurve_ne_zero 0

theorem smul_arc (t : ℂ) : t • arc t = segreCurve t - baseTensor := by
  apply tensor_ext
  intro i j k
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_sub, Pi.sub_apply,
    coords_arc, segreCurve, baseTensor, coords_pure, coords_W, coords_U, Pi.add_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [e0, e1]
  all_goals ring

theorem continuous_coords_arc : Continuous (fun t : ℂ => coords (arc t)) := by
  apply continuous_pi
  intro i
  rcases i with ⟨i, j, k⟩
  simp only [coords_arc]
  fun_prop

/-- The projective points of the nonzero polynomial arc. -/
def projectiveArc (t : ℂ) : Projectivization ℂ Tensor :=
  Projectivization.mk ℂ (arc t) (arc_ne_zero t)

def projectiveCurve (t : ℂ) : Projectivization ℂ Tensor :=
  Projectivization.mk ℂ (segreCurve t) (segreCurve_ne_zero t)

def projectiveBase : Projectivization ℂ Tensor :=
  Projectivization.mk ℂ baseTensor baseTensor_ne_zero

def projectiveW : Projectivization ℂ Tensor := Projectivization.mk ℂ W W_ne_zero

@[simp] theorem projectiveArc_zero : projectiveArc 0 = projectiveW := by
  simp [projectiveArc, projectiveW]

/-- For a nonzero parameter the two Segre generators are projectively distinct. -/
theorem projectiveCurve_ne_base (t : ℂ) (ht : t ≠ 0) :
    projectiveCurve t ≠ projectiveBase := by
  intro h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have h1 := congrArg (fun x => coords x (0, (0, 1))) ha
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, segreCurve, baseTensor,
    coords_pure, Pi.add_apply] at h1
  norm_num [e0, e1] at h1
  exact ht h1.symm

/-- The arc point lies on the line through two distinct actual Segre points. -/
theorem projectiveArc_mem_span (t : ℂ) (ht : t ≠ 0) :
    projectiveArc t ∈ Projectivization.Subspace.span
      (Set.range (![projectiveCurve t, projectiveBase] : Fin 2 → Projectivization ℂ Tensor)) := by
  let points : Fin 2 → Projectivization ℂ Tensor := ![projectiveCurve t, projectiveBase]
  let line := Projectivization.Subspace.span (Set.range points)
  have hc : projectiveCurve t ∈ line :=
    Projectivization.Subspace.subset_span _ ⟨0, rfl⟩
  have hb : projectiveBase ∈ line :=
    Projectivization.Subspace.subset_span _ ⟨1, rfl⟩
  have hn : segreCurve t + -baseTensor ≠ 0 := by
    have h := smul_ne_zero ht (arc_ne_zero t)
    simpa only [smul_arc, sub_eq_add_neg] using h
  have hm : -baseTensor ≠ 0 :=
    (@neg_ne_zero Tensor inferInstance baseTensor).mpr baseTensor_ne_zero
  have heq : Projectivization.mk ℂ (-baseTensor) hm = projectiveBase := by
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨-1, by simp⟩
  have hs := line.mem_add (segreCurve t) (-baseTensor) (segreCurve_ne_zero t) hm hn
    hc (heq.symm ▸ hb)
  have hscale : Projectivization.mk ℂ (segreCurve t + -baseTensor) hn =
      projectiveArc t := by
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨t, by simpa only [sub_eq_add_neg] using smul_arc t⟩
  exact hscale ▸ hs

/-- A homogeneous quadratic cutting out all pure tensors but not W. -/
def sliceMinor : MvPolynomial Coordinate ℂ :=
  MvPolynomial.X (0, (0, 0)) * MvPolynomial.X (0, (1, 1)) -
    MvPolynomial.X (0, (0, 1)) * MvPolynomial.X (0, (1, 0))

theorem sliceMinor_homogeneous : sliceMinor.IsHomogeneous 2 := by
  exact ((MvPolynomial.isHomogeneous_X ℂ _).mul
    (MvPolynomial.isHomogeneous_X ℂ _)).sub
      ((MvPolynomial.isHomogeneous_X ℂ _).mul (MvPolynomial.isHomogeneous_X ℂ _))

@[simp] theorem sliceMinor_pure (a b c : Vector) :
    MvPolynomial.eval (coords (pure a b c)) sliceMinor = 0 := by
  simp only [sliceMinor, map_sub, map_mul, MvPolynomial.eval_X, coords_pure]
  ring

@[simp] theorem sliceMinor_W : MvPolynomial.eval (coords W) sliceMinor = -1 := by
  simp only [sliceMinor, map_sub, map_mul, MvPolynomial.eval_X, coords_W]
  norm_num [e0, e1]

theorem projectiveCurve_mem_segre (t : ℂ) : projectiveCurve t ∈ segre := by
  exact ⟨e0 + t • e1, e0 + t • e1, e0 + t • e1, segreCurve_ne_zero t, rfl⟩

theorem projectiveBase_mem_segre : projectiveBase ∈ segre := by
  exact ⟨e0, e0, e0, baseTensor_ne_zero, rfl⟩

theorem projectiveArc_mem_secantSpanLocus_two (t : ℂ) (ht : t ≠ 0) :
    projectiveArc t ∈ secantSpanLocus 2 := by
  refine ⟨![projectiveCurve t, projectiveBase], ?_, projectiveArc_mem_span t ht⟩
  intro i
  fin_cases i
  · exact projectiveCurve_mem_segre t
  · exact projectiveBase_mem_segre

/-- Every equation of the entire second span locus vanishes at the limiting point. -/
theorem projectiveW_mem_secantVariety_two : projectiveW ∈ secantVariety 2 := by
  intro d p hp hvan
  apply (projectiveVanishes_mk_iff hp W W_ne_zero).mpr
  let f : ℂ → ℂ := fun t => MvPolynomial.eval (coords (arc t)) p
  have hf : Continuous f := p.continuous_eval.comp continuous_coords_arc
  have heq : Set.EqOn f (fun _ => 0) ({0}ᶜ : Set ℂ) := by
    intro t ht
    exact hvan (projectiveArc t) (projectiveArc_mem_secantSpanLocus_two t ht)
      (arc t) (arc_ne_zero t) rfl
  have h0 : (0 : ℂ) ∈ closure ({0}ᶜ : Set ℂ) := (dense_compl_singleton 0) 0
  simpa only [f, arc_zero] using (heq.closure hf continuous_const) h0

theorem sliceMinor_vanishes_on_segre (x : ProjectiveTensor) (hx : x ∈ segre) :
    ProjectiveVanishes sliceMinor x := by
  obtain ⟨a, b, c, h, rfl⟩ := hx
  exact (projectiveVanishes_mk_iff sliceMinor_homogeneous (pure a b c) h).mpr
    (sliceMinor_pure a b c)

/-- The first closed secant is separated from W by an actual homogeneous equation. -/
theorem projectiveW_not_mem_secantVariety_one : projectiveW ∉ secantVariety 1 := by
  intro h
  have hvan : ProjectiveVanishes sliceMinor projectiveW :=
    h 2 sliceMinor sliceMinor_homogeneous (by
      rw [secantSpanLocus_one]
      exact sliceMinor_vanishes_on_segre)
  have hz := hvan W W_ne_zero rfl
  rw [sliceMinor_W] at hz
  norm_num at hz

theorem projectiveW_in_second_layer :
    projectiveW ∈ secantVariety 2 ∧ projectiveW ∉ secantVariety 1 :=
  ⟨projectiveW_mem_secantVariety_two, projectiveW_not_mem_secantVariety_one⟩

end Conjecture6891
