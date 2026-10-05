import Conjecture5960.Family
import Mathlib.Analysis.InnerProductSpace.Projection

noncomputable section
namespace Conjecture5960

def eigenspaceOne (A : Mat2) : Submodule ℝ Plane :=
  Module.End.eigenspace (Matrix.toEuclideanLin A) 1

def firstAxis : Plane := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![1, 0]

/-- Intrinsic, sign-independent eigenvector statistic, defined using the actual eigenspace. -/
def statistic (A : Mat2) : ℝ := ‖(eigenspaceOne A).orthogonalProjection firstAxis‖ ^ 2

theorem firstVector_mem_eigenspaceOne (t : ℝ) :
    firstVector t ∈ eigenspaceOne (matrixFamily t) := by
  change firstVector t ∈ Module.End.eigenspace (Matrix.toEuclideanLin (matrixFamily t)) 1
  rw [Module.End.mem_eigenspace_iff, one_smul]
  exact firstVector_eigen t

theorem eigenspaceOne_vector_formula (t : ℝ) (w : Plane)
    (hw : w ∈ eigenspaceOne (matrixFamily t)) :
    w = (cosine t * w 0 + sine t * w 1) • firstVector t := by
  have he : Matrix.toEuclideanLin (matrixFamily t) w = w := by
    simpa only [eigenspaceOne, Module.End.mem_eigenspace_iff, one_smul] using hw
  have h0 := congrArg (fun v : Plane => v 0) he
  have h1 := congrArg (fun v : Plane => v 1) he
  simp only [Matrix.toEuclideanLin_apply, matrixFamily_explicit, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] at h0 h1
  simp [Matrix.vecHead, Matrix.vecTail] at h0 h1
  have hu := cosine_sq_add_sine_sq t
  have hu0 := congrArg (fun x : ℝ => x * w 0) hu
  have hu1 := congrArg (fun x : ℝ => x * w 1) hu
  dsimp at hu0 hu1
  have hs : sine t * (sine t * w 0 - cosine t * w 1) = 0 := by
    nlinarith only [h0, hu0]
  have hc : cosine t * (sine t * w 0 - cosine t * w 1) = 0 := by
    nlinarith only [h1, hu1]
  have hd : sine t * w 0 - cosine t * w 1 = 0 := by
    by_cases hsin : sine t = 0
    · have hcos : cosine t ≠ 0 := by intro h; simp [h, hsin] at hu
      exact (mul_eq_zero.mp hc).resolve_left hcos
    · exact (mul_eq_zero.mp hs).resolve_left hsin
  ext i
  fin_cases i
  · change w 0 = (cosine t * w 0 + sine t * w 1) * cosine t
    nlinarith only [hu0, congrArg (fun x : ℝ => sine t * x) hd]
  · change w 1 = (cosine t * w 0 + sine t * w 1) * sine t
    nlinarith only [hu1, congrArg (fun x : ℝ => cosine t * x) hd]

theorem eigenspaceOne_matrixFamily (t : ℝ) :
    eigenspaceOne (matrixFamily t) = Submodule.span ℝ {firstVector t} := by
  ext w
  constructor
  · intro hw
    rw [Submodule.mem_span_singleton]
    exact ⟨cosine t * w 0 + sine t * w 1, (eigenspaceOne_vector_formula t w hw).symm⟩
  · intro hw
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨a, rfl⟩ := hw
    exact Submodule.smul_mem _ a (firstVector_mem_eigenspaceOne t)

theorem projection_matrixFamily (t : ℝ) (w : Plane) :
    ((eigenspaceOne (matrixFamily t)).orthogonalProjection w : Plane) =
      @inner ℝ Plane _ (firstVector t) w • firstVector t := by
  rw [eigenspaceOne_matrixFamily]
  exact Submodule.orthogonalProjection_unit_singleton ℝ (firstVector_norm t) w

theorem inner_firstVector_firstAxis (t : ℝ) :
    @inner ℝ Plane _ (firstVector t) firstAxis = cosine t := by
  simp [PiLp.inner_apply, firstVector, firstAxis, Fin.sum_univ_two]

theorem statistic_matrixFamily (t : ℝ) : statistic (matrixFamily t) = cosine t ^ 2 := by
  unfold statistic
  change ‖((eigenspaceOne (matrixFamily t)).orthogonalProjection firstAxis : Plane)‖ ^ 2 = _
  rw [projection_matrixFamily, inner_firstVector_firstAxis, norm_smul, firstVector_norm]
  simp [Real.norm_eq_abs]

/-- The intrinsic statistic equals the squared first coordinate for every unit eigenvector. -/
theorem statistic_eq_normalized_eigenvector (t : ℝ) (w : Plane)
    (hw : w ∈ eigenspaceOne (matrixFamily t)) (hn : ‖w‖ = 1) :
    statistic (matrixFamily t) = (w 0) ^ 2 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    (show w ∈ Submodule.span ℝ {firstVector t} by rw [← eigenspaceOne_matrixFamily]; exact hw)
  have han : ‖a‖ = 1 := by
    have h := congrArg norm ha
    simpa [norm_smul, firstVector_norm, hn] using h
  have hasq : a ^ 2 = 1 := by nlinarith [sq_abs a, Real.norm_eq_abs a]
  rw [statistic_matrixFamily, ← ha]
  change cosine t ^ 2 = (a * cosine t) ^ 2
  rw [mul_pow, hasq, one_mul]

theorem cosine_nonneg_on_unitInterval {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ cosine t := by
  unfold cosine
  apply div_nonneg
  · nlinarith [ht.1, ht.2]
  · exact (denominator_pos t).le

/-- The parameter genuinely changes orientation; on this interval no two matrices coincide. -/
theorem matrixFamily_injOn_unitInterval : Set.InjOn matrixFamily (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hsq := congrArg statistic hab
  rw [statistic_matrixFamily, statistic_matrixFamily] at hsq
  have hc : cosine a = cosine b := by
    nlinarith [cosine_nonneg_on_unitInterval ha, cosine_nonneg_on_unitInterval hb]
  have hcross : (1-a^2)*(1+b^2) = (1-b^2)*(1+a^2) := by
    exact (div_eq_div_iff (denominator_pos a).ne' (denominator_pos b).ne').mp hc
  nlinarith [ha.1, hb.1]

@[fun_prop] theorem continuous_firstVector : Continuous firstVector := by
  unfold firstVector
  apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · simpa using continuous_cosine
  · simpa using continuous_sine

@[fun_prop] theorem continuous_secondVector : Continuous secondVector := by
  unfold secondVector
  apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · simpa using continuous_sine.neg
  · simpa using continuous_cosine

end Conjecture5960
