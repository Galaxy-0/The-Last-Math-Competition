import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.NormedSpace.OperatorNorm.Mul
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

noncomputable section
open ContinuousLinearMap
namespace RankOneBackwardError
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Actual continuous rank-at-most-one operator built from the inner product. -/
def correction (x : E) (r : F) : E →L[𝕜] F :=
  ((‖x‖ : 𝕜)^2)⁻¹ • (toSpanSingleton 𝕜 r).comp (innerSL 𝕜 x)

theorem correction_apply (x v : E) (r : F) :
    correction (𝕜:=𝕜) x r v=(((‖x‖:𝕜)^2)⁻¹ * (@inner 𝕜 E _ x v)) • r := by
  simp [correction,smul_smul,toSpanSingleton_apply]

theorem correction_solves (x : E) (hx : x≠0) (r : F) :
    correction (𝕜:=𝕜) x r x=r := by
  rw [correction_apply,inner_self_eq_norm_sq_to_K]
  have hn : (‖x‖:𝕜)≠0 := by simp [hx]
  simp [hn]

theorem universal_lower_bound (x : E) (hx : x≠0) (r : F)
    (D : E →L[𝕜] F) (hD : D x=r) : ‖r‖/‖x‖≤‖D‖ := by
  apply (div_le_iff₀ (norm_pos_iff.mpr hx)).2
  rw [← hD]
  exact D.le_opNorm x

theorem correction_norm_le (x : E) (hx : x≠0) (r : F) :
    ‖correction (𝕜:=𝕜) x r‖≤‖r‖/‖x‖ := by
  have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
  calc ‖correction (𝕜:=𝕜) x r‖
      ≤ ‖((‖x‖:𝕜)^2)⁻¹‖ * ‖(toSpanSingleton 𝕜 r).comp (innerSL 𝕜 x)‖ :=
        opNorm_smul_le _ _
    _ = (‖x‖^2)⁻¹ * ‖(toSpanSingleton 𝕜 r).comp (innerSL 𝕜 x)‖ := by
      rw [norm_inv,norm_pow,RCLike.norm_ofReal,abs_norm]
    _
      ≤ (‖x‖^2)⁻¹ * (‖toSpanSingleton 𝕜 r‖ * ‖innerSL 𝕜 x‖) :=
        mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (by positivity)
    _ = ‖r‖/‖x‖ := by
      rw [norm_toSpanSingleton,innerSL_apply_norm]
      field_simp
      <;> ring

theorem correction_norm (x : E) (hx : x≠0) (r : F) :
    ‖correction (𝕜:=𝕜) x r‖=‖r‖/‖x‖ := by
  exact le_antisymm (correction_norm_le x hx r)
    (universal_lower_bound x hx r _ (correction_solves x hx r))

theorem correction_range (x : E) (hx : x≠0) (r : F) :
    LinearMap.range (correction (𝕜:=𝕜) x r).toLinearMap=Submodule.span 𝕜 {r} := by
  apply le_antisymm
  · rintro y ⟨v,rfl⟩
    rw [show (correction (𝕜:=𝕜) x r).toLinearMap v=correction (𝕜:=𝕜) x r v from rfl,
      correction_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro y hy
    have he : y=r := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨x,correction_solves x hx r⟩

theorem rank_exactly_one (x : E) (hx : x≠0) (r : F) (hr : r≠0) :
    Module.finrank 𝕜 (LinearMap.range (correction (𝕜:=𝕜) x r).toLinearMap)=1 := by
  rw [correction_range x hx r]
  exact finrank_span_singleton hr

theorem zero_residual (x : E) : correction (𝕜:=𝕜) x (0:F)=0 := by
  ext v
  simp [correction_apply]

/-- The complete feasible set of absolute, A-only operator-norm perturbation magnitudes. -/
def feasibleNorms (A : E →L[𝕜] F) (x : E) (b : F) : Set ℝ :=
  {c | ∃ D : E →L[𝕜] F, (A+D) x=b ∧ ‖D‖=c}

theorem corrected_equation (A : E →L[𝕜] F) (x : E) (hx : x≠0) (b : F) :
    (A+correction (𝕜:=𝕜) x (b-A x)) x=b := by
  simp [correction_solves x hx]

theorem optimum_isLeast (A : E →L[𝕜] F) (x : E) (hx : x≠0) (b : F) :
    IsLeast (feasibleNorms A x b) (‖b-A x‖/‖x‖) := by
  constructor
  · exact ⟨correction x (b-A x),corrected_equation A x hx b,correction_norm x hx _⟩
  · rintro c ⟨D,hD,rfl⟩
    apply universal_lower_bound x hx (b-A x) D
    have he : A x+D x=b := hD
    exact eq_sub_of_add_eq' he

/-- The genuine infimum equals the ratio, and the preceding theorem proves attainment. -/
theorem backward_error_exact (A : E →L[𝕜] F) (x : E) (hx : x≠0) (b : F) :
    sInf (feasibleNorms A x b)=‖b-A x‖/‖x‖ := (optimum_isLeast A x hx b).csInf_eq

theorem optimal_rank_one (A : E →L[𝕜] F) (x : E) (hx : x≠0) (b : F)
    (hr : b-A x≠0) : ∃ D : E →L[𝕜] F,
    (A+D) x=b ∧ Module.finrank 𝕜 (LinearMap.range D.toLinearMap)=1 ∧
    ‖D‖=‖b-A x‖/‖x‖ ∧ ∀ B : E →L[𝕜] F, (A+B) x=b → ‖D‖≤‖B‖ := by
  refine ⟨correction x (b-A x),corrected_equation A x hx b,
    rank_exactly_one x hx _ hr,correction_norm x hx _,?_⟩
  intro B hB
  rw [correction_norm x hx]
  exact (optimum_isLeast A x hx b).2 ⟨B,hB,rfl⟩

#print axioms correction_apply
#print axioms correction_solves
#print axioms universal_lower_bound
#print axioms correction_norm
#print axioms correction_range
#print axioms rank_exactly_one
#print axioms zero_residual
#print axioms corrected_equation
#print axioms optimum_isLeast
#print axioms backward_error_exact
#print axioms optimal_rank_one
end RankOneBackwardError
