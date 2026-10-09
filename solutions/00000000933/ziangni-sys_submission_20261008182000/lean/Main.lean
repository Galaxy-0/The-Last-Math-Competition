import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

open Complex Metric
open scoped ComplexConjugate
namespace RieszCounterexample
abbrev E := ℂ × ℂ
abbrev Op := E →L[ℂ] E
noncomputable def P (k : ℝ) : Op :=
  ((k : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod (ContinuousLinearMap.snd ℂ ℂ ℂ)
@[simp] theorem P_apply (k : ℝ) (v : E) : P k v = ((k : ℂ)*v.2, v.2) := rfl
noncomputable def Q (k : ℝ) : Op := 1-P k
@[simp] theorem Q_apply (k : ℝ) (v : E) : Q k v = (v.1-(k : ℂ)*v.2, 0) := by
  ext <;> simp [Q]
noncomputable def resolvent (k : ℝ) (z : ℂ) : Op := z⁻¹ • Q k + (z-1)⁻¹ • P k
noncomputable def shifted (k : ℝ) (z : ℂ) : Op := z • (1 : Op) - P k

theorem inverse_left (k : ℝ) (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    resolvent k z * shifted k z = 1 := by
  apply ContinuousLinearMap.ext; intro v; apply Prod.ext <;> simp [resolvent, shifted, Q_apply, P_apply] <;> field_simp [h0, sub_ne_zero.mpr h1] <;> ring

theorem inverse_right (k : ℝ) (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    shifted k z * resolvent k z = 1 := by
  apply ContinuousLinearMap.ext; intro v; apply Prod.ext <;> simp [resolvent, shifted, Q_apply, P_apply] <;> field_simp [h0, sub_ne_zero.mpr h1] <;> ring

theorem spectrum_exact (k : ℝ) : spectrum ℂ (P k) = {0,1} := by
  ext z
  rw [spectrum.mem_iff]
  change ¬ IsUnit (shifted k z) ↔ z ∈ ({0,1} : Set ℂ)
  constructor
  · intro hn
    by_contra hm
    have hm' : z ≠ 0 ∧ z ≠ 1 := by simpa using hm
    have h0 := hm'.1
    have h1 := hm'.2
    exact hn (isUnit_iff_exists.mpr ⟨resolvent k z, inverse_right k z h0 h1, inverse_left k z h0 h1⟩)
  · intro hz hu
    obtain ⟨b, hb, hb'⟩ := isUnit_iff_exists.mp hu
    rcases hz with rfl | hz
    · have hv := congrArg (fun A : Op => A (1,0)) hb'
      simp [shifted] at hv
      have hf := congrArg Prod.fst hv
      norm_num at hf
    · have hz1 : z = 1 := hz
      subst z
      have hv := congrArg (fun A : Op => A ((k : ℂ),1)) hb'
      simp [shifted] at hv
      have hf := congrArg Prod.snd hv
      norm_num at hf

-- Actual scalar contour integrals, including the pole outside the contour.
theorem outside_integral (c w : ℂ) (h : (1/2 : ℝ) < dist w c) :
    (∮ z in C(c, (1/2 : ℝ)), (z-w)⁻¹) = 0 := by
  have hn : ∀ z ∈ closedBall c (1/2 : ℝ), z-w ≠ 0 := by
    intro z hz he
    have := sub_eq_zero.mp he
    subst z
    exact (not_le_of_gt h) hz
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable (by norm_num)
    Set.countable_empty
  · exact (continuousOn_id.sub continuousOn_const).inv₀ hn
  · intro z hz
    exact (differentiableAt_id.sub_const w).inv (hn z (ball_subset_closedBall hz.1))


theorem inverse_continuous (c w : ℂ) (h : dist w c ≠ (1/2 : ℝ)) :
    ContinuousOn (fun z => (z-w)⁻¹) (sphere c (1/2 : ℝ)) := by
  apply (continuousOn_id.sub continuousOn_const).inv₀
  intro z hz he
  have he' : z = w := sub_eq_zero.mp he
  subst z
  exact h hz

noncomputable def riesz (k : ℝ) (c : ℂ) : Op :=
  (2*Real.pi*Complex.I : ℂ)⁻¹ • ∮ z in C(c, (1/2 : ℝ)), resolvent k z

theorem riesz_formula (k : ℝ) (c : ℂ)
    (h0 : dist 0 c ≠ (1/2 : ℝ)) (h1 : dist 1 c ≠ (1/2 : ℝ)) :
    riesz k c = (2*Real.pi*Complex.I : ℂ)⁻¹ •
      (((∮ z in C(c, (1/2 : ℝ)), (z-0)⁻¹) • Q k) +
       ((∮ z in C(c, (1/2 : ℝ)), (z-1)⁻¹) • P k)) := by
  unfold riesz resolvent
  rw [circleIntegral.integral_add]
  · simp only [circleIntegral.integral_smul_const, sub_zero]
  · simpa using ((inverse_continuous c 0 h0).smul continuousOn_const).circleIntegrable (by norm_num)
  · exact ((inverse_continuous c 1 h1).smul continuousOn_const).circleIntegrable (by norm_num)

theorem riesz_zero (k : ℝ) : riesz k 0 = Q k := by
  rw [riesz_formula k 0 (by norm_num) (by norm_num),
    circleIntegral.integral_sub_inv_of_mem_ball (by simp [Metric.mem_ball]),
    outside_integral 0 1 (by norm_num)]
  apply ContinuousLinearMap.ext; intro v; apply Prod.ext <;>
    simp [smul_add, smul_smul, Q_apply, P_apply] <;>
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem riesz_one (k : ℝ) : riesz k 1 = P k := by
  rw [riesz_formula k 1 (by norm_num) (by norm_num),
    outside_integral 1 0 (by norm_num),
    circleIntegral.integral_sub_inv_of_mem_ball (by simp [Metric.mem_ball])]
  apply ContinuousLinearMap.ext; intro v; apply Prod.ext <;>
    simp [smul_add, smul_smul, Q_apply, P_apply] <;>
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem projection_norms (k : ℝ) : |k| ≤ ‖P k‖ ∧ |k| ≤ ‖Q k‖ := by
  have hp := (P k).le_opNorm ((0,1) : E)
  have hq := (Q k).le_opNorm ((0,1) : E)
  simp [Prod.norm_def, P_apply, Q_apply] at hp hq
  constructor
  · exact hp.1
  · exact hq

-- For a two-point spectrum the nontrivial splits are exactly the two singleton subsets.
def nontrivialSplit (s : Set ℂ) : Prop := s ⊆ {0,1} ∧ s.Nonempty ∧ s ≠ {0,1}

theorem splitting_set (s : Set ℂ) : nontrivialSplit s ↔ s = {0} ∨ s = {1} := by
  constructor
  · rintro ⟨hs, hne, hfull⟩
    rcases hne.subset_pair_iff_eq.mp hs with h0 | h1 | h2
    · exact Or.inl h0
    · exact Or.inr h1
    · exact False.elim (hfull h2)
  · rintro (rfl | rfl)
    · refine ⟨by simp, by simp, ?_⟩
      intro he
      have hh : (1 : ℂ) ∈ ({0} : Set ℂ) := by rw [he]; simp
      norm_num at hh
    · refine ⟨by simp, by simp, ?_⟩
      intro he
      have hh : (0 : ℂ) ∈ ({1} : Set ℂ) := by rw [he]; simp
      norm_num at hh
noncomputable def splittingInfimum (k : ℝ) : ℝ := sInf {‖riesz k 0‖, ‖riesz k 1‖}

theorem infimum_unbounded : ∀ B : ℝ, ∃ k : ℝ, B < splittingInfimum k := by
  intro B
  refine ⟨|B|+1, ?_⟩
  have hp := (projection_norms (|B|+1)).1
  have hq := (projection_norms (|B|+1)).2
  rw [splittingInfimum, csInf_pair, riesz_zero, riesz_one]
  apply lt_min
  · have := le_abs_self B
    have hk : 0 ≤ |B|+1 := by positivity
    rw [abs_of_nonneg hk] at hq
    linarith
  · have := le_abs_self B
    have hk : 0 ≤ |B|+1 := by positivity
    rw [abs_of_nonneg hk] at hp
    linarith

#print axioms inverse_left
#print axioms inverse_right
#print axioms spectrum_exact
#print axioms riesz_zero
#print axioms riesz_one
#print axioms projection_norms
#print axioms splitting_set
#print axioms infimum_unbounded
end RieszCounterexample
