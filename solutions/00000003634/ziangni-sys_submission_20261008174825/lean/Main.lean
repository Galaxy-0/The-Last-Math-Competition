import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

namespace FloquetJordan
abbrev E := ℝ × ℝ
noncomputable def N : E →L[ℝ] E := (ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0
@[simp] theorem N_apply (v : E) : N v = (v.2, 0) := rfl
noncomputable def fundamental (t : ℝ) : E →L[ℝ] E := 1 + t • N

theorem N_squared : N ^ 2 = 0 := by
  ext v <;> simp [pow_two]

/-- The actual operator exponential has the advertised fundamental matrix. -/
theorem exponential (t : ℝ) : NormedSpace.exp ℝ (t • N) = fundamental t := by
  have hsquare : (t • N) ^ 2 = 0 := by
    ext v <;> simp [pow_two]
  rw [NormedSpace.exp_eq_tsum]
  dsimp only
  rw [tsum_eq_sum (s := Finset.range 2) (fun n hn => ?_)]
  · simp [fundamental, Finset.sum_range_succ]
  · have hn2 : 2 ≤ n := by simpa using hn
    rw [pow_eq_zero_of_le hn2 hsquare, smul_zero]

@[simp] theorem fundamental_apply (t : ℝ) (v : E) :
    fundamental t v = (v.1 + t*v.2, v.2) := by
  apply Prod.ext <;> simp [fundamental, N_apply]

theorem fundamental_initial : fundamental 0 = 1 := by simp [fundamental]

theorem fundamental_inverse (t : ℝ) : fundamental (-t) * fundamental t = 1 := by
  ext v <;> simp <;> ring

theorem fundamental_ode (t : ℝ) (v : E) :
    HasDerivAt (fun s => fundamental s v) (N (fundamental t v)) t := by
  simpa using ((hasDerivAt_const t v.1).add ((hasDerivAt_id t).mul_const v.2)).prodMk
    (hasDerivAt_const t v.2)

theorem zero_ode (t : ℝ) (v : E) : HasDerivAt (fun _ : ℝ => v) (0 : E) t :=
  hasDerivAt_const t v

/-- Both constant coefficients are one-periodic. -/
theorem coefficients_periodic :
    Function.Periodic (fun _ : ℝ => N) 1 ∧
    Function.Periodic (fun _ : ℝ => (0 : E →L[ℝ] E)) 1 := by
  constructor <;> intro t <;> rfl

/-- For complex eigenvectors, the nilpotent Floquet matrix has only eigenvalue zero. -/
theorem nilpotent_eigenvalues (mu : ℂ) (v : ℂ × ℂ) (hv : v ≠ 0)
    (he : (v.2, (0 : ℂ)) = mu • v) : mu = 0 := by
  by_contra hl
  have h2 : mu * v.2 = 0 := by simpa using (congrArg Prod.snd he).symm
  have hv2 : v.2 = 0 := (mul_eq_zero.mp h2).resolve_left hl
  have h1 : mu * v.1 = 0 := by simpa [hv2] using (congrArg Prod.fst he).symm
  have hv1 : v.1 = 0 := (mul_eq_zero.mp h1).resolve_left hl
  exact hv (Prod.ext hv1 hv2)

theorem zero_eigenvalues (mu : ℂ) (v : ℂ × ℂ) (hv : v ≠ 0)
    (he : (0 : ℂ × ℂ) = mu • v) : mu = 0 := by
  by_contra hl
  have hv1 : v.1 = 0 := (mul_eq_zero.mp (by simpa using (congrArg Prod.fst he).symm)).resolve_left hl
  have hv2 : v.2 = 0 := (mul_eq_zero.mp (by simpa using (congrArg Prod.snd he).symm)).resolve_left hl
  exact hv (Prod.ext hv1 hv2)

theorem eigenvalue_zero_exists :
    ((1 : ℂ), (0 : ℂ)) ≠ 0 ∧
      ((0 : ℂ), (0 : ℂ)) = (0 : ℂ) • ((1 : ℂ), (0 : ℂ)) := by
  simp

/-- Lyapunov stability of the zero solution, for forward time. -/
def Stable (flow : ℝ → E → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ v : E, ‖v‖ < δ → ∀ t : ℝ, 0 ≤ t → ‖flow t v‖ < ε

theorem zero_stable : Stable (fun _ v => v) := by
  intro ε hε
  exact ⟨ε, hε, fun v hv _ _ => hv⟩

theorem nilpotent_unstable : ¬ Stable (fun t v => fundamental t v) := by
  intro hs
  obtain ⟨δ, hδ, hsmall⟩ := hs 1 (by norm_num)
  have hv : ‖((0 : ℝ), δ/2)‖ < δ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_zero,
      abs_of_pos (by positivity : 0 < δ/2), max_eq_right (by positivity)]
    linarith
  have ht : 0 ≤ 2/δ := by positivity
  have hbad := hsmall (0, δ/2) hv (2/δ) ht
  have hfirst : 2/δ * (δ/2) = 1 := by field_simp <;> ring
  have hnorm : 1 ≤ ‖fundamental (2/δ) (0, δ/2)‖ := by
    simp only [fundamental_apply, zero_add, hfirst, Prod.norm_def, Real.norm_eq_abs,
      abs_one]
    exact le_max_left _ _
  linarith

/-- Equal (zero) exponent real-part signs coexist with opposite stability behavior. -/
theorem stability_not_determined :
    Stable (fun _ v => v) ∧ ¬ Stable (fun t v => fundamental t v) :=
  ⟨zero_stable, nilpotent_unstable⟩
end FloquetJordan
#print axioms FloquetJordan.exponential
#print axioms FloquetJordan.fundamental_ode
#print axioms FloquetJordan.fundamental_inverse
#print axioms FloquetJordan.nilpotent_eigenvalues
#print axioms FloquetJordan.zero_eigenvalues
#print axioms FloquetJordan.stability_not_determined
