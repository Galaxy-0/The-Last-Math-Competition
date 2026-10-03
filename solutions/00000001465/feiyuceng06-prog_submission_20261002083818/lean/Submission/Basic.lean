import Mathlib

/-!
# Conjecture 00000001465 is false

The Moreau envelope of `f` with parameter `λ > 0` is
`M_λ f (x) = inf_y (f y + ‖x - y‖² / (2λ))`. Conjecture 00000001465 asserts, among
other things, that for `λ` above a critical value there is a convex `f` whose
envelope is *not differentiable at a minimizer*.

No such `f` exists, convex or not. Let `x*` minimize `M = M_λ f`. Taking `y = x` in
the infimum gives `M ≤ f`, so `f y ≥ M x*` for all `y`. Using
`‖x - y‖² ≤ 2‖x - x*‖² + 2‖x* - y‖²`, for every `y`,

  `M x ≤ f y + ‖x - y‖²/(2λ) ≤ 2 (f y + ‖x* - y‖²/(2λ)) - M x* + ‖x - x*‖²/λ`,

and taking the infimum over `y` gives `M x ≤ M x* + ‖x - x*‖²/λ`. Together with
`M x ≥ M x*`, this shows that `M` is differentiable at `x*` with derivative `0`.
-/

namespace Submission00000001465

open Filter Topology Asymptotics

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `M` is the Moreau envelope of `f` with parameter `lam`: for every `x`,
`M x = inf_y (f y + ‖x - y‖² / (2 lam))`, the infimum (greatest lower bound) being a
real number. -/
def IsMoreauEnvelope (f : E → ℝ) (lam : ℝ) (M : E → ℝ) : Prop :=
  ∀ x, IsGLB (Set.range fun y => f y + ‖x - y‖ ^ 2 / (2 * lam)) (M x)

omit [NormedSpace ℝ E] in
/-- The Moreau envelope lies below `f`. -/
theorem le_self_of_isMoreauEnvelope {f : E → ℝ} {lam : ℝ} {M : E → ℝ}
    (hM : IsMoreauEnvelope f lam M) (x : E) : M x ≤ f x := by
  have := (hM x).1 ⟨x, rfl⟩
  simpa using this

omit [NormedSpace ℝ E] in
/-- Quadratic growth bound at a minimizer: `M x ≤ M x* + ‖x - x*‖² / lam`. -/
theorem le_of_isMin {f : E → ℝ} {lam : ℝ} {M : E → ℝ} (hlam : 0 < lam)
    (hM : IsMoreauEnvelope f lam M) {xs : E} (hmin : ∀ x, M xs ≤ M x) (x : E) :
    M x ≤ M xs + ‖x - xs‖ ^ 2 / lam := by
  have hfge : ∀ y, M xs ≤ f y := fun y => (hmin y).trans (le_self_of_isMoreauEnvelope hM y)
  -- `(M x + M xs - ‖x - xs‖²/lam) / 2` is a lower bound of the family defining `M xs`.
  have hlow : (M x + M xs - ‖x - xs‖ ^ 2 / lam) / 2 ∈
      lowerBounds (Set.range fun y => f y + ‖xs - y‖ ^ 2 / (2 * lam)) := by
    rintro _ ⟨y, rfl⟩
    have h1 : M x ≤ f y + ‖x - y‖ ^ 2 / (2 * lam) := (hM x).1 ⟨y, rfl⟩
    have htri : ‖x - y‖ ≤ ‖x - xs‖ + ‖xs - y‖ := by
      calc ‖x - y‖ = ‖(x - xs) + (xs - y)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖x - xs‖ + ‖xs - y‖ := norm_add_le _ _
    have hsq : ‖x - y‖ ^ 2 ≤ 2 * ‖x - xs‖ ^ 2 + 2 * ‖xs - y‖ ^ 2 := by
      nlinarith [norm_nonneg (x - y), norm_nonneg (x - xs), norm_nonneg (xs - y),
        sq_nonneg (‖x - xs‖ - ‖xs - y‖)]
    have h2 : ‖x - y‖ ^ 2 / (2 * lam) ≤ ‖x - xs‖ ^ 2 / lam + ‖xs - y‖ ^ 2 / lam := by
      rw [show ‖x - xs‖ ^ 2 / lam + ‖xs - y‖ ^ 2 / lam =
          (2 * ‖x - xs‖ ^ 2 + 2 * ‖xs - y‖ ^ 2) / (2 * lam) by field_simp]
      gcongr
    have h3 := hfge y
    have h4 : ‖xs - y‖ ^ 2 / lam = 2 * (‖xs - y‖ ^ 2 / (2 * lam)) := by
      field_simp
    simp only
    linarith
  have := (hM xs).2 hlow
  linarith

/-- The Moreau envelope is differentiable, with derivative `0`, at each of its
minimizers. -/
theorem hasFDerivAt_of_isMin {f : E → ℝ} {lam : ℝ} {M : E → ℝ} (hlam : 0 < lam)
    (hM : IsMoreauEnvelope f lam M) {xs : E} (hmin : ∀ x, M xs ≤ M x) :
    HasFDerivAt M (0 : E →L[ℝ] ℝ) xs := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [isLittleO_iff]
  intro c hc
  have hball : ∀ᶠ h : E in 𝓝 0, ‖h‖ ≤ c * lam :=
    eventually_norm_sub_lt 0 (by positivity : 0 < c * lam) |>.mono fun h hh => by
      simpa using hh.le
  filter_upwards [hball] with h hh
  have hup := le_of_isMin hlam hM hmin (xs + h)
  have hlo := hmin (xs + h)
  simp only [add_sub_cancel_left] at hup
  show ‖M (xs + h) - M xs - 0‖ ≤ c * ‖h‖
  rw [sub_zero]
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have : ‖h‖ ^ 2 / lam ≤ c * ‖h‖ := by
    rw [div_le_iff₀ hlam]
    nlinarith [norm_nonneg h]
  linarith

end General

/-! ## The conjecture -/

/-- The minimal Lipschitz constant of `f`. -/
noncomputable def lipConst {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  sInf {K : ℝ | 0 ≤ K ∧ ∀ x y, |f x - f y| ≤ K * ‖x - y‖}

/-- Conjecture 00000001465 on `ℝⁿ`. With `λ* = 1 / L(f)`:
(1) for `0 < λ < λ*`, the Moreau envelope of every convex `f` is `C¹`;
(2) for `λ > λ*` there is a convex `f` whose envelope is not differentiable at a
minimizer. -/
def ConjectureHolds : Prop :=
  (∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (lam : ℝ) (M : EuclideanSpace ℝ (Fin n) → ℝ),
      ConvexOn ℝ Set.univ f → 0 < lam → lam < 1 / lipConst f →
        IsMoreauEnvelope f lam M → ContDiff ℝ 1 M) ∧
  (∃ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (lam : ℝ) (M : EuclideanSpace ℝ (Fin n) → ℝ)
      (xs : EuclideanSpace ℝ (Fin n)),
      ConvexOn ℝ Set.univ f ∧ 0 < lam ∧ 1 / lipConst f < lam ∧ IsMoreauEnvelope f lam M ∧
        (∀ x, M xs ≤ M x) ∧ ¬ DifferentiableAt ℝ M xs)

/-- Conjecture 00000001465 is false: its second clause fails, since every Moreau
envelope is differentiable at its minimizers. -/
theorem conjecture_00000001465_false : ¬ ConjectureHolds := by
  rintro ⟨-, n, f, lam, M, xs, -, hlam, -, hM, hmin, hnd⟩
  exact hnd (hasFDerivAt_of_isMin hlam hM hmin).differentiableAt

end Submission00000001465

#print axioms Submission00000001465.conjecture_00000001465_false
