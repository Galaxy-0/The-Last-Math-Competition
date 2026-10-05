import Mathlib

/-!
# Conjecture 00000007000: same box norms, different scattering spectra

Conjecture 00000007000 reads:

> Definition: Box norms and scattering spectra are two layers. Conjecture: There exist two
> functions with identical box norms but different scattering spectra, and the separation is
> realized by an explicit permutation pair with the same norms but different phase.

Reading. The functions are real functions `f : X × Y → ℝ` on a finite grid. The (Gowers) box norm
is `‖f‖_□ = (E_{x,x',y,y'} f(x,y) f(x,y') f(x',y) f(x',y'))^{1/4}`. A *permutation pair* is a pair
`(σ, τ)` of permutations of `X` and of `Y`, acting by `f ↦ f ∘ (σ × τ)`; it preserves the box norm
of every function (`boxNorm_permute`). On the grid `ZMod 4 × ZMod 4` the Fourier transform is
`f̂(ξ) = ∑_{x,y} f(x,y) e^{-2πi(ξ₁x + ξ₂y)/4}`, the *scattering spectrum* is the diffraction
intensity `I_f(ξ) = |f̂(ξ)|²` (the structure factor), and the *phase* is `f̂(ξ)/|f̂(ξ)|`.

Main result (`conjecture7000`). For `f = 1_{x ∈ {0,1}} · 1_{y = 0}` and the permutation pair
`σ = (1 2)`, `τ = (0 1)`, the function `g = f ∘ (σ × τ) = 1_{x ∈ {0,2}} · 1_{y = 1}` has

* the same box norm as `f` (and `‖f‖_□ > 0`, so this is not a degenerate equality);
* a different scattering spectrum: `I_f(1,0) = 2` but `I_g(1,0) = 0`;
* a different phase at a frequency with the same intensity: `f̂(0,1) = 2` and `ĝ(0,1) = -2i`,
  both of intensity 4.

Convention: `Complex.I ^ k` is used for `e^{2πik/4}`; `exp_eq` proves the identity.
-/

namespace Submission00000007000

open Complex Finset

section General

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- The box-norm sum `∑_{x,x',y,y'} f(x,y) f(x,y') f(x',y) f(x',y')`. -/
def boxSum (f : X × Y → ℝ) : ℝ :=
  ∑ q : X × X × Y × Y,
    f (q.1, q.2.2.1) * f (q.1, q.2.2.2) * f (q.2.1, q.2.2.1) * f (q.2.1, q.2.2.2)

/-- The box-norm sum is a sum of squares, hence nonnegative. -/
lemma boxSum_eq_sq (f : X × Y → ℝ) :
    boxSum f = ∑ x : X, ∑ x' : X, (∑ y : Y, f (x, y) * f (x', y)) ^ 2 := by
  unfold boxSum
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Fintype.sum_prod_type, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
  ring

lemma boxSum_nonneg (f : X × Y → ℝ) : 0 ≤ boxSum f := by
  rw [boxSum_eq_sq]; positivity

/-- The Gowers box norm `‖f‖_□`. -/
noncomputable def boxNorm (f : X × Y → ℝ) : ℝ :=
  (boxSum f / ((Fintype.card X : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2)) ^ (1 / 4 : ℝ)

/-- The action of a permutation pair `(σ, τ)`. -/
def permute (σ : Equiv.Perm X) (τ : Equiv.Perm Y) (f : X × Y → ℝ) : X × Y → ℝ :=
  fun p => f (σ p.1, τ p.2)

/-- Every permutation pair preserves the box-norm sum. -/
theorem boxSum_permute (σ : Equiv.Perm X) (τ : Equiv.Perm Y) (f : X × Y → ℝ) :
    boxSum (permute σ τ f) = boxSum f := by
  unfold boxSum permute
  exact Fintype.sum_equiv (σ.prodCongr (σ.prodCongr (τ.prodCongr τ))) _ _ (fun _ => rfl)

/-- Every permutation pair preserves the box norm. -/
theorem boxNorm_permute (σ : Equiv.Perm X) (τ : Equiv.Perm Y) (f : X × Y → ℝ) :
    boxNorm (permute σ τ f) = boxNorm f := by
  unfold boxNorm; rw [boxSum_permute]

end General

/-! ## Fourier transform on `ZMod 4 × ZMod 4` -/

abbrev G := ZMod 4 × ZMod 4

/-- The character `k ↦ e^{2πik/4} = i^k`. -/
noncomputable def e4 (k : ZMod 4) : ℂ := I ^ k.val

lemma exp_eq (k : ZMod 4) : e4 k = Complex.exp (2 * Real.pi * I * (k.val : ℂ) / 4) := by
  rw [e4, show (2 * Real.pi * I * (k.val : ℂ) / 4 : ℂ) = (k.val : ℕ) * (Real.pi / 2 * I) by ring,
    Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]

/-- Fourier transform `f̂(ξ) = ∑ f(x,y) e^{-2πi(ξ₁x+ξ₂y)/4}`. -/
noncomputable def fourier (f : G → ℝ) (ξ : G) : ℂ :=
  ∑ p : G, (f p : ℂ) * e4 (-(ξ.1 * p.1 + ξ.2 * p.2))

/-- The scattering spectrum (diffraction intensity) `I_f(ξ) = |f̂(ξ)|²`. -/
noncomputable def intensity (f : G → ℝ) (ξ : G) : ℝ := Complex.normSq (fourier f ξ)

/-! ## The explicit pair -/

/-- `f = 1_{x ∈ {0,1}} · 1_{y = 0}`. -/
def f : G → ℝ := fun p => if (p.1 = 0 ∨ p.1 = 1) ∧ p.2 = 0 then 1 else 0

/-- `σ = (1 2)` on the first coordinate. -/
def σ : Equiv.Perm (ZMod 4) := Equiv.swap 1 2

/-- `τ = (0 1)` on the second coordinate. -/
def τ : Equiv.Perm (ZMod 4) := Equiv.swap 0 1

/-- `g = f ∘ (σ × τ)`. -/
def g : G → ℝ := permute σ τ f

lemma g_eq : g = fun p => if (p.1 = 0 ∨ p.1 = 2) ∧ p.2 = 1 then 1 else 0 := by
  have h : ∀ x y : ZMod 4, (((σ x = 0 ∨ σ x = 1) ∧ τ y = 0) ↔ ((x = 0 ∨ x = 2) ∧ y = 1)) := by
    decide
  funext p
  simp only [g, permute, f, h]


lemma e4_val (k : ZMod 4) :
    e4 k = if k = 0 then 1 else if k = 1 then I else if k = 2 then -1 else -I := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by revert k; decide
  rcases hk with rfl | rfl | rfl | rfl
  · rw [e4, show (0 : ZMod 4).val = 0 from rfl]; simp
  · rw [e4, show (1 : ZMod 4).val = 1 from rfl]; simp (config := { decide := true })
  · rw [e4, show (2 : ZMod 4).val = 2 from rfl]; simp (config := { decide := true })
  · rw [e4, show (3 : ZMod 4).val = 3 from rfl, pow_succ, I_sq]
    simp (config := { decide := true })

lemma sum_zmod4 {M : Type} [AddCommMonoid M] (F : ZMod 4 → M) : ∑ x : ZMod 4, F x = F 0 + F 1 + F 2 + F 3 :=
  Fin.sum_univ_four F

lemma fourier_f_10 : fourier f (1, 0) = 1 - I := by
  rw [fourier, Fintype.sum_prod_type]
  simp (config := { decide := true }) [sum_zmod4, f, e4_val]
  ring

lemma fourier_g_10 : fourier g (1, 0) = 0 := by
  rw [fourier, g_eq, Fintype.sum_prod_type]
  simp (config := { decide := true }) [sum_zmod4, e4_val]

lemma fourier_f_01 : fourier f (0, 1) = 2 := by
  rw [fourier, Fintype.sum_prod_type]
  simp (config := { decide := true }) [sum_zmod4, f, e4_val]
  ring

lemma fourier_g_01 : fourier g (0, 1) = -2 * I := by
  rw [fourier, g_eq, Fintype.sum_prod_type]
  simp (config := { decide := true }) [sum_zmod4, e4_val]
  ring

/-- The phase `f̂(ξ)/|f̂(ξ)|` of the Fourier coefficient. -/
noncomputable def phase (f : G → ℝ) (ξ : G) : ℂ := fourier f ξ / (‖fourier f ξ‖ : ℂ)

lemma phase_f_01 : phase f (0, 1) = 1 := by
  rw [phase, fourier_f_01]
  norm_num

lemma phase_g_01 : phase g (0, 1) = -I := by
  rw [phase, fourier_g_01]
  have : ‖(-2 * I : ℂ)‖ = 2 := by simp
  rw [this]
  push_cast
  ring

lemma boxSum_f : boxSum f = 4 := by
  rw [boxSum_eq_sq]
  simp (config := { decide := true }) [sum_zmod4, f]
  norm_num

/-- **Conjecture 00000007000 (Gowers box norm / diffraction-intensity reading).** The function
`f` and its image `g` under the explicit permutation pair `(σ, τ) = ((1 2), (0 1))` have the same
(positive) box norm, but different scattering spectra; at the frequency `(0,1)` their
intensities agree and their phases differ. -/
theorem conjecture7000 :
    ∃ (f g : G → ℝ) (σ τ : Equiv.Perm (ZMod 4)),
      σ ≠ 1 ∧ τ ≠ 1 ∧ g = permute σ τ f ∧
      boxNorm g = boxNorm f ∧ 0 < boxNorm f ∧
      intensity f ≠ intensity g ∧ intensity f (1, 0) = 2 ∧ intensity g (1, 0) = 0 ∧
      intensity f (0, 1) = intensity g (0, 1) ∧ phase f (0, 1) ≠ phase g (0, 1) := by
  have hI10f : intensity f (1, 0) = 2 := by
    rw [intensity, fourier_f_10, Complex.normSq_apply]; simp; norm_num
  have hI10g : intensity g (1, 0) = 0 := by
    rw [intensity, fourier_g_10]; simp
  refine ⟨f, g, σ, τ, ?_, ?_, rfl, boxNorm_permute σ τ f, ?_, ?_, hI10f, hI10g, ?_, ?_⟩
  · intro h
    have := congrArg (fun e : Equiv.Perm (ZMod 4) => e 1) h
    simp [σ] at this
    exact absurd this (by decide)
  · intro h
    have := congrArg (fun e : Equiv.Perm (ZMod 4) => e 0) h
    simp [τ] at this
    exact absurd this (by decide)
  · unfold boxNorm
    rw [boxSum_f]
    apply Real.rpow_pos_of_pos
    simp
  · intro h
    have := congrFun h (1, 0)
    rw [hI10f, hI10g] at this
    norm_num at this
  · rw [intensity, intensity, fourier_f_01, fourier_g_01, Complex.normSq_apply,
      Complex.normSq_apply]
    simp
  · rw [phase_f_01, phase_g_01]
    intro h
    have := congrArg Complex.re h
    simp at this

end Submission00000007000
