import Mathlib

/-!
# Conjecture 00000000982: fixed points of the Berezin transform on Fock space

Conjecture: the fixed points of the Berezin transform on Fock space are radial functions, and the
fixed-point set has cardinality at most 2.

We define the Fock space `F²` (entire functions square-integrable against the Gaussian measure
`dλ(w) = π⁻¹ e^{-|w|²} dA(w)`), its normalized reproducing kernel
`k_z(w) = e^{w z̄ - |z|²/2}`, and the Berezin transform of a symbol
`(B f)(z) = ∫ f(w) |k_z(w)|² dλ(w)` (the value `⟨T_f k_z, k_z⟩` of the Toeplitz operator).
We prove that `B` is the Gaussian convolution `(B f)(z) = π⁻¹ ∫ f(z+u) e^{-|u|²} dA(u)`, that it
fixes every constant and every monomial `w ↦ w^k`, that `w ↦ w` is not radial, and that the
fixed-point set is infinite even among bounded symbols.
-/

open MeasureTheory Complex

namespace C982

noncomputable section

/-- Density of the Gaussian measure `dλ(w) = π⁻¹ e^{-|w|²} dA(w)` w.r.t. Lebesgue measure on `ℂ`. -/
def gaussDensity (w : ℂ) : ℝ := Real.pi⁻¹ * Real.exp (-‖w‖ ^ 2)

/-- Membership in the Fock space `F²`: `f` is entire and `∫ |f|² dλ < ∞`. -/
def InFock (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ Integrable (fun w => ‖f w‖ ^ 2 * gaussDensity w)

/-- The reproducing kernel `K(w, z) = e^{w z̄}` of `F²`. -/
def fockKernel (z w : ℂ) : ℂ := cexp (w * (starRingEnd ℂ) z)

/-- The normalized reproducing kernel `k_z(w) = e^{w z̄ - |z|²/2}`. -/
def normKernel (z w : ℂ) : ℂ := cexp (w * (starRingEnd ℂ) z - ((‖z‖ ^ 2 / 2 : ℝ) : ℂ))

/-- The Berezin transform of a symbol `f`: `(B f)(z) = ∫ f(w) |k_z(w)|² dλ(w)`. -/
def berezin (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w, f w * ((‖normKernel z w‖ ^ 2 * gaussDensity w : ℝ) : ℂ)

/-- A function on `ℂ` is radial if it depends only on `|z|`. -/
def IsRadial (f : ℂ → ℂ) : Prop := ∀ z w : ℂ, ‖z‖ = ‖w‖ → f z = f w

/-- Fixed points of the Berezin transform in `F²`. -/
def fockFixed : Set (ℂ → ℂ) := {f | InFock f ∧ berezin f = f}

/-- Fixed points of the Berezin transform among bounded symbols. -/
def boundedFixed : Set (ℂ → ℂ) := {f | (∃ C, ∀ z, ‖f z‖ ≤ C) ∧ berezin f = f}

/-- The Gaussian `G(u) = π⁻¹ e^{-|u|²}` as a complex-valued function. -/
def G (u : ℂ) : ℂ := ((Real.pi⁻¹ * Real.exp (-‖u‖ ^ 2) : ℝ) : ℂ)

/-! ### The kernel and the convolution form -/

/-- `k_z = K(·, z) / √K(z, z)`, with `K(z, z) = e^{|z|²}`. -/
theorem normKernel_eq (z w : ℂ) :
    normKernel z w = fockKernel z w * ((Real.exp (-(‖z‖ ^ 2 / 2)) : ℝ) : ℂ) := by
  rw [normKernel, fockKernel, ofReal_exp, sub_eq_add_neg, Complex.exp_add, ofReal_neg]

theorem kernel_weight (z w : ℂ) :
    ‖normKernel z w‖ ^ 2 * gaussDensity w = Real.pi⁻¹ * Real.exp (-‖w - z‖ ^ 2) := by
  rw [normKernel, Complex.norm_exp, gaussDensity, ← Real.exp_nat_mul]
  have h1 : ‖w - z‖ ^ 2 = ‖w‖ ^ 2 + ‖z‖ ^ 2 - 2 * (w * (starRingEnd ℂ) z).re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  rw [h1, mul_left_comm, ← Real.exp_add]
  congr 2
  simp only [sub_re, ofReal_re]
  push_cast
  ring

theorem berezin_eq_conv (f : ℂ → ℂ) (z : ℂ) : berezin f z = ∫ u, f (z + u) * G u := by
  have h : ∀ w, f w * ((‖normKernel z w‖ ^ 2 * gaussDensity w : ℝ) : ℂ)
      = (fun u => f (z + u) * G u) (w - z) := by
    intro w
    simp only [kernel_weight, G, add_sub_cancel]
  simp_rw [berezin, h]
  exact integral_sub_right_eq_self (fun u => f (z + u) * G u) z

/-! ### Gaussian integrals -/

theorem integrable_gauss {b : ℝ} (hb : 0 < b) :
    Integrable (fun u : ℂ => Real.exp (-b * ‖u‖ ^ 2)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (b : ℂ))
    (by simpa using hb) 0 0).norm
  refine this.congr (ae_of_all _ fun u => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  rw [← ofReal_pow, ← ofReal_neg, ← ofReal_mul, ofReal_re]

theorem gauss_mass : ∫ u : ℂ, Real.exp (-‖u‖ ^ 2) = Real.pi := by
  have := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (b := 1) one_pos
  simp only [neg_mul, one_mul, div_one, Complex.finrank_real_complex] at this
  rw [this]
  norm_num

theorem integral_G : ∫ u, G u = 1 := by
  unfold G
  rw [integral_complex_ofReal, integral_const_mul, gauss_mass]
  simp [Real.pi_ne_zero]

/-- Polynomial moments of the Gaussian are integrable. -/
theorem integrable_moment (k : ℕ) :
    Integrable (fun u : ℂ => ‖u‖ ^ k * Real.exp (-‖u‖ ^ 2)) := by
  refine ((integrable_gauss (b := 1 / 2) (by norm_num)).const_mul
    (k.factorial * Real.exp (1 / 2))).mono' (by fun_prop) (ae_of_all _ fun u => ?_)
  have hx := norm_nonneg u
  have h1 : ‖u‖ ^ k ≤ k.factorial * Real.exp ‖u‖ := by
    have := Real.pow_div_factorial_le_exp ‖u‖ hx k
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have h2 : Real.exp ‖u‖ * Real.exp (-‖u‖ ^ 2)
      ≤ Real.exp (1 / 2) * Real.exp (-(1 / 2) * ‖u‖ ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (‖u‖ - 1)])
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖u‖ ^ k * Real.exp (-‖u‖ ^ 2)
      ≤ k.factorial * Real.exp ‖u‖ * Real.exp (-‖u‖ ^ 2) := by gcongr
    _ = k.factorial * (Real.exp ‖u‖ * Real.exp (-‖u‖ ^ 2)) := by ring
    _ ≤ k.factorial * (Real.exp (1 / 2) * Real.exp (-(1 / 2) * ‖u‖ ^ 2)) := by gcongr
    _ = _ := by ring

theorem integrable_pow_G (j : ℕ) : Integrable (fun u : ℂ => u ^ j * G u) := by
  refine ((integrable_moment j).const_mul Real.pi⁻¹).mono' (by unfold G; fun_prop)
    (ae_of_all _ fun u => ?_)
  rw [norm_mul, norm_pow, G, norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact le_of_eq (by ring)

/-- Odd/rotational symmetry: `∫ u^j G(u) dA(u) = 0` for `j ≥ 1` (rotate by `e^{iπ/j}`). -/
theorem moment_zero {j : ℕ} (hj : 0 < j) : ∫ u, u ^ j * G u = 0 := by
  set ω : Circle := Circle.exp (Real.pi / j)
  have hω : (ω : ℂ) ^ j = -1 := by
    have hj' : (j : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
    have e : (j : ℂ) * (((Real.pi / j : ℝ) : ℂ) * I) = Real.pi * I := by
      push_cast; field_simp
    rw [Circle.coe_exp, ← Complex.exp_nat_mul, e, Complex.exp_pi_mul_I]
  have hrot := (LinearIsometryEquiv.measurePreserving (rotation ω)).integral_comp
    (rotation ω).toHomeomorph.measurableEmbedding (fun u => u ^ j * G u)
  have hG : ∀ u, G ((ω : ℂ) * u) = G u := by
    intro u; simp [G, Circle.norm_coe]
  simp only [rotation_apply, hG, mul_pow, hω, neg_mul, one_mul, integral_neg] at hrot
  have : (2 : ℂ) * ∫ u, u ^ j * G u = 0 := by linear_combination -hrot
  simpa using this

/-! ### Fixed points -/

theorem berezin_const (c : ℂ) : berezin (fun _ => c) = fun _ => c := by
  funext z
  rw [berezin_eq_conv, integral_const_mul, integral_G, mul_one]

theorem berezin_pow (k : ℕ) : berezin (fun w => w ^ k) = fun w => w ^ k := by
  funext z
  rw [berezin_eq_conv]
  simp_rw [add_pow, Finset.sum_mul]
  rw [integral_finsetSum _ (fun m _ =>
    ((integrable_pow_G (k - m)).const_mul (z ^ m * (k.choose m : ℂ))).congr
      (ae_of_all _ fun u => by ring))]
  rw [Finset.sum_eq_single k]
  · simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
    rw [integral_const_mul, integral_G, mul_one]
  · intro m hm hmk
    have hlt : 0 < k - m := by
      have := Finset.mem_range.mp hm; omega
    have : ∀ u : ℂ, z ^ m * u ^ (k - m) * (k.choose m : ℂ) * G u
        = (z ^ m * (k.choose m : ℂ)) * (u ^ (k - m) * G u) := fun u => by ring
    simp_rw [this, integral_const_mul, moment_zero hlt, mul_zero]
  · intro h; exact absurd (Finset.self_mem_range_succ k) h

theorem const_inFock (c : ℂ) : InFock (fun _ => c) := by
  refine ⟨differentiable_const c, ?_⟩
  refine ((integrable_moment 0).const_mul (‖c‖ ^ 2 * Real.pi⁻¹)).congr (ae_of_all _ fun u => ?_)
  simp only [gaussDensity, pow_zero, one_mul]
  ring

theorem pow_inFock (k : ℕ) : InFock (fun w : ℂ => w ^ k) := by
  refine ⟨differentiable_pow k, ?_⟩
  refine ((integrable_moment (2 * k)).const_mul Real.pi⁻¹).congr (ae_of_all _ fun u => ?_)
  simp only [gaussDensity, norm_pow]
  ring

theorem id_not_radial : ¬ IsRadial (fun w : ℂ => w) := by
  intro h
  have := h 1 I (by simp)
  exact one_ne_I this
where one_ne_I : (1 : ℂ) ≠ I := fun h => by simpa using congrArg Complex.im h

theorem pow_mem_fockFixed (k : ℕ) : (fun w : ℂ => w ^ k) ∈ fockFixed :=
  ⟨pow_inFock k, berezin_pow k⟩

theorem const_mem (c : ℂ) : (fun _ : ℂ => c) ∈ fockFixed ∩ boundedFixed :=
  ⟨⟨const_inFock c, berezin_const c⟩, ⟨⟨‖c‖, fun _ => le_rfl⟩, berezin_const c⟩⟩

/-- Every constant is a fixed point, so the fixed-point set is infinite, both in `F²` and among
bounded symbols. -/
theorem fixed_infinite : (fockFixed ∩ boundedFixed).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun c : ℂ => fun _ : ℂ => c) ?_ const_mem
  intro a b h
  simpa using congrFun h 0

/-- The monomials `w ↦ w^k` (all fixed by `B`) are linearly independent. -/
theorem monomials_linearIndependent : LinearIndependent ℂ (fun k : ℕ => fun w : ℂ => w ^ k) := by
  let L : Polynomial ℂ →ₗ[ℂ] (ℂ → ℂ) := LinearMap.pi fun z => Polynomial.leval z
  have hL : Function.Injective L := by
    intro p q h
    exact Polynomial.funext fun z => congrFun h z
  have := (Polynomial.basisMonomials ℂ).linearIndependent.map' L (LinearMap.ker_eq_bot.mpr hL)
  have e : (⇑L ∘ ⇑(Polynomial.basisMonomials ℂ)) = fun k : ℕ => fun w : ℂ => w ^ k := by
    funext k w
    simp [L, Polynomial.coe_basisMonomials]
  rw [e] at this
  exact this

/-- **Main theorem.** The conjecture fails: `w ↦ w` is a non-radial fixed point in `F²`, every
monomial and every constant is fixed, and the fixed-point set is infinite (already among bounded
symbols, where all fixed points found are constants). -/
theorem conjecture_982_false :
    ((fun w : ℂ => w) ∈ fockFixed ∧ ¬ IsRadial (fun w : ℂ => w)) ∧
    (∀ k : ℕ, (fun w : ℂ => w ^ k) ∈ fockFixed) ∧
    LinearIndependent ℂ (fun k : ℕ => fun w : ℂ => w ^ k) ∧
    fockFixed.Infinite ∧ boundedFixed.Infinite ∧
    ¬ ((∀ f ∈ fockFixed, IsRadial f) ∧ fockFixed.encard ≤ 2) ∧
    ¬ (boundedFixed.encard ≤ 2) := by
  have hid : (fun w : ℂ => w) ∈ fockFixed := by
    simpa using pow_mem_fockFixed 1
  have hF : fockFixed.Infinite := fixed_infinite.mono Set.inter_subset_left
  have hB : boundedFixed.Infinite := fixed_infinite.mono Set.inter_subset_right
  refine ⟨⟨hid, id_not_radial⟩, pow_mem_fockFixed, monomials_linearIndependent, hF, hB,
    fun h => id_not_radial (h.1 _ hid), fun h => ?_⟩
  exact hB (Set.finite_of_encard_le_coe h)

end

end C982
