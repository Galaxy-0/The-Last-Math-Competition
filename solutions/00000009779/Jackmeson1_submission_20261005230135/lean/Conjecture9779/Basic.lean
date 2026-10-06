import Mathlib

/-!
# Conjecture 00000009779: the decay clause is false

The conjecture claims that the eigenvalues of the integral operator of a `C^k` kernel on a
`d`-dimensional domain satisfy `|λ_n| ≤ C n^(-k-1-d/2)`.

For every dimension `D = d + 1 ≥ 1` and every `k ≥ 0` we build a real, symmetric, positive
semidefinite kernel `K` on the cube `[0,1]^D` with `K` of class `C^k` on `ℝ^D × ℝ^D`, and show
that no constant `C` works (in the eigenfunction form `EigenBound`).  With `s = k + 5/4`,

  `K(x, y) = f_s(x₀ - y₀)`,   `f_s(t) = ∑_{m ≥ 1} m^(-s) cos(2π m t)`.

The functions `φ_m(x) = exp(2π i m x₀)` (`m ≥ 1`) are orthonormal in `L²([0,1]^D)` and satisfy
`T_K φ_m = (1/2) m^(-s) φ_m` everywhere on the cube.  So for every `n` there are `n` orthonormal
eigenfunctions with eigenvalues `≥ (1/2) n^(-s)`, and `(1/2) n^(-s) > C n^(-k-1-D/2)` for large `n`.
-/

open MeasureTheory Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace C9779

/-! ## The objects of the conjecture -/

/-- The unit cube `[0,1]^D` in `ℝ^D`. -/
def cube (D : ℕ) : Set (Fin D → ℝ) := Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1

/-- The integral operator of the kernel `K` on `L²([0,1]^D)`:
`(T_K φ)(x) = ∫_{[0,1]^D} K(x,y) φ(y) dy`. -/
def intOp {D : ℕ} (K : (Fin D → ℝ) → (Fin D → ℝ) → ℝ) (φ : (Fin D → ℝ) → ℂ)
    (x : Fin D → ℝ) : ℂ :=
  ∫ y in cube D, (K x y : ℂ) * φ y

/-- `φ 0, …, φ (n-1)` are continuous functions, orthonormal in `L²([0,1]^D)`, and eigenfunctions
of `T_K` with eigenvalues `μ 0, …, μ (n-1)` (the eigen-equation holds at every point of the cube). -/
def IsOrthonormalEigenfamily {D n : ℕ} (K : (Fin D → ℝ) → (Fin D → ℝ) → ℝ)
    (φ : Fin n → (Fin D → ℝ) → ℂ) (μ : Fin n → ℂ) : Prop :=
  (∀ i, Continuous (φ i)) ∧
  (∀ i j, ∫ x in cube D, conj (φ i x) * φ j x = if i = j then 1 else 0) ∧
  (∀ i, ∀ x ∈ cube D, intOp K (φ i) x = μ i * φ i x)

/-- The conjectured bound in eigenfunction form: for every `n ≥ 1`, every orthonormal family of
`n` continuous eigenfunctions contains a member whose eigenvalue has absolute value at most
`C n^(-k-1-D/2)`.  If `|λ_1| ≥ |λ_2| ≥ ⋯` are the eigenvalues of `T_K` counted with multiplicity,
then `|λ_n| ≤ C n^(-k-1-D/2)` for all `n ≥ 1` implies this predicate, because `n` orthonormal
eigenfunctions whose eigenvalues all exceed `c` in absolute value force `|λ_n| > c`
(see `proof.tex`). -/
def EigenBound {D : ℕ} (K : (Fin D → ℝ) → (Fin D → ℝ) → ℝ) (k : ℕ) (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (φ : Fin n → (Fin D → ℝ) → ℂ) (μ : Fin n → ℂ),
    IsOrthonormalEigenfamily K φ μ →
      ∃ i, ‖μ i‖ ≤ C * (n : ℝ) ^ (-((k : ℝ) + 1 + (D : ℝ) / 2))

/-- A real kernel is positive semidefinite (Mercer): `∑_{a,b} c_a c_b K(x_a, x_b) ≥ 0`. -/
def PosSemidefKernel {D : ℕ} (K : (Fin D → ℝ) → (Fin D → ℝ) → ℝ) : Prop :=
  ∀ (p : ℕ) (x : Fin p → Fin D → ℝ) (c : Fin p → ℝ), 0 ≤ ∑ a, ∑ b, c a * c b * K (x a) (x b)

/-! ## The one-variable kernel `f_s` -/

/-- The Fourier coefficient `(j+1)^(-s)` (frequency `m = j + 1`). -/
def coef (s : ℝ) (j : ℕ) : ℝ := (((j : ℝ) + 1) ^ s)⁻¹

lemma coef_pos (s : ℝ) (j : ℕ) : 0 < coef s j := by
  unfold coef; positivity

/-- The `j`-th term `t ↦ (j+1)^(-s) cos(2π(j+1)t)`. -/
def term (s : ℝ) (j : ℕ) (t : ℝ) : ℝ := coef s j * Real.cos (2 * Real.pi * ((j : ℝ) + 1) * t)

/-- `f_s(t) = ∑_{m ≥ 1} m^(-s) cos(2π m t)`. -/
def fser (s : ℝ) (t : ℝ) : ℝ := ∑' j : ℕ, term s j t

lemma summable_coef_mul_pow {s : ℝ} (i : ℕ) (hs : (i : ℝ) + 1 < s) :
    Summable fun j : ℕ => coef s j * ((j : ℝ) + 1) ^ i := by
  have h1 : Summable fun j : ℕ => (((j : ℝ)) ^ (s - i))⁻¹ :=
    Real.summable_nat_rpow_inv.2 (by linarith)
  refine ((summable_nat_add_iff 1).2 h1).congr fun j => ?_
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  simp only [coef, Nat.cast_add, Nat.cast_one]
  rw [Real.rpow_sub hj, Real.rpow_natCast, inv_div, div_eq_inv_mul]

lemma summable_coef {s : ℝ} (hs : 1 < s) : Summable (coef s) := by
  simpa using summable_coef_mul_pow (s := s) 0 (by simpa using hs)

lemma abs_term_le (s : ℝ) (j : ℕ) (t : ℝ) : |term s j t| ≤ coef s j := by
  rw [term, abs_mul, abs_of_pos (coef_pos s j)]
  exact mul_le_of_le_one_right (coef_pos s j).le (Real.abs_cos_le_one _)

lemma summable_term {s : ℝ} (hs : 1 < s) (t : ℝ) : Summable fun j => term s j t :=
  (summable_coef hs).of_norm_bounded fun j => by
    simpa [Real.norm_eq_abs] using abs_term_le s j t

lemma norm_iteratedFDeriv_term_le (s : ℝ) (j i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i (term s j) t‖ ≤ (2 * Real.pi) ^ i * (coef s j * ((j : ℝ) + 1) ^ i) := by
  have hω : 0 < 2 * Real.pi * ((j : ℝ) + 1) := by positivity
  have h : iteratedDeriv i (term s j) t = coef s j * ((2 * Real.pi * ((j : ℝ) + 1)) ^ i *
      iteratedDeriv i Real.cos (2 * Real.pi * ((j : ℝ) + 1) * t)) := by
    have e : term s j = fun t => coef s j * Real.cos (2 * Real.pi * ((j : ℝ) + 1) * t) := rfl
    rw [e, iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul Real.contDiff_cos]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, h, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (coef_pos s j), abs_of_pos (pow_pos hω i)]
  have hc := Real.abs_iteratedDeriv_cos_le_one i (2 * Real.pi * ((j : ℝ) + 1) * t)
  calc coef s j * ((2 * Real.pi * ((j : ℝ) + 1)) ^ i *
        |iteratedDeriv i Real.cos (2 * Real.pi * ((j : ℝ) + 1) * t)|)
      ≤ coef s j * ((2 * Real.pi * ((j : ℝ) + 1)) ^ i * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc (pow_pos hω i).le)
          (coef_pos s j).le
    _ = (2 * Real.pi) ^ i * (coef s j * ((j : ℝ) + 1) ^ i) := by rw [mul_pow]; ring

/-- `f_s` is `C^k` as soon as `s > k + 1`. -/
lemma contDiff_fser {k : ℕ} {s : ℝ} (hs : (k : ℝ) + 1 < s) : ContDiff ℝ k (fser s) := by
  have hf : ∀ j, ContDiff ℝ ((k : ℕ∞) : WithTop ℕ∞) (term s j) := fun j =>
    contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
  have hv : ∀ i : ℕ, (i : ℕ∞) ≤ (k : ℕ∞) →
      Summable fun j : ℕ => (2 * Real.pi) ^ i * (coef s j * ((j : ℝ) + 1) ^ i) := by
    intro i hi
    have hi' : (i : ℝ) ≤ k := by exact_mod_cast hi
    exact (summable_coef_mul_pow i (by linarith)).mul_left _
  have := contDiff_tsum (𝕜 := ℝ) (N := (k : ℕ∞)) hf hv
    (fun i j t _ => norm_iteratedFDeriv_term_le s j i t)
  exact_mod_cast this

lemma fser_neg (s t : ℝ) : fser s (-t) = fser s t := by
  simp only [fser, term, mul_neg, Real.cos_neg]

/-! ## Fourier computations on `[0,1]` -/

/-- `e_j(x) = exp(2π i (j+1) x)`. -/
def efun (j : ℕ) (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * I * ((j : ℂ) + 1) * x)

lemma continuous_efun (j : ℕ) : Continuous (efun j) := by
  unfold efun; fun_prop

lemma norm_efun (j : ℕ) (x : ℝ) : ‖efun j x‖ = 1 := by
  rw [efun, show (2 * Real.pi * I * ((j : ℂ) + 1) * x) =
    ((2 * Real.pi * ((j : ℝ) + 1) * x : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma integral_exp_int (p : ℤ) :
    ∫ y in (0:ℝ)..1, Complex.exp (2 * Real.pi * I * p * y) = if p = 0 then 1 else 0 := by
  split_ifs with hp
  · subst hp; simp
  · have hc : (2 * Real.pi * I * p : ℂ) ≠ 0 := by
      have : (p : ℂ) ≠ 0 := by exact_mod_cast hp
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, I_ne_zero, this]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * I * p * ((1:ℝ) : ℂ)) = 1 := by
      rw [show (2 * Real.pi * I * p * ((1:ℝ) : ℂ) : ℂ) = p * (2 * Real.pi * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I p
    rw [h1]; simp

lemma conj_efun_mul (a b : ℕ) (x : ℝ) :
    conj (efun a x) * efun b x = Complex.exp (2 * Real.pi * I * (((b : ℤ) - a : ℤ) : ℂ) * x) := by
  rw [efun, efun, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_add, map_one, map_natCast, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  push_cast; ring

lemma integral_conj_efun_mul (a b : ℕ) :
    ∫ x in (0:ℝ)..1, conj (efun a x) * efun b x = if a = b then 1 else 0 := by
  simp_rw [conj_efun_mul]
  rw [integral_exp_int]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (by omega), if_neg h]

lemma term_mul_efun (s : ℝ) (j j₀ : ℕ) (x y : ℝ) :
    ((term s j (x - y) : ℝ) : ℂ) * efun j₀ y =
      ((coef s j : ℂ) / 2 * Complex.exp (2 * Real.pi * I * ((j : ℂ) + 1) * x)) *
          Complex.exp (2 * Real.pi * I * (((j₀ : ℤ) - j : ℤ) : ℂ) * y) +
        ((coef s j : ℂ) / 2 * Complex.exp (-(2 * Real.pi * I * ((j : ℂ) + 1) * x))) *
          Complex.exp (2 * Real.pi * I * (((j₀ : ℤ) + j + 2 : ℤ) : ℂ) * y) := by
  have hA : Complex.exp (((2 * Real.pi * ((j : ℝ) + 1) * (x - y) : ℝ) : ℂ) * I) * efun j₀ y =
      Complex.exp (2 * Real.pi * I * ((j : ℂ) + 1) * x) *
        Complex.exp (2 * Real.pi * I * (((j₀ : ℤ) - j : ℤ) : ℂ) * y) := by
    rw [efun, ← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have hB : Complex.exp (-((2 * Real.pi * ((j : ℝ) + 1) * (x - y) : ℝ) : ℂ) * I) * efun j₀ y =
      Complex.exp (-(2 * Real.pi * I * ((j : ℂ) + 1) * x)) *
        Complex.exp (2 * Real.pi * I * (((j₀ : ℤ) + j + 2 : ℤ) : ℂ) * y) := by
    rw [efun, ← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [term, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  linear_combination ((coef s j : ℂ) / 2) * hA + ((coef s j : ℂ) / 2) * hB

lemma integral_term_mul_efun (s : ℝ) (j j₀ : ℕ) (x : ℝ) :
    ∫ y in (0:ℝ)..1, ((term s j (x - y) : ℝ) : ℂ) * efun j₀ y =
      if j = j₀ then ((coef s j₀ / 2 : ℝ) : ℂ) * efun j₀ x else 0 := by
  simp_rw [term_mul_efun]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_exp_int, integral_exp_int]
  · have h2 : ((j₀ : ℤ) + j + 2 : ℤ) ≠ 0 := by omega
    rw [if_neg h2, mul_zero, add_zero]
    by_cases h : j = j₀
    · subst h
      rw [if_pos (sub_self _), if_pos rfl, mul_one, efun]
      push_cast; ring
    · have h1 : ((j₀ : ℤ) - j : ℤ) ≠ 0 := by omega
      rw [if_neg h1, if_neg h, mul_zero]
  · exact (by fun_prop : Continuous fun y : ℝ =>
      (coef s j : ℂ) / 2 * Complex.exp (2 * Real.pi * I * ((j : ℂ) + 1) * x) *
        Complex.exp (2 * Real.pi * I * (((j₀ : ℤ) - j : ℤ) : ℂ) * y)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun y : ℝ =>
      (coef s j : ℂ) / 2 * Complex.exp (-(2 * Real.pi * I * ((j : ℂ) + 1) * x)) *
        Complex.exp (2 * Real.pi * I * (((j₀ : ℤ) + j + 2 : ℤ) : ℂ) * y)).intervalIntegrable _ _

lemma continuous_term_mul_efun (s : ℝ) (j j₀ : ℕ) (x : ℝ) :
    Continuous fun y : ℝ => ((term s j (x - y) : ℝ) : ℂ) * efun j₀ y := by
  unfold term efun; fun_prop

/-- The eigen-equation on `[0,1]`: `∫₀¹ f_s(x - y) e_j(y) dy = (1/2)(j+1)^(-s) e_j(x)`. -/
lemma eigen_1d {s : ℝ} (hs : 1 < s) (j₀ : ℕ) (x : ℝ) :
    ∫ y in (0:ℝ)..1, ((fser s (x - y) : ℝ) : ℂ) * efun j₀ y =
      ((coef s j₀ / 2 : ℝ) : ℂ) * efun j₀ x := by
  have hlim : ∀ y : ℝ, HasSum (fun j => ((term s j (x - y) : ℝ) : ℂ) * efun j₀ y)
      (((fser s (x - y) : ℝ) : ℂ) * efun j₀ y) := fun y =>
    (Complex.hasSum_ofReal.2 (summable_term hs (x - y)).hasSum).mul_right _
  have hds : HasSum (fun j => ∫ y in (0:ℝ)..1, ((term s j (x - y) : ℝ) : ℂ) * efun j₀ y)
      (∫ y in (0:ℝ)..1, ((fser s (x - y) : ℝ) : ℂ) * efun j₀ y) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun j _ => coef s j)
      (fun j => (continuous_term_mul_efun s j j₀ x).aestronglyMeasurable) (fun j => ?_) ?_ ?_
      (ae_of_all _ fun y _ => hlim y)
    · refine ae_of_all _ fun y _ => ?_
      rw [norm_mul, norm_efun, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_term_le s j (x - y)
    · exact ae_of_all _ fun y _ => summable_coef hs
    · exact intervalIntegrable_const
  simp_rw [integral_term_mul_efun] at hds
  exact hds.unique (hasSum_ite_eq j₀ _)

/-! ## Lifting to the cube `[0,1]^(d+1)` -/

lemma integral_cube_eval (d : ℕ) {g : ℝ → ℂ} (hg : Continuous g) :
    ∫ y in cube (d + 1), g (y 0) = ∫ t in (0:ℝ)..1, g t := by
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩
  have hμ : volume.restrict (cube (d + 1)) =
      Measure.pi fun _ : Fin (d + 1) => volume.restrict (Set.Icc (0:ℝ) 1) := by
    rw [cube, volume_pi, Measure.restrict_pi_pi]
  have hmp := measurePreserving_eval
    (fun _ : Fin (d + 1) => volume.restrict (Set.Icc (0:ℝ) 1)) 0
  rw [hμ, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  calc ∫ y, g (y 0) ∂(Measure.pi fun _ : Fin (d + 1) => volume.restrict (Set.Icc (0:ℝ) 1))
      = ∫ t, g t ∂(Measure.map (Function.eval 0)
          (Measure.pi fun _ : Fin (d + 1) => volume.restrict (Set.Icc (0:ℝ) 1))) :=
        (integral_map hmp.measurable.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ t in Set.Icc (0:ℝ) 1, g t := by rw [hmp.map_eq]

/-- The counterexample kernel on `[0,1]^(d+1)`: `K(x,y) = f_s(x₀ - y₀)`. -/
def Kd (d : ℕ) (s : ℝ) (x y : Fin (d + 1) → ℝ) : ℝ := fser s (x 0 - y 0)

/-- The eigenfunction `φ_j(x) = exp(2π i (j+1) x₀)` on `[0,1]^(d+1)`. -/
def phi (d j : ℕ) (x : Fin (d + 1) → ℝ) : ℂ := efun j (x 0)

lemma Kd_symm (d : ℕ) (s : ℝ) (x y : Fin (d + 1) → ℝ) : Kd d s x y = Kd d s y x := by
  rw [Kd, Kd, ← fser_neg, neg_sub]

lemma continuous_fser {s : ℝ} (hs : 1 < s) : Continuous (fser s) :=
  (contDiff_fser (k := 0) (by simpa using hs)).continuous

lemma eigen_d {s : ℝ} (hs : 1 < s) (d j : ℕ) (x : Fin (d + 1) → ℝ) :
    intOp (Kd d s) (phi d j) x = ((coef s j / 2 : ℝ) : ℂ) * phi d j x := by
  have hg : Continuous fun t : ℝ => ((fser s (x 0 - t) : ℝ) : ℂ) * efun j t := by
    have := continuous_fser hs
    have := continuous_efun j
    fun_prop
  exact (integral_cube_eval d hg).trans (eigen_1d hs j (x 0))

lemma orthonormal_d (d a b : ℕ) :
    ∫ x in cube (d + 1), conj (phi d a x) * phi d b x = if a = b then 1 else 0 := by
  have hg : Continuous fun t : ℝ => conj (efun a t) * efun b t := by
    have := continuous_efun a
    have := continuous_efun b
    fun_prop
  exact (integral_cube_eval d hg).trans (integral_conj_efun_mul a b)

lemma posSemidef_Kd (d : ℕ) {s : ℝ} (hs : 1 < s) : PosSemidefKernel (Kd d s) := by
  intro p x c
  have hsw : ∑ a, ∑ b, c a * c b * Kd d s (x a) (x b) =
      ∑' j, ∑ a, ∑ b, c a * c b * term s j (x a 0 - x b 0) := by
    rw [Summable.tsum_finsetSum fun a _ => summable_sum fun b _ =>
      (summable_term hs _).mul_left _]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Summable.tsum_finsetSum fun b _ => (summable_term hs _).mul_left _]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Kd, fser, tsum_mul_left]
  rw [hsw]
  refine tsum_nonneg fun j => ?_
  set ω := 2 * Real.pi * ((j : ℝ) + 1)
  have key : ∑ a, ∑ b, c a * c b * term s j (x a 0 - x b 0) =
      coef s j * ((∑ a, c a * Real.cos (ω * x a 0)) * (∑ b, c b * Real.cos (ω * x b 0)) +
        (∑ a, c a * Real.sin (ω * x a 0)) * (∑ b, c b * Real.sin (ω * x b 0))) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [term, mul_sub, Real.cos_sub]; ring
  rw [key]
  exact mul_nonneg (coef_pos s j).le (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))

/-! ## The growth estimate and the main theorem -/

lemma growth (k D : ℕ) (hD : 1 ≤ D) (C : ℝ) : ∃ n : ℕ, 1 ≤ n ∧ ∀ i : ℕ, i < n →
    C * (n : ℝ) ^ (-((k : ℝ) + 1 + (D : ℝ) / 2)) < coef ((k : ℝ) + 5 / 4) i / 2 := by
  have hDr : (1:ℝ) ≤ D := by exact_mod_cast hD
  obtain ⟨n, hn2, hn1⟩ := ((((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 4)).comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop (2 * C)).and
      (eventually_ge_atTop 1)).exists
  refine ⟨n, hn1, fun i hi => ?_⟩
  have hn2' : 2 * C < (n : ℝ) ^ ((1:ℝ) / 4) := hn2
  have hn : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0:ℝ) < n := by linarith
  have hu : (n : ℝ) ^ ((1:ℝ) / 4) ≤ (n : ℝ) ^ ((D : ℝ) / 2 - 1 / 4) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hu0 : 0 < (n : ℝ) ^ ((D : ℝ) / 2 - 1 / 4) := Real.rpow_pos_of_pos hn0 _
  have hp0 : 0 < (n : ℝ) ^ (-((k : ℝ) + 5 / 4)) := Real.rpow_pos_of_pos hn0 _
  have hsplit : (n : ℝ) ^ (-((k : ℝ) + 1 + (D : ℝ) / 2)) =
      (n : ℝ) ^ (-((k : ℝ) + 5 / 4)) / (n : ℝ) ^ ((D : ℝ) / 2 - 1 / 4) := by
    rw [← Real.rpow_sub hn0]; congr 1; ring
  have hcoef : (n : ℝ) ^ (-((k : ℝ) + 5 / 4)) ≤ coef ((k : ℝ) + 5 / 4) i := by
    rw [coef, Real.rpow_neg hn0.le]
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by positivity) hi' (by positivity))
  rw [hsplit]
  have h2C : 2 * C < (n : ℝ) ^ ((D : ℝ) / 2 - 1 / 4) := lt_of_lt_of_le hn2' hu
  have : C * ((n : ℝ) ^ (-((k : ℝ) + 5 / 4)) / (n : ℝ) ^ ((D : ℝ) / 2 - 1 / 4)) <
      (n : ℝ) ^ (-((k : ℝ) + 5 / 4)) / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ hu0 two_pos]
    nlinarith
  linarith

lemma contDiff_Kd (d k : ℕ) : ContDiff ℝ k (Function.uncurry (Kd d ((k : ℝ) + 5 / 4))) := by
  have h1 : ContDiff ℝ k fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) => p.1 0 - p.2 0 := by
    fun_prop
  exact (contDiff_fser (by linarith)).comp h1

/-- No constant `C` gives the conjectured bound `|λ_n| ≤ C n^(-k-1-D/2)` for the kernel
`Kd d (k + 5/4)` on `[0,1]^D`, `D = d + 1`. -/
theorem not_eigenBound (d k : ℕ) : ¬ ∃ C : ℝ, EigenBound (Kd d ((k : ℝ) + 5 / 4)) k C := by
  have hs1 : 1 < (k : ℝ) + 5 / 4 := by have := k.cast_nonneg (α := ℝ); linarith
  rintro ⟨C, hC⟩
  obtain ⟨n, hn1, hgrow⟩ := growth k (d + 1) (by omega) C
  obtain ⟨i, hi⟩ := hC n hn1 (fun i => phi d i.val)
    (fun i => ((coef ((k : ℝ) + 5 / 4) i.val / 2 : ℝ) : ℂ))
    ⟨fun i => (continuous_efun _).comp (continuous_apply 0),
     fun i j => by rw [orthonormal_d]; simp [Fin.val_inj],
     fun i x _ => eigen_d hs1 d i.val x⟩
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by have := coef_pos ((k : ℝ) + 5 / 4) i.val; positivity)] at hi
  have := hgrow i.val i.isLt
  linarith

/-- **Disproof of the decay clause.** For every dimension `D = d + 1 ≥ 1` and every `k ≥ 0` there
is a real, symmetric, positive semidefinite kernel `K` on `[0,1]^D`, of class `C^k` on
`ℝ^D × ℝ^D`, such that `EigenBound K k C` fails for every constant `C`.  By the remark at
`EigenBound`, `|λ_n| ≤ C n^(-k-1-D/2)` then fails for every `C`. -/
theorem main (d k : ℕ) :
    ∃ K : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ) → ℝ,
      ContDiff ℝ k (Function.uncurry K) ∧ (∀ x y, K x y = K y x) ∧ PosSemidefKernel K ∧
      ¬ ∃ C : ℝ, EigenBound K k C :=
  ⟨Kd d ((k : ℝ) + 5 / 4), contDiff_Kd d k, Kd_symm d _,
    posSemidef_Kd d (by have := k.cast_nonneg (α := ℝ); linarith), not_eigenBound d k⟩

/-- In dimension `D = 1` the counterexample is radial: `K(x,y) = f(|x - y|)` with `f` of class
`C^k` on `ℝ`; `K` is `C^k` and positive semidefinite, and again no constant `C` works. -/
theorem main_radial (k : ℕ) :
    ∃ f : ℝ → ℝ, ContDiff ℝ k f ∧
      ContDiff ℝ k (Function.uncurry fun x y : Fin 1 → ℝ => f |x 0 - y 0|) ∧
      PosSemidefKernel (fun x y : Fin 1 → ℝ => f |x 0 - y 0|) ∧
      ¬ ∃ C : ℝ, EigenBound (fun x y : Fin 1 → ℝ => f |x 0 - y 0|) k C := by
  have hK : (fun x y : Fin 1 → ℝ => fser ((k : ℝ) + 5 / 4) |x 0 - y 0|) =
      Kd 0 ((k : ℝ) + 5 / 4) := by
    funext x y
    rcases abs_cases (x 0 - y 0) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h, Kd]
    · rw [h, Kd, fser_neg]
  refine ⟨fser ((k : ℝ) + 5 / 4), contDiff_fser (by linarith), ?_, ?_, ?_⟩
  · rw [hK]; exact contDiff_Kd 0 k
  · rw [hK]; exact posSemidef_Kd 0 (by have := k.cast_nonneg (α := ℝ); linarith)
  · rw [hK]; exact not_eigenBound 0 k

end C9779
