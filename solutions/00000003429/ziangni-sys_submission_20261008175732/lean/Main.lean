import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open scoped Matrix Topology
namespace ObservableMixing
attribute [local simp] Matrix.cons_val_two

def P : Matrix (Fin 3) (Fin 3) ℝ := !![5/8, 1/8, 1/4; 1/8, 5/8, 1/4; 1/4, 1/4, 1/2]
def π (_i : Fin 3) : ℝ := 1/3
def f : Fin 3 → ℝ := ![1, 1, -2]
def slow : Fin 3 → ℝ := ![1, -1, 0]

theorem positive (i j : Fin 3) : 0 < P i j := by fin_cases i <;> fin_cases j <;> norm_num [P]
theorem stochastic (i : Fin 3) : ∑ j, P i j = 1 := by fin_cases i <;> norm_num [P, Fin.sum_univ_three]
theorem lazy (i : Fin 3) : 1/2 ≤ P i i := by fin_cases i <;> norm_num [P]
theorem probability : (∀ i, 0 < π i) ∧ ∑ i, π i = 1 := by norm_num [π, Fin.sum_univ_three]
theorem stationary (j : Fin 3) : ∑ i, π i * P i j = π j := by
  fin_cases j <;> norm_num [P, π, Fin.sum_univ_three]
theorem reversible (i j : Fin 3) : π i * P i j = π j * P j i := by
  fin_cases i <;> fin_cases j <;> norm_num [P, π]

def centered (v : Fin 3 → ℝ) : Prop := ∑ i, π i * v i = 0
theorem observable_centered : centered f := by norm_num [centered, f, π, Fin.sum_univ_three]
theorem observable_nonzero : f ≠ 0 := by intro h; have := congrFun h 0; norm_num [f] at this
theorem observable_eigen : P *ᵥ f = (1/4 : ℝ) • f := by
  ext i; fin_cases i <;> norm_num [P, f, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Coordinates for the actual two-dimensional centered observable space. -/
def encode (x : Fin 2 → ℝ) : Fin 3 → ℝ := ![x 0 + x 1, -x 0 + x 1, -2 * x 1]
def D : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 0; 0, 1/4]

theorem encode_centered (x : Fin 2 → ℝ) : centered (encode x) := by
  simp [centered, encode, π, Fin.sum_univ_three]; ring

theorem encode_injective : Function.Injective encode := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [encode, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  ext i
  fin_cases i <;> dsimp at * <;> linarith

theorem encode_surjective_centered (v : Fin 3 → ℝ) (hv : centered v) :
    ∃ x : Fin 2 → ℝ, encode x = v := by
  refine ⟨![(v 0-v 1)/2, (v 0+v 1)/2], ?_⟩
  simp only [centered, π, Fin.sum_univ_three] at hv
  ext i
  fin_cases i <;> simp [encode] <;> linarith

theorem restriction_conjugacy (x : Fin 2 → ℝ) : P *ᵥ encode x = encode (D *ᵥ x) := by
  ext i
  fin_cases i <;> simp [P, D, encode, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

theorem restricted_spectrum : spectrum ℝ D = {(1/2 : ℝ), 1/4} := by
  ext z
  have hd : (algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) z - D).det = (z-1/2)*(z-1/4) := by
    simp [Matrix.det_fin_two, Matrix.algebraMap_eq_diagonal, D]
  simp [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, hd, isUnit_iff_ne_zero, mul_eq_zero, sub_eq_zero]
  tauto

/-- Spectral radius of the centered restriction in the displayed coordinates. -/
def mixingRadius : ℝ := sSup ((fun z : ℝ => |z|) '' spectrum ℝ D)

theorem mixing_radius_eq : mixingRadius = 1/2 := by
  norm_num [mixingRadius, restricted_spectrum, Set.image_insert_eq, Set.image_singleton, abs_of_pos, max_eq_left]

theorem power_observable (n : ℕ) : (P^n) *ᵥ f = (1/4 : ℝ)^n • f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, observable_eigen]
    simp [smul_smul, pow_succ, mul_comm]

/-- Stationary autocorrelation, normalized by the positive stationary variance. -/
def covariance (n : ℕ) : ℝ := ∑ i, π i * f i * ((P^n) *ᵥ f) i
def correlation (n : ℕ) : ℝ := covariance n / covariance 0

theorem covariance_eq (n : ℕ) : covariance n = 2 * (1/4 : ℝ)^n := by
  unfold covariance
  rw [power_observable]
  simp [π, f, Fin.sum_univ_three]
  ring

theorem correlation_eq (n : ℕ) : correlation n = (1/4 : ℝ)^n := by
  rw [correlation, covariance_eq, covariance_eq]
  norm_num

theorem lag_regression (n : ℕ) : correlation (n+1) / correlation n = 1/4 := by
  rw [correlation_eq, correlation_eq, pow_succ]
  field_simp

theorem root_rate (n : ℕ) : |correlation (n+1)| ^ ((n+1 : ℕ) : ℝ)⁻¹ = (1/4 : ℝ) := by
  rw [correlation_eq, abs_of_pos (by positivity)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (1/4 : ℝ)),
    mul_inv_cancel₀ (by positivity : ((n+1 : ℕ) : ℝ) ≠ 0), Real.rpow_one]

theorem exponential_rate_limit :
    Filter.Tendsto (fun n : ℕ => |correlation (n+1)| ^ ((n+1 : ℕ) : ℝ)⁻¹)
      Filter.atTop (𝓝 (1/4 : ℝ)) := by
  simpa only [root_rate] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1/4 : ℝ)) Filter.atTop (𝓝 (1/4 : ℝ)))

theorem observable_rate_ne_mixing : (1/4 : ℝ) ≠ mixingRadius := by rw [mixing_radius_eq]; norm_num

theorem rate_limit_not_mixing :
    ¬ Filter.Tendsto (fun n : ℕ => |correlation (n+1)| ^ ((n+1 : ℕ) : ℝ)⁻¹)
      Filter.atTop (𝓝 mixingRadius) := by
  intro h
  exact observable_rate_ne_mixing (tendsto_nhds_unique exponential_rate_limit h)

#print axioms positive
#print axioms stochastic
#print axioms lazy
#print axioms probability
#print axioms stationary
#print axioms reversible
#print axioms observable_centered
#print axioms observable_nonzero
#print axioms encode_centered
#print axioms encode_injective
#print axioms encode_surjective_centered
#print axioms restriction_conjugacy
#print axioms mixing_radius_eq
#print axioms covariance_eq
#print axioms correlation_eq
#print axioms lag_regression
#print axioms exponential_rate_limit
#print axioms observable_rate_ne_mixing
#print axioms rate_limit_not_mixing
end ObservableMixing
