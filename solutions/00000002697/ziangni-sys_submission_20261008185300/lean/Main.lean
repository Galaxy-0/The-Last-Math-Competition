import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

open Filter Matrix
open scoped Topology
namespace TangentShears
abbrev E := ℝ × ℝ
abbrev Op := E →L[ℝ] E
def F (p : E) : E := (1+p.1-6*p.1^2+4*p.1^3+(1-p.1)*p.2, p.1^3-p.1^2+p.2)
noncomputable def J (p : E) : Op :=
  ((1-12*p.1+12*p.1^2-p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (1-p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
  ((3*p.1^2-2*p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)
@[simp] theorem J_apply (p v : E) : J p v =
    ((1-12*p.1+12*p.1^2-p.2)*v.1+(1-p.1)*v.2, (3*p.1^2-2*p.1)*v.1+v.2) := rfl

theorem derivative (p : E) : HasFDerivAt F (J p) p := by
  have hx : HasFDerivAt (fun q : E => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hy : HasFDerivAt (fun q : E => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hx2 := hx.mul hx
  have hx3 := hx2.mul hx
  have h1 := ((((hasFDerivAt_const (1:ℝ) p).add hx).sub (hx2.const_mul 6)).add
    (hx3.const_mul 4)).add (((hasFDerivAt_const (1:ℝ) p).sub hx).mul hy)
  have h2 := (hx3.sub hx2).add hy
  convert h1.prodMk h2 using 1
  · apply funext; intro q; apply Prod.ext <;> simp [F] <;> ring
  · apply ContinuousLinearMap.ext; intro v; apply Prod.ext <;> simp [J_apply] <;> ring

def orbit (n : ℕ) : E := if n%2=0 then (0,0) else (1,0)
@[simp] theorem orbit_even (m : ℕ) : orbit (2*m) = (0,0) := by simp [orbit]
@[simp] theorem orbit_odd (m : ℕ) : orbit (2*m+1) = (1,0) := by simp [orbit, Nat.add_mod]

theorem orbit_step (n : ℕ) : orbit (n+1) = F (orbit n) := by
  have ht := Nat.mod_lt n (show 0<2 by norm_num)
  by_cases h : n%2=0
  · have hn : (n+1)%2=1 := by omega
    norm_num [orbit, h, hn, F]
  · have hc : n%2=1 := by omega
    have hn : (n+1)%2=0 := by omega
    norm_num [orbit, hc, hn, F]

noncomputable def A : Op := (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).prod
  (ContinuousLinearMap.snd ℝ ℝ ℝ)
noncomputable def B : Op := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
  (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)
@[simp] theorem A_apply (v : E) : A v = (v.1+v.2,v.2) := rfl
@[simp] theorem B_apply (v : E) : B v = (v.1,v.1+v.2) := rfl
@[simp] theorem J_zero : J (0,0) = A := by ext v <;> norm_num [J_apply]
@[simp] theorem J_one : J (1,0) = B := by ext v <;> norm_num [J_apply]

-- The complexified actual Jacobian matrices at the two orbit points.
def jacobianMatrix (p : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1-12*p.1+12*p.1^2-p.2 : ℝ) : ℂ), ((1-p.1 : ℝ) : ℂ);
     ((3*p.1^2-2*p.1 : ℝ) : ℂ), 1]

theorem spectral_determinant (n : ℕ) (z : ℂ) :
    (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - jacobianMatrix (orbit n)).det = (z-1)^2 := by
  unfold orbit
  split_ifs <;> rw [Matrix.det_fin_two] <;> simp [jacobianMatrix] <;> ring

theorem spectrum_one (n : ℕ) : spectrum ℂ (jacobianMatrix (orbit n)) = {1} := by
  ext z
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
  simp only [isUnit_iff_ne_zero, not_not, Set.mem_singleton_iff]
  rw [Algebra.algebraMap_eq_smul_one]
  change (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - jacobianMatrix (orbit n)).det = 0 ↔ z=1
  rw [spectral_determinant]
  simp [sub_eq_zero]

noncomputable def rho : ℝ := (3+Real.sqrt 5)/2

theorem rho_properties : 2 < rho ∧ rho^2-3*rho+1=0 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg 5
  constructor <;> dsimp [rho] <;> nlinarith

noncomputable def v : E := (1,rho-1)
noncomputable def w : E := (rho,rho-1)
@[simp] theorem A_v : A v = w := by ext <;> simp [v,w]
@[simp] theorem B_w : B w = rho • v := by
  have hp := rho_properties.2
  ext <;> simp [v,w,Prod.smul_mk] <;> nlinarith

noncomputable def tangent : ℕ → E
  | 0 => v
  | n+1 => J (orbit n) (tangent n)

theorem tangent_even_odd (m : ℕ) : tangent (2*m) = rho^m • v ∧ tangent (2*m+1) = rho^m • w := by
  induction m with
  | zero => simp [tangent, orbit, v, w]
  | succ m ih =>
    have he : tangent (2*(m+1)) = rho^(m+1) • v := by
      rw [show 2*(m+1)= (2*m+1)+1 by omega, tangent, orbit_odd, J_one, ih.2,
        map_smul, B_w, smul_smul, ← pow_succ]
    refine ⟨he, ?_⟩
    rw [tangent, orbit_even, J_zero, he, map_smul, A_v]

theorem tangent_formula (n : ℕ) :
    tangent n = rho^(n/2) • (if n%2=0 then v else w) := by
  have ht := Nat.mod_lt n (show 0<2 by norm_num)
  have hn := Nat.mod_add_div n 2
  by_cases h : n%2=0
  · have he : n=2*(n/2) := by omega
    rw [if_pos h, he]
    simpa using (tangent_even_odd (n/2)).1
  · have he : n=2*(n/2)+1 := by omega
    have hd : (2*(n/2)+1)/2 = n/2 := by omega
    rw [if_neg h, he, hd]
    simpa using (tangent_even_odd (n/2)).2

@[simp] theorem norm_v : ‖v‖ = rho-1 := by
  have hp := rho_properties.1
  simp [v, Prod.norm_def, Real.norm_eq_abs, abs_of_pos (by linarith : 0<rho-1), max_eq_right (by linarith : 1≤rho-1)]
@[simp] theorem norm_w : ‖w‖ = rho := by
  have hp := rho_properties.1
  simp [w, Prod.norm_def, Real.norm_eq_abs, abs_of_pos (by linarith : 0<rho),
    abs_of_pos (by linarith : 0<rho-1), max_eq_left (by linarith : rho-1≤rho)]

noncomputable def remainder (n : ℕ) : ℝ := if n%2=0 then Real.log (rho-1) else Real.log rho

theorem log_growth (n : ℕ) : Real.log ‖tangent n‖ = (n/2 : ℕ)*Real.log rho + remainder n := by
  have hr := rho_properties.1
  have hp : 0<rho := by linarith
  have hm : rho-1≠0 := by linarith
  rw [tangent_formula, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hp _)]
  by_cases h : n%2=0
  · simp only [if_pos h, norm_v, remainder]
    rw [Real.log_mul (pow_ne_zero _ hp.ne') hm, Real.log_pow]
  · simp only [if_neg h, norm_w, remainder]
    rw [Real.log_mul (pow_ne_zero _ hp.ne') hp.ne', Real.log_pow]
theorem quotient_limit : Tendsto (fun n : ℕ => ((n/2 : ℕ) : ℝ)/(n:ℝ)) atTop (𝓝 (1/2)) := by
  have hm := tendsto_mod_div_atTop_nhds_zero_nat (show 0<2 by norm_num)
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hh : Tendsto (fun n : ℕ => (1-(n%2:ℕ)/(n:ℝ))/2) atTop (𝓝 (1/2)) := by
    simpa using (h1.sub hm).div_const (2:ℝ)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hc : (n:ℝ) = (n%2:ℕ) + 2*(n/2:ℕ) := by exact_mod_cast (Nat.mod_add_div n 2).symm
  field_simp
  nlinarith

theorem remainder_limit : Tendsto (fun n : ℕ => remainder n/(n:ℝ)) atTop (𝓝 0) := by
  have hp := rho_properties.1
  have hl0 : 0≤Real.log (rho-1) := Real.log_nonneg (by linarith)
  have hl1 : 0≤Real.log rho := Real.log_nonneg (by linarith)
  have hle : Real.log (rho-1) ≤ Real.log rho := Real.log_le_log (by linarith) (by linarith)
  apply tendsto_bdd_div_atTop_nhds_zero (b := (0:ℝ)) (B := Real.log rho) _ _ tendsto_natCast_atTop_atTop
  · exact Eventually.of_forall fun n => by unfold remainder; split_ifs <;> assumption
  · exact Eventually.of_forall fun n => by unfold remainder; split_ifs <;> simp_all

theorem lyapunov_exponent : Tendsto (fun n : ℕ => Real.log ‖tangent n‖/(n:ℝ))
    atTop (𝓝 (Real.log rho/2)) := by
  have ht := (quotient_limit.mul_const (Real.log rho)).add remainder_limit
  convert ht using 1
  · ext n
    rw [log_growth]
    ring
  · ring

theorem spectral_average_zero (e : ℕ → ℂ)
    (he : ∀ n, e n ∈ spectrum ℂ (jacobianMatrix (orbit n))) (N : ℕ) :
    (∑ n ∈ Finset.range N, Real.log ‖e n‖)/(N:ℝ) = 0 := by
  have hz : ∀ n, Real.log ‖e n‖ = 0 := by
    intro n
    have hh := he n
    rw [spectrum_one, Set.mem_singleton_iff] at hh
    rw [hh]
    simp
  simp [hz]
theorem exponent_positive : 0<Real.log rho/2 := by
  have hp := rho_properties.1
  exact div_pos (Real.log_pos (by linarith)) (by norm_num)

theorem conjecture_false : Real.log rho/2 ≠ 0 := ne_of_gt exponent_positive

#print axioms derivative
#print axioms orbit_step
#print axioms spectrum_one
#print axioms tangent_even_odd
#print axioms log_growth
#print axioms lyapunov_exponent
#print axioms exponent_positive
#print axioms spectral_average_zero
#print axioms conjecture_false
end TangentShears
