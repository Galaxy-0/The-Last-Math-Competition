import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

open Matrix
namespace CriticalDirections
abbrev E := ℝ × ℝ
noncomputable def F (μ : ℝ) (p : E) : E := (μ*p.1+p.1^3, μ*p.2+p.2^3)
noncomputable def J (μ : ℝ) (p : E) : E →L[ℝ] E :=
  ((μ+3*p.1^2) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
  ((μ+3*p.2^2) • ContinuousLinearMap.snd ℝ ℝ ℝ)
@[simp] theorem J_apply (μ : ℝ) (p v : E) :
    J μ p v = ((μ+3*p.1^2)*v.1,(μ+3*p.2^2)*v.2) := rfl

theorem derivative (μ : ℝ) (p : E) : HasFDerivAt (F μ) (J μ p) p := by
  have hx : HasFDerivAt (fun q : E => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hy : HasFDerivAt (fun q : E => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have h1 := (hx.const_mul μ).add ((hx.mul hx).mul hx)
  have h2 := (hy.const_mul μ).add ((hy.mul hy).mul hy)
  convert h1.prodMk h2 using 1
  · funext q; apply Prod.ext <;> simp [F] <;> ring
  · apply ContinuousLinearMap.ext; intro v; apply Prod.ext <;> simp [J_apply] <;> ring

@[simp] theorem fixed_zero (μ : ℝ) : F μ (0,0) = (0,0) := by simp [F]
theorem critical_derivative : J 1 (0,0) = ContinuousLinearMap.id ℝ E := by
  ext v <;> simp [J_apply]
def jacobianMatrix (μ : ℝ) (p : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((μ+3*p.1^2 : ℝ) : ℂ), 0; 0, ((μ+3*p.2^2 : ℝ) : ℂ)]
theorem spectrum_zero (μ : ℝ) : spectrum ℂ (jacobianMatrix μ (0,0)) = {(μ : ℂ)} := by
  ext z
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
  simp only [isUnit_iff_ne_zero, not_not, Set.mem_singleton_iff]
  rw [Algebra.algebraMap_eq_smul_one]
  change (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - jacobianMatrix μ (0,0)).det = 0 ↔ z=(μ:ℂ)
  rw [Matrix.det_fin_two]
  simp [jacobianMatrix, sub_eq_zero]

theorem critical_spectral_radius :
    spectrum ℂ (jacobianMatrix 1 (0,0)) = {1} ∧
    (∀ z ∈ spectrum ℂ (jacobianMatrix 1 (0,0)), ‖z‖ = (1:ℝ)) := by
  constructor
  · simpa using spectrum_zero 1
  · intro z hz
    rw [spectrum_zero] at hz
    have h : z=1 := by simpa using hz
    rw [h]
    norm_num
noncomputable def scalarOrbit (a : ℝ) : ℕ → ℝ
  | 0 => a
  | n+1 => scalarOrbit a n + (scalarOrbit a n)^3

theorem scalar_growth (a : ℝ) (ha : 0 < a) (n : ℕ) :
    a ≤ scalarOrbit a n ∧ a+(n:ℝ)*a^3 ≤ scalarOrbit a n := by
  induction n with
  | zero => simp [scalarOrbit]
  | succ n ih =>
    have hpow : a^3 ≤ (scalarOrbit a n)^3 := by exact pow_le_pow_left₀ ha.le ih.1 3
    have hp : 0 < a^3 := pow_pos ha 3
    simp only [scalarOrbit, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith

theorem scalar_escape (a : ℝ) (ha : 0 < a) (R : ℝ) : ∃ n, R < scalarOrbit a n := by
  have hp : 0 < a^3 := pow_pos ha 3
  obtain ⟨n, hn⟩ := exists_nat_gt ((R-a)/a^3)
  have hm : R-a < (n:ℝ)*a^3 := (div_lt_iff₀ hp).mp hn
  exact ⟨n, lt_of_lt_of_le (by linarith) (scalar_growth a ha n).2⟩

theorem axis_orbits (a : ℝ) (n : ℕ) :
    (F 1)^[n] (a,0) = (scalarOrbit a n,0) ∧
    (F 1)^[n] (0,a) = (0,scalarOrbit a n) := by
  induction n with
  | zero => simp [scalarOrbit]
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih.1, ih.2, F, scalarOrbit]
    norm_num

-- A forward direction is nonlinearly repelling if arbitrarily small positive
-- displacements along it leave the closed unit neighborhood under true iteration.
def RepellingDirection (v : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ‖a • v‖ < ε ∧
    ∃ n : ℕ, 1 < ‖(F 1)^[n] (a • v)‖

theorem two_repelling_directions : RepellingDirection (1,0) ∧ RepellingDirection (0,1) := by
  constructor
  · intro ε hε
    refine ⟨ε/2, by positivity, ?_, ?_⟩
    · simp [norm_smul, Prod.norm_def, Real.norm_eq_abs, abs_of_pos hε]
      exact hε
    · obtain ⟨n, hn⟩ := scalar_escape (ε/2) (by positivity) 1
      refine ⟨n, ?_⟩
      simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
      rw [(axis_orbits (ε/2) n).1]
      apply lt_of_lt_of_le _ (le_max_left ‖scalarOrbit (ε/2) n‖ ‖(0:ℝ)‖)
      simpa [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < scalarOrbit (ε/2) n)] using hn
  · intro ε hε
    refine ⟨ε/2, by positivity, ?_, ?_⟩
    · simp [norm_smul, Prod.norm_def, Real.norm_eq_abs, abs_of_pos hε]
      exact hε
    · obtain ⟨n, hn⟩ := scalar_escape (ε/2) (by positivity) 1
      refine ⟨n, ?_⟩
      simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
      rw [(axis_orbits (ε/2) n).2]
      apply lt_of_lt_of_le _ (le_max_right ‖(0:ℝ)‖ ‖scalarOrbit (ε/2) n‖)
      simpa [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < scalarOrbit (ε/2) n)] using hn
theorem directions_independent (s t : ℝ) (h : s • ((1,0) : E) + t • ((0,1) : E) = 0) : s=0 ∧ t=0 := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simpa using And.intro h1 h2

theorem not_unique_critical_direction :
    ¬ ∃ v : E, ∀ w : E, RepellingDirection w → ∃ c : ℝ, w = c • v := by
  rintro ⟨v,h⟩
  obtain ⟨s, hs⟩ := h (1,0) two_repelling_directions.1
  obtain ⟨t, ht⟩ := h (0,1) two_repelling_directions.2
  have hs1 := congrArg Prod.fst hs
  have hs2 := congrArg Prod.snd hs
  have ht1 := congrArg Prod.fst ht
  have ht2 := congrArg Prod.snd ht
  simp only [Prod.fst, Prod.snd, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at *
  have hv : v.1 ≠ 0 := by intro hv; simp [hv] at hs1
  have hz : t=0 := (mul_eq_zero.mp ht1.symm).resolve_right hv
  simp [hz] at ht2

#print axioms derivative
#print axioms critical_derivative
#print axioms spectrum_zero
#print axioms critical_spectral_radius
#print axioms scalar_growth
#print axioms scalar_escape
#print axioms axis_orbits
#print axioms two_repelling_directions
#print axioms directions_independent
#print axioms not_unique_critical_direction
end CriticalDirections
