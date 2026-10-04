import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open scoped Classical
namespace NetworkSaddles
abbrev Point := ℝ × ℝ
def loss (c : ℝ) (p : Point) : ℝ := c*(p.1^2-1)^2+p.2^2

structure DenseLayer (m n : ℕ) where
  weights : Matrix (Fin n) (Fin m) ℝ
  bias : Fin n → ℝ
def DenseLayer.eval {m n} (L : DenseLayer m n) (u : Fin m → ℝ) (i : Fin n) : ℝ :=
  L.bias i + ∑ j, L.weights i j * u j
def squareActivation {n} (u : Fin n → ℝ) (i : Fin n) : ℝ := (u i)^2
structure Network where
  first : DenseLayer 2 3
  second : DenseLayer 3 2
  output : Fin 2 → ℝ
def Network.eval (N : Network) (p : Point) : ℝ :=
  ∑ i, N.output i * squareActivation
    (N.second.eval (squareActivation (N.first.eval ![p.1,p.2]))) i
def network (c : ℝ) : Network where
  first := ⟨!![1,0; 0,1; 0,1], ![0,1,-1]⟩
  second := ⟨!![1,0,0; 0,1/4,-1/4], ![-1,0]⟩
  output := ![c,1]

theorem network_formula (c : ℝ) (p : Point) :
    (network c).eval p = loss c p := by
  simp [Network.eval, network, DenseLayer.eval, squareActivation,
    Fin.sum_univ_two, Fin.sum_univ_three, loss]
  ring

def xCoord : Point →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
def yCoord : Point →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
def differential (c : ℝ) (p : Point) : Point →L[ℝ] ℝ :=
  (4*c*p.1*(p.1^2-1)) • xCoord + (2*p.2) • yCoord

theorem loss_derivative (c : ℝ) (p : Point) :
    HasFDerivAt (loss c) (differential c p) p := by
  have hx := xCoord.hasFDerivAt (x := p)
  have hy := yCoord.hasFDerivAt (x := p)
  have ha := (hx.mul hx).sub_const (1 : ℝ)
  have hf := ((ha.mul ha).const_mul c).add (hy.mul hy)
  convert hf using 1
  · ext q
    simp [loss, xCoord, yCoord, pow_two]
  · apply ContinuousLinearMap.ext
    intro q
    simp [differential, xCoord, yCoord]
    ring

theorem stationary_coordinates {c : ℝ} (hc : 0 < c) {p : Point}
    (h : differential c p = 0) :
    (p.1 = 0 ∨ p.1 = 1 ∨ p.1 = -1) ∧ p.2 = 0 := by
  have hx := congrArg (fun L : Point →L[ℝ] ℝ => L (1,0)) h
  have hy := congrArg (fun L : Point →L[ℝ] ℝ => L (0,1)) h
  simp [differential, xCoord, yCoord] at hx hy
  have he : p.1 = 0 ∨ p.1^2 = 1 := by
    rcases hx with (h1 | h1) | h1
    · exact False.elim ((ne_of_gt hc) h1)
    · exact Or.inl h1
    · right; linarith
  refine ⟨?_, hy⟩
  rcases he with he | he
  · exact Or.inl he
  · exact Or.inr (sq_eq_one_iff.mp he)

theorem origin_not_local_min {c : ℝ} (hc : 0 < c) :
    ¬ IsLocalMin (loss c) (0,0) := by
  intro h
  have hn : {q : Point | loss c (0,0) ≤ loss c q} ∈
      nhds ((0,0) : Point) := h
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε,hε,hball⟩
  let t : ℝ := min (ε/2) (1/2)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht1 : t ≤ 1/2 := min_le_right _ _
  have hb : ((t,0) : Point) ∈ Metric.ball (0,0) ε := by
    simp [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, Real.norm_eq_abs,
      abs_of_pos ht, max_eq_left (le_of_lt ht), htε]
  have hh := hball hb
  norm_num [loss] at hh
  have hs : 0 < t^2 := sq_pos_of_pos ht
  have hu : t^2 ≤ 1/4 := by nlinarith
  have hd : 0 < c*t^2*(2-t^2) :=
    mul_pos (mul_pos hc hs) (by linarith)
  nlinarith

def minimumPositions : Set Point := {p | (p.1 = 1 ∨ p.1 = -1) ∧ p.2 = 0}
theorem nonnegative {c : ℝ} (hc : 0 < c) (p : Point) : 0 ≤ loss c p :=
  add_nonneg (mul_nonneg (le_of_lt hc) (sq_nonneg _)) (sq_nonneg _)
theorem minimum_value {c : ℝ} (hc : 0 < c) {p : Point}
    (hp : p ∈ minimumPositions) :
    loss c p = 0 ∧ ∀ q, loss c p ≤ loss c q := by
  rcases hp with ⟨hx,hy⟩
  have hz : loss c p = 0 := by
    rcases hx with hx | hx <;> simp [loss,hx,hy]
  exact ⟨hz, fun q => hz ▸ nonnegative hc q⟩

theorem all_local_minima {c : ℝ} (hc : 0 < c) (p : Point) :
    IsLocalMin (loss c) p ↔ p ∈ minimumPositions := by
  constructor
  · intro h
    have hz : differential c p = 0 := by
      rw [← (loss_derivative c p).fderiv]
      exact h.fderiv_eq_zero
    rcases stationary_coordinates hc hz with ⟨hx,hy⟩
    rcases hx with hx | hx
    · have hp : p = (0,0) := Prod.ext hx hy
      exact False.elim (origin_not_local_min hc (hp ▸ h))
    · exact ⟨hx,hy⟩
  · intro hp
    exact Filter.Eventually.of_forall (minimum_value hc hp).2

theorem all_global_minima {c : ℝ} (hc : 0 < c) (p : Point) :
    (∀ q, loss c p ≤ loss c q) ↔ p ∈ minimumPositions := by
  constructor
  · intro h
    exact (all_local_minima hc p).mp (Filter.Eventually.of_forall h)
  · exact fun hp => (minimum_value hc hp).2

theorem derivative_x (c x y : ℝ) :
    deriv (fun t => loss c (t,y)) x = 4*c*x*(x^2-1) := by
  have h := (((((hasDerivAt_id x).pow 2).sub_const 1).pow 2).const_mul c).add_const (y^2)
  convert h.deriv using 1 <;> dsimp [loss] <;> ring
theorem derivative_y (c x y : ℝ) :
    deriv (fun t => loss c (x,t)) y = 2*y := by
  have h := ((hasDerivAt_id y).pow 2).const_add (c*(x^2-1)^2)
  convert h.deriv using 1 <;> dsimp [loss] <;> ring
theorem derivative_x_twice (c x : ℝ) :
    deriv (fun t => 4*c*t*(t^2-1)) x = 4*c*(3*x^2-1) := by
  have h := ((hasDerivAt_id x).const_mul (4*c)).mul
    (((hasDerivAt_id x).pow 2).sub_const 1)
  convert h.deriv using 1 <;> simp only [id_eq] <;> ring

theorem derivative_two (y : ℝ) : deriv (fun t : ℝ => 2*t) y = 2 := by
  simpa using ((hasDerivAt_id y).const_mul (2 : ℝ)).deriv

-- The actual Hessian entries are second partial derivatives of the network output.
def Hessian (f : Point → ℝ) (p : Point) : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  if i = 0 then
    if j = 0 then deriv (fun x => deriv (fun t => f (t,p.2)) x) p.1
    else deriv (fun y => deriv (fun x => f (x,y)) p.1) p.2
  else
    if j = 0 then deriv (fun x => deriv (fun y => f (x,y)) p.2) p.1
    else deriv (fun y => deriv (fun t => f (p.1,t)) y) p.2
def hessian (c : ℝ) (p : Point) := Hessian (loss c) p

theorem hessian_formula (c : ℝ) (p : Point) :
    hessian c p = !![4*c*(3*p.1^2-1),0; 0,2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hessian, Hessian, derivative_x, derivative_y, derivative_x_twice, derivative_two, deriv_const]

abbrev CMat := Matrix (Fin 2) (Fin 2) ℂ
theorem saddle_spectrum (c : ℝ) :
    spectrum ℂ ((hessian c (0,0)).map Complex.ofReal) =
      {((-4*c : ℝ) : ℂ), (2 : ℂ)} := by
  ext z
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hd :
      (algebraMap ℂ CMat z - (hessian c (0,0)).map Complex.ofReal).det =
      (z - ((-4*c : ℝ) : ℂ))*(z-2) := by
    simp [hessian_formula, Matrix.det_fin_two, Matrix.algebraMap_matrix_apply,
      Matrix.map_apply]
  rw [hd]
  simp only [not_not, mul_eq_zero, sub_eq_zero,
    Set.mem_insert_iff, Set.mem_singleton_iff]

theorem origin_critical (c : ℝ) :
    HasFDerivAt (loss c) (0 : Point →L[ℝ] ℝ) (0,0) := by
  simpa [differential] using loss_derivative c (0,0)

theorem spectra_differ :
    spectrum ℂ ((hessian 1 (0,0)).map Complex.ofReal) ≠
    spectrum ℂ ((hessian 2 (0,0)).map Complex.ofReal) := by
  rw [saddle_spectrum, saddle_spectrum]
  intro h
  have hm : (-4 : ℂ) ∈ ({((-4*(1 : ℝ) : ℝ) : ℂ), (2 : ℂ)} : Set ℂ) := by norm_num
  rw [h] at hm
  norm_num at hm

theorem explicit_perturbation (p : Point) :
    (network 2).eval p - (network 1).eval p = (p.1^2-1)^2 := by
  rw [network_formula, network_formula]
  unfold loss
  ring

def StrictSaddle (N : Network) (p : Point) : Prop :=
  HasFDerivAt N.eval (0 : Point →L[ℝ] ℝ) p ∧
  ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
    (a : ℂ) ∈ spectrum ℂ ((Hessian N.eval p).map Complex.ofReal) ∧
    (b : ℂ) ∈ spectrum ℂ ((Hessian N.eval p).map Complex.ofReal)

theorem network_saddle {c : ℝ} (hc : 0 < c) : StrictSaddle (network c) (0,0) := by
  have he : (network c).eval = loss c := funext (network_formula c)
  unfold StrictSaddle
  rw [he]
  refine ⟨origin_critical c, -4*c, 2, by linarith, by norm_num, ?_, ?_⟩
  · change ((-4*c : ℝ) : ℂ) ∈ spectrum ℂ ((hessian c (0,0)).map Complex.ofReal)
    rw [saddle_spectrum]
    simp
  · change (2 : ℂ) ∈ spectrum ℂ ((hessian c (0,0)).map Complex.ofReal)
    rw [saddle_spectrum]
    simp

theorem counterexample :
    ∃ N₁ N₂ : Network,
      (∀ p, IsLocalMin N₁.eval p ↔ p ∈ minimumPositions) ∧
      (∀ p, IsLocalMin N₂.eval p ↔ p ∈ minimumPositions) ∧
      (∀ p ∈ minimumPositions, N₁.eval p = 0 ∧ N₂.eval p = 0) ∧
      StrictSaddle N₁ (0,0) ∧ StrictSaddle N₂ (0,0) ∧
      spectrum ℂ ((Hessian N₁.eval (0,0)).map Complex.ofReal) ≠
        spectrum ℂ ((Hessian N₂.eval (0,0)).map Complex.ofReal) ∧
      (∀ p, N₂.eval p - N₁.eval p = (p.1^2-1)^2) := by
  have h₁ : (network 1).eval = loss 1 := funext (network_formula 1)
  have h₂ : (network 2).eval = loss 2 := funext (network_formula 2)
  refine ⟨network 1, network 2, ?_, ?_, ?_,
    network_saddle (by norm_num), network_saddle (by norm_num), ?_, explicit_perturbation⟩
  · rw [h₁]
    exact all_local_minima (by norm_num)
  · rw [h₂]
    exact all_local_minima (by norm_num)
  · intro p hp
    rw [network_formula, network_formula]
    exact ⟨(minimum_value (by norm_num) hp).1, (minimum_value (by norm_num) hp).1⟩
  · rw [h₁,h₂]
    exact spectra_differ

#print axioms network_formula
#print axioms loss_derivative
#print axioms all_local_minima
#print axioms all_global_minima
#print axioms minimum_value
#print axioms hessian_formula
#print axioms saddle_spectrum
#print axioms origin_critical
#print axioms spectra_differ
#print axioms explicit_perturbation
#print axioms network_saddle
#print axioms counterexample
end NetworkSaddles
