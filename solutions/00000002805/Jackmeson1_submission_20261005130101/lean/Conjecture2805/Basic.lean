import Mathlib

/-!
# Conjecture 00000002805: the zero set of the Schilder rate is not the Cameron–Martin unit ball

Setting (Schilder's theorem): `B` is a standard Brownian motion in `ℝ^d` on the time interval
`[0, T]`, `T > 0`. The path space is `C₀ = C₀([0,T]; ℝ^d)` (continuous paths with `ω 0 = 0`).
The Cameron–Martin space is the subspace of absolutely continuous paths whose derivative is in
`L²`, and the Schilder rate function is
`I(ω) = ½ ∫₀ᵀ ‖ω̇(t)‖² dt` if `ω` is absolutely continuous, `I(ω) = +∞` otherwise.
The Cameron–Martin norm is `‖ω‖_H = (∫₀ᵀ ‖ω̇(t)‖² dt)^{1/2}`.

The conjecture claims (first clause): `I(ω) = 0` if and only if `ω` lies in the Cameron–Martin
unit ball. We refute this for every dimension `d ≥ 1` and every horizon `T > 0`: the straight
path `ω₀(t) = t • w`, `‖w‖ = 1/(2√T)`, has `‖ω₀‖_H² = 1/4` (so it lies in the closed and in the
open unit ball) but `I(ω₀) = 1/8 ≠ 0`.

`ℝ^d` is `EuclideanSpace ℝ (Fin d)`; the derivative is Mathlib's `deriv`; the integrals are
lower Lebesgue integrals over `Set.Icc 0 T`, so `I(ω)` and `‖ω‖_H²` take values in `[0, ∞]`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace C2805

/-- `ℝ^d` with the Euclidean norm. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The path space `C₀([0,T]; ℝ^d)`: paths continuous on `[0,T]` starting at `0`. -/
def PathSpace (d : ℕ) (T : ℝ) : Set (ℝ → Rd d) :=
  {ω | ContinuousOn ω (Icc 0 T) ∧ ω 0 = 0}

/-- The Cameron–Martin space: paths in `C₀` that are absolutely continuous on `[0,T]` and whose
derivative is in `L²([0,T]; ℝ^d)`. -/
def CameronMartin (d : ℕ) (T : ℝ) : Set (ℝ → Rd d) :=
  {ω | ω 0 = 0 ∧ AbsolutelyContinuousOnInterval ω 0 T ∧
    MemLp (deriv ω) 2 (volume.restrict (Icc 0 T))}

/-- The squared Cameron–Martin norm `‖ω‖_H² = ∫₀ᵀ ‖ω̇(t)‖² dt` (in `[0, ∞]`). -/
def cmNormSq (T : ℝ) {d : ℕ} (ω : ℝ → Rd d) : ℝ≥0∞ :=
  ∫⁻ t in Icc 0 T, ‖deriv ω t‖ₑ ^ 2

/-- The closed Cameron–Martin unit ball `{ω ∈ H : ‖ω‖_H ≤ 1}`. -/
def cmClosedUnitBall (d : ℕ) (T : ℝ) : Set (ℝ → Rd d) :=
  {ω | ω ∈ CameronMartin d T ∧ cmNormSq T ω ≤ 1}

/-- The open Cameron–Martin unit ball `{ω ∈ H : ‖ω‖_H < 1}`. -/
def cmOpenUnitBall (d : ℕ) (T : ℝ) : Set (ℝ → Rd d) :=
  {ω | ω ∈ CameronMartin d T ∧ cmNormSq T ω < 1}

open Classical in
/-- Schilder's rate function: `I(ω) = ½ ∫₀ᵀ ‖ω̇(t)‖² dt` if `ω` is absolutely continuous on
`[0,T]`, and `+∞` otherwise. -/
def schilderRate (d : ℕ) (T : ℝ) (ω : ℝ → Rd d) : ℝ≥0∞ :=
  if AbsolutelyContinuousOnInterval ω 0 T then (1 / 2 : ℝ≥0∞) * cmNormSq T ω else ⊤

/-- The rate is half the squared Cameron–Martin norm on the Cameron–Martin space. -/
theorem schilderRate_eq_of_mem {d : ℕ} {T : ℝ} {ω : ℝ → Rd d} (h : ω ∈ CameronMartin d T) :
    schilderRate d T ω = (1 / 2 : ℝ≥0∞) * cmNormSq T ω := by
  rw [schilderRate, if_pos h.2.1]

/-- The direction vector `w = (1/(2√T)) e₀`. -/
def dir (d : ℕ) [NeZero d] (T : ℝ) : Rd d :=
  (1 / (2 * Real.sqrt T)) • EuclideanSpace.single (0 : Fin d) (1 : ℝ)

/-- The straight path `ω₀(t) = t • w`. -/
def straightPath (d : ℕ) [NeZero d] (T : ℝ) : ℝ → Rd d := fun t => t • dir d T

theorem norm_dir (d : ℕ) [NeZero d] {T : ℝ} (hT : 0 < T) : ‖dir d T‖ = 1 / (2 * Real.sqrt T) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  rw [dir, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

theorem deriv_straightPath (d : ℕ) [NeZero d] (T : ℝ) :
    deriv (straightPath d T) = fun _ => dir d T := by
  funext t
  have h := (hasDerivAt_id t).smul_const (dir d T)
  simp only [id, one_smul] at h
  exact h.deriv

theorem straightPath_mem_pathSpace (d : ℕ) [NeZero d] (T : ℝ) :
    straightPath d T ∈ PathSpace d T := by
  refine ⟨?_, by simp [straightPath]⟩
  exact (continuous_id.smul continuous_const).continuousOn

theorem straightPath_mem_cameronMartin (d : ℕ) [NeZero d] (T : ℝ) :
    straightPath d T ∈ CameronMartin d T := by
  refine ⟨by simp [straightPath], ?_, ?_⟩
  · apply ContDiffOn.absolutelyContinuousOnInterval
    exact (contDiff_id.smul contDiff_const).contDiffOn
  · rw [deriv_straightPath]
    exact memLp_const _

/-- `‖ω₀‖_H² = 1/4`. -/
theorem cmNormSq_straightPath (d : ℕ) [NeZero d] {T : ℝ} (hT : 0 < T) :
    cmNormSq T (straightPath d T) = ENNReal.ofReal (1 / 4) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hsq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  rw [cmNormSq, deriv_straightPath, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Icc, sub_zero, ← ofReal_norm, norm_dir d hT,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  rw [hsq]
  ring

/-- `I(ω₀) = 1/8`. -/
theorem schilderRate_straightPath (d : ℕ) [NeZero d] {T : ℝ} (hT : 0 < T) :
    schilderRate d T (straightPath d T) = ENNReal.ofReal (1 / 8) := by
  rw [schilderRate_eq_of_mem (straightPath_mem_cameronMartin d T), cmNormSq_straightPath d hT,
    show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by simp, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem straightPath_mem_open_ball (d : ℕ) [NeZero d] {T : ℝ} (hT : 0 < T) :
    straightPath d T ∈ cmOpenUnitBall d T := by
  refine ⟨straightPath_mem_cameronMartin d T, ?_⟩
  rw [cmNormSq_straightPath d hT]
  simp

theorem straightPath_mem_closed_ball (d : ℕ) [NeZero d] {T : ℝ} (hT : 0 < T) :
    straightPath d T ∈ cmClosedUnitBall d T :=
  ⟨straightPath_mem_cameronMartin d T, (straightPath_mem_open_ball d hT).2.le⟩

theorem schilderRate_straightPath_ne_zero (d : ℕ) [NeZero d] {T : ℝ} (hT : 0 < T) :
    schilderRate d T (straightPath d T) ≠ 0 := by
  rw [schilderRate_straightPath d hT]
  simp

/-- **Main theorem (closed ball).** For every dimension `d ≥ 1` and horizon `T > 0`, it is false
that for all paths `ω ∈ C₀([0,T]; ℝ^d)`, the Schilder rate vanishes iff `ω` lies in the closed
Cameron–Martin unit ball. -/
theorem schilder_rigidity_false (d : ℕ) [NeZero d] (T : ℝ) (hT : 0 < T) :
    ¬ ∀ ω ∈ PathSpace d T, (schilderRate d T ω = 0 ↔ ω ∈ cmClosedUnitBall d T) := by
  intro h
  exact schilderRate_straightPath_ne_zero d hT
    ((h _ (straightPath_mem_pathSpace d T)).2 (straightPath_mem_closed_ball d hT))

/-- **Main theorem (open ball).** Same with the open Cameron–Martin unit ball. -/
theorem schilder_rigidity_false_open (d : ℕ) [NeZero d] (T : ℝ) (hT : 0 < T) :
    ¬ ∀ ω ∈ PathSpace d T, (schilderRate d T ω = 0 ↔ ω ∈ cmOpenUnitBall d T) := by
  intro h
  exact schilderRate_straightPath_ne_zero d hT
    ((h _ (straightPath_mem_pathSpace d T)).2 (straightPath_mem_open_ball d hT))

end C2805
