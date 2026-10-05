import Mathlib

/-!
# Conjecture 00000001354: the uniform square-root-phase prime sum bound is false

For `0 < α ≤ 1` and real `x`, let `S_α(x) = Σ_{p ≤ x} e(α √p)` with `e(t) = exp(2πit)`.
The conjecture says `S_1(x) ≪ x^{1/4+ε}`, and that the same bound holds *uniformly* in
`0 < α ≤ 1` (Chinese: 一致成立).

The uniform clause is false for every `0 < ε < 3/4`. Given `x ≥ 1`, take `α = 1/(8√x) ∈ (0, 1]`.
Every phase `2π α √p` with `p ≤ x` lies in `[0, π/4]`, so `Re S_α(x) ≥ cos(π/4) π(x)`.
Chebyshev's lower bound (Mathlib's `Chebyshev.pi_ge'`) makes `π(x)` larger than any constant
times `x^{1/4+ε}` for large `x`.
-/

open Real Filter

namespace Conjecture1354

/-! ## Definitions -/

/-- The additive character `e(t) = exp(2πit)`. -/
noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * t)

/-- The dilated square-phase prime sum `S_α(x) = Σ_{p ≤ x} e(α √p)`. Here `Nat.primesLE ⌊x⌋₊` is
the finset of primes `p ≤ x`. The conjecture's square-phase prime sum is `S 1 x`. -/
noncomputable def S (α x : ℝ) : ℂ := ∑ p ∈ Nat.primesLE ⌊x⌋₊, e (α * √(p : ℝ))

/-- Clause 1: `Σ_{p ≤ x} e(√p) ≪ x^{1/4+ε}` for every `ε > 0` (implied constant and threshold may
depend on `ε`). -/
def AlphaOneClause : Prop :=
  ∀ ε > 0, ∃ C X : ℝ, ∀ x ≥ X, ‖S 1 x‖ ≤ C * x ^ ((1 : ℝ) / 4 + ε)

/-- The bound `S_α(x) ≪ x^{1/4+ε}` holding uniformly in `0 < α ≤ 1`: one constant `C` and one
threshold `X` serve every `α ∈ (0, 1]`. This is the standard meaning of a uniform `≪`/`O` bound,
and it is weaker than the usual convention, which takes `X = 2`. -/
def UniformBound (ε : ℝ) : Prop :=
  ∃ C X : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ x ≥ X, ‖S α x‖ ≤ C * x ^ ((1 : ℝ) / 4 + ε)

/-- Clause 2: the same upper bound holds uniformly after replacing `√p` by `α√p`, `0 < α ≤ 1`. -/
def UniformClause : Prop :=
  ∀ ε > 0, UniformBound ε

/-- Conjecture 00000001354: clause 1 and the uniform clause 2. -/
def Conjecture : Prop :=
  AlphaOneClause ∧ UniformClause

/-! ## The phase lower bound -/

theorem e_re (t : ℝ) : (e t).re = Real.cos (2 * π * t) := by
  have h : (2 * π * Complex.I * t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, h, Complex.exp_ofReal_mul_I_re]

/-- With `α = 1/(8√x)` every phase is in `[0, π/4]`, so `Re S_α(x) ≥ (√2/2) π(x)`. -/
theorem re_S_ge {x : ℝ} (hx : 0 < x) :
    √2 / 2 * (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (S (1 / (8 * √x)) x).re := by
  rw [S, Complex.re_sum, ← Nat.primesLE_card_eq_primeCounting]
  have hsx : 0 < √x := Real.sqrt_pos.2 hx
  calc √2 / 2 * ((Nat.primesLE ⌊x⌋₊).card : ℝ)
      = ∑ _p ∈ Nat.primesLE ⌊x⌋₊, √2 / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (e (1 / (8 * √x) * √(p : ℝ))).re := by
        apply Finset.sum_le_sum
        intro p hp
        have hpx : (p : ℝ) ≤ x :=
          le_trans (by exact_mod_cast Nat.le_of_mem_primesLE hp) (Nat.floor_le hx.le)
        have hsp : √(p : ℝ) ≤ √x := Real.sqrt_le_sqrt hpx
        have hsp0 : 0 ≤ √(p : ℝ) := Real.sqrt_nonneg _
        rw [e_re, ← Real.cos_pi_div_four]
        apply Real.cos_le_cos_of_nonneg_of_le_pi
        · positivity
        · linarith [Real.pi_pos]
        · have heq : 2 * π * (1 / (8 * √x) * √(p : ℝ)) = π / 4 * (√(p : ℝ) / √x) := by
            field_simp; ring
          rw [heq]
          have h1 : √(p : ℝ) / √x ≤ 1 := div_le_one_of_le₀ hsp hsx.le
          nlinarith [Real.pi_pos]
    _ = _ := rfl

/-! ## Chebyshev growth of `π(x)` -/

/-- For `0 < θ < 1`, `π(x)` eventually exceeds any constant times `x^θ`. -/
theorem exists_large {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (K X : ℝ) :
    ∃ x : ℝ, X ≤ x ∧ 2 ≤ x ∧ K * x ^ θ < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  set η := (1 - θ) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hηle : η ≤ 1 - η := by rw [hη]; linarith
  have ht := (tendsto_rpow_atTop hη0).eventually_gt_atTop (4 * (|K| + 2) / η)
  obtain ⟨x, hxy, hxX⟩ := (ht.and (eventually_ge_atTop (max X 2))).exists
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hxX
  refine ⟨x, le_trans (le_max_left _ _) hxX, hx2, ?_⟩
  have hx0 : 0 < x := by linarith
  set y := x ^ η with hydef
  set z := x ^ (1 - η) with hzdef
  have hy : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hz : 0 < z := Real.rpow_pos_of_pos hx0 _
  have hyz : y ≤ z := Real.rpow_le_rpow_of_exponent_le (by linarith) hηle
  have hxzy : x = z * y := by
    rw [hzdef, hydef, ← Real.rpow_add hx0]; simp
  have hθy : x ^ θ * y = z := by
    rw [hydef, hzdef, ← Real.rpow_add hx0]; congr 1; rw [hη]; ring
  set P : ℝ := (Nat.primeCounting ⌊x⌋₊ : ℝ) with hPdef
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  have hlog_pos : 0 < log x := Real.log_pos (by linarith)
  have hpi := Chebyshev.pi_ge' (by linarith : (1 : ℝ) < x)
  have hP : (x - 1) * log 2 - log (x + 2) ≤ P * log x := by
    rwa [div_le_iff₀ hlog_pos] at hpi
  have hlog_le : log x ≤ y / η := Real.log_le_rpow_div hx0.le hη0
  have hlog2 : log (x + 2) ≤ 2 * log x := by
    rw [← Real.log_rpow hx0]
    apply Real.log_le_log (by linarith)
    rw [show x ^ (2 : ℝ) = x * x by norm_num [sq]]
    nlinarith
  have hl2 : (1 : ℝ) / 2 < log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hx4 : x / 4 ≤ (x - 1) * log 2 := by nlinarith
  -- `η · log x ≤ y`
  have hηlog : η * log x ≤ y := by
    have := mul_le_mul_of_nonneg_left hlog_le hη0.le
    rwa [mul_div_cancel₀ _ hη0.ne'] at this
  -- `η · (P · log x) ≤ P · y`
  have hηP : η * (P * log x) ≤ P * y := by
    have := mul_le_mul_of_nonneg_left hηlog hP0
    linarith [this]
  -- `η x / 4 - 2 y ≤ P y`
  have key : η * x / 4 - 2 * y ≤ P * y := by
    have h1 : η * ((x - 1) * log 2 - log (x + 2)) ≤ η * (P * log x) :=
      mul_le_mul_of_nonneg_left hP hη0.le
    have h2 : η * log (x + 2) ≤ 2 * y := by
      have := mul_le_mul_of_nonneg_left hlog2 hη0.le
      linarith
    have h3 : η * (x / 4) ≤ η * ((x - 1) * log 2) := mul_le_mul_of_nonneg_left hx4 hη0.le
    nlinarith
  -- `|K| + 2 < η y / 4`
  have hyK : |K| + 2 < η * y / 4 := by
    have := hxy
    rw [div_lt_iff₀ hη0] at this
    linarith
  have hmain : K * x ^ θ * y < P * y := by
    have e1 : K * x ^ θ * y = K * z := by rw [mul_assoc, hθy]
    have e2 : K * z ≤ |K| * z := mul_le_mul_of_nonneg_right (le_abs_self K) hz.le
    have e3 : (|K| + 2) * z < η * y / 4 * z := mul_lt_mul_of_pos_right hyK hz
    have e4 : η * x / 4 = η * y / 4 * z := by rw [hxzy]; ring
    nlinarith
  exact lt_of_mul_lt_mul_right hmain hy.le

/-! ## Main theorems -/

/-- **The uniform bound fails for every `0 < ε < 3/4`.** For every `C` and `X` there are
`α ∈ (0, 1]` and `x ≥ X` (namely `α = 1/(8√x)`) with `‖S_α(x)‖ > C x^{1/4+ε}`. -/
theorem not_uniformBound {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 3 / 4) : ¬ UniformBound ε := by
  rintro ⟨C, X, h⟩
  obtain ⟨x, hxX, hx2, hbig⟩ :=
    exists_large (θ := 1 / 4 + ε) (by linarith) (by linarith) (2 * C) X
  have hx0 : 0 < x := by linarith
  have hsx : 0 < √x := Real.sqrt_pos.2 hx0
  have hsx1 : 1 ≤ √x := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hα : 1 / (8 * √x) ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one (by positivity)]; linarith
  have h1 := h _ hα x hxX
  have h2 := re_S_ge hx0
  have h3 := Complex.re_le_norm (S (1 / (8 * √x)) x)
  have hs2 : (1 : ℝ) ≤ √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hP0 : (0 : ℝ) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- The uniform clause is false. -/
theorem not_uniformClause : ¬ UniformClause := fun h =>
  not_uniformBound (ε := 1 / 4) (by norm_num) (by norm_num) (h _ (by norm_num))

/-- **Main theorem.** Conjecture 00000001354, read with the uniform clause, is false. -/
theorem conjecture1354_false : ¬ Conjecture := fun h => not_uniformClause h.2

end Conjecture1354
