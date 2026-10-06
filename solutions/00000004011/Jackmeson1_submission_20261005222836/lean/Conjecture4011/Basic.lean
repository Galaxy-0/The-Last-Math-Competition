import Mathlib

/-!
# Conjecture 00000004011: no Fernique-type tail bound for a linear-growth RDE

The conjecture says that the solution norm of an RDE `dY = V(Y) dX` satisfies
`P(‖Y‖ > t) ≤ 2 exp(-t^2/c)`, where `c` depends only on the growth constant of the
vector fields and the tail parameters of the driver.

We refute it for the scalar linear equation `dY = Y dX`, `Y_0 = 1`, on `[0,1]`.
The vector field `V(y) = y` has linear growth `|V y| ≤ 1 * (1 + |y|)` with growth
constant `1` (and is `1`-Lipschitz). The driver is the smooth random path
`X_t = t G` with `G` standard Gaussian, so `|X_t - X_s| = |G| |t - s|` and
`P(|G| > t) ≤ 2 exp(-t^2/2)`. For a differentiable driver the RDE is the classical
ODE `Y' = V(Y) X'`, whose unique solution on `[0,1]` is `Y_t = exp(t G)`.
Then `Y_1 - Y_0 = exp G - 1` is lognormal, and for every `c > 0` and every
threshold `T` there is `t ≥ T` with `P(N(Y) > t) > 2 exp(-t^2/c)`, for every path
functional `N` that dominates the increment `Y_1 - Y_0` on the solution paths
(for example the sup norm on `[0,1]`, which is the case formalized below; the terminal
value `|Y_1|` and the `p`-variation and Hoelder norms on `[0,1]` also dominate it).
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace C4011

/-- The growth condition with growth constant `K`: `|V y| ≤ K (1 + |y|)` for all `y`. -/
def HasLinearGrowth (V : ℝ → ℝ) (K : ℝ) : Prop := ∀ y, |V y| ≤ K * (1 + |y|)

/-- `Y` solves the RDE `dY = V(Y) dX`, `Y_0 = y₀`, on `[0,1]` for a driver `X` that is
differentiable on `[0,1]`: this is the classical (Riemann-Stieltjes) equation
`Y'(t) = V(Y t) X'(t)` on `[0,1]` (one-sided derivatives at the endpoints). -/
def IsRDESolution (V : ℝ → ℝ) (X : ℝ → ℝ) (y₀ : ℝ) (Y : ℝ → ℝ) : Prop :=
  Y 0 = y₀ ∧ ∀ t ∈ Icc (0 : ℝ) 1,
    HasDerivWithinAt Y (V (Y t) * derivWithin X (Icc 0 1) t) (Icc 0 1) t

/-- The smooth driver `X_t = t g`. -/
def linDriver (g : ℝ) : ℝ → ℝ := fun t => t * g

/-- The sup norm `sup_{t ∈ [0,1]} |y t|` of a path on `[0,1]`. -/
noncomputable def supNorm01 (y : ℝ → ℝ) : ℝ := sSup ((fun t => |y t|) '' Icc (0 : ℝ) 1)

/-! ## The equation `dY = Y dX` -/

/-- `V(y) = y` has linear growth with growth constant `1`. -/
theorem linearGrowth_id : HasLinearGrowth id 1 := by
  intro y
  simp

/-- `V(y) = y` is `1`-Lipschitz. -/
theorem lipschitz_id_field : LipschitzWith 1 (id : ℝ → ℝ) := LipschitzWith.id

/-- The driver `X_t = t g` is Lipschitz with constant `|g|`. -/
theorem linDriver_increment (g s t : ℝ) :
    |linDriver g t - linDriver g s| = |g| * |t - s| := by
  simp only [linDriver]
  rw [← sub_mul, abs_mul, mul_comm]

lemma derivWithin_linDriver (g t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    derivWithin (linDriver g) (Icc 0 1) t = g := by
  have h : HasDerivAt (fun t : ℝ => t * g) g t := by
    simpa using (hasDerivAt_id t).mul_const g
  exact h.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc zero_lt_one) t ht)

/-- Existence: `Y_t = exp(t g)` solves `dY = Y dX` with `X_t = t g`, `Y_0 = 1`. -/
theorem exp_isRDESolution (g : ℝ) :
    IsRDESolution id (linDriver g) 1 (fun t => exp (t * g)) := by
  refine ⟨by simp, fun t ht => ?_⟩
  rw [derivWithin_linDriver g t ht]
  have h := ((hasDerivAt_id t).mul_const g).exp
  simpa using h.hasDerivWithinAt

/-- Uniqueness: every solution of `dY = Y dX`, `X_t = t g`, `Y_0 = 1` equals
`exp(t g)` on `[0,1]`. -/
theorem isRDESolution_unique {g : ℝ} {Y : ℝ → ℝ}
    (hY : IsRDESolution id (linDriver g) 1 Y) :
    ∀ t ∈ Icc (0 : ℝ) 1, Y t = exp (t * g) := by
  obtain ⟨h0, hd⟩ := hY
  set f : ℝ → ℝ := fun t => Y t * exp (-(t * g)) with hfdef
  have hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f 0 (Icc 0 1) t := by
    intro t ht
    have h1 := hd t ht
    rw [derivWithin_linDriver g t ht] at h1
    have h2 : HasDerivAt (fun t => exp (-(t * g))) (exp (-(t * g)) * (-(1 * g))) t :=
      ((hasDerivAt_id t).mul_const g).neg.exp
    have h4 : HasDerivWithinAt (fun s => Y s * exp (-(s * g))) 0 (Icc 0 1) t := by
      refine (h1.mul h2.hasDerivWithinAt).congr_deriv ?_
      simp only [id_eq]
      ring
    exact h4
  have hconst := constant_of_derivWithin_zero (f := f) (a := 0) (b := 1)
    (fun t ht => (hf t ht).differentiableWithinAt)
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).derivWithin
      ((uniqueDiffOn_Icc zero_lt_one) t (Ico_subset_Icc_self ht)))
  intro t ht
  have h := hconst t ht
  simp only [hfdef, h0, zero_mul, neg_zero, exp_zero, mul_one] at h
  have he : exp (-(t * g)) * exp (t * g) = 1 := by rw [← exp_add]; simp
  calc Y t = Y t * exp (-(t * g)) * exp (t * g) := by rw [mul_assoc, he, mul_one]
    _ = exp (t * g) := by rw [h, one_mul]

/-! ## Gaussian tails -/

/-- Lower bound for the standard Gaussian tail: `P(G > s) ≥ φ(s+1)` for `s ≥ 0`. -/
lemma gaussian_tail_lower (s : ℝ) (hs : 0 ≤ s) :
    ENNReal.ofReal (gaussianPDFReal 0 1 (s + 1)) ≤ gaussianReal 0 1 (Ioi s) := by
  calc ENNReal.ofReal (gaussianPDFReal 0 1 (s + 1))
      ≤ ENNReal.ofReal (∫ x in Ioc s (s + 1), gaussianPDFReal 0 1 x) := by
        apply ENNReal.ofReal_le_ofReal
        have h := setIntegral_ge_of_const_le_real (μ := volume) (s := Ioc s (s + 1))
          (c := gaussianPDFReal 0 1 (s + 1)) (f := gaussianPDFReal 0 1) measurableSet_Ioc
          (by simp) ?_ ((integrable_gaussianPDFReal 0 1).integrableOn)
        · simpa [Measure.real, Real.volume_Ioc] using h
        · intro x hx
          simp only [gaussianPDFReal]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply exp_le_exp.mpr
          have hx1 : 0 < x := lt_of_le_of_lt hs hx.1
          have hx2 : x ≤ s + 1 := hx.2
          have : (x - 0) ^ 2 ≤ (s + 1 - 0) ^ 2 := by nlinarith
          have h2 : (0 : ℝ) < 2 * ((1 : ℝ≥0) : ℝ) := by simp
          rw [div_le_div_iff_of_pos_right h2]
          linarith
    _ = gaussianReal 0 1 (Ioc s (s + 1)) :=
        (gaussianReal_apply_eq_integral 0 one_ne_zero _).symm
    _ ≤ gaussianReal 0 1 (Ioi s) := measure_mono Ioc_subset_Ioi_self

lemma subgaussian_id : HasSubgaussianMGF id 1 (gaussianReal 0 1) :=
  ⟨fun t => by simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t,
   fun t => by rw [mgf_id_gaussianReal]; simp⟩

/-- The driver has Gaussian tails: `P(|G| > t) ≤ 2 exp(-t^2/2)` for `t ≥ 0`. -/
theorem driver_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G : Ω → ℝ) (hG : Measurable G) (hlaw : P.map G = gaussianReal 0 1)
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | t < |G ω|} ≤ ENNReal.ofReal (2 * exp (-t ^ 2 / 2)) := by
  have hmeas : MeasurableSet {x : ℝ | t < |x|} :=
    measurableSet_lt measurable_const measurable_abs
  have hP : P {ω | t < |G ω|} = gaussianReal 0 1 {x : ℝ | t < |x|} := by
    rw [← hlaw, Measure.map_apply hG hmeas]; rfl
  have hsub : {x : ℝ | t < |x|} ⊆ {x | t ≤ id x} ∪ {x | t ≤ (-id) x} := by
    intro x hx
    simp only [mem_ofPred_eq, mem_union, id, Pi.neg_apply] at hx ⊢
    rcases le_or_gt 0 x with h | h
    · left; rw [abs_of_nonneg h] at hx; linarith
    · right; rw [abs_of_neg h] at hx; linarith
  have e1 := subgaussian_id.measure_ge_le ht
  have e2 := subgaussian_id.neg.measure_ge_le ht
  simp only [NNReal.coe_one, mul_one] at e1 e2
  rw [hP]
  calc gaussianReal 0 1 {x : ℝ | t < |x|}
      ≤ gaussianReal 0 1 ({x | t ≤ id x} ∪ {x | t ≤ (-id) x}) := measure_mono hsub
    _ ≤ gaussianReal 0 1 {x | t ≤ id x} + gaussianReal 0 1 {x | t ≤ (-id) x} :=
        measure_union_le _ _
    _ = ENNReal.ofReal ((gaussianReal 0 1).real {x | t ≤ id x}) +
          ENNReal.ofReal ((gaussianReal 0 1).real {x | t ≤ (-id) x}) := by
        simp [Measure.real]
    _ ≤ ENNReal.ofReal (exp (-t ^ 2 / 2)) + ENNReal.ofReal (exp (-t ^ 2 / 2)) := by
        gcongr
    _ = ENNReal.ofReal (2 * exp (-t ^ 2 / 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-! ## The tail of the solution is not Fernique-type -/

/-- The elementary estimate: for `u = 1 + 20c + max T 0` and `t = exp u - 1`,
`2 exp(-t^2/c) < φ(u+1)`. -/
lemma key_estimate (c T : ℝ) (hc : 0 < c) :
    let u := 1 + 20 * c + max T 0
    2 * exp (-(exp u - 1) ^ 2 / c) < gaussianPDFReal 0 1 (u + 1) := by
  intro u
  have hT := le_max_right T 0
  have hu1 : 1 ≤ u := by simp only [u]; linarith
  have hexp := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ u)
  set t := exp u - 1 with ht
  have htu : u ^ 2 / 2 ≤ t := by rw [ht]; nlinarith
  have hu2 : 20 * c < u ^ 2 := by simp only [u] at hu1 ⊢; nlinarith
  have hbig : (u + 1) ^ 2 / 2 + 3 < t ^ 2 / c := by
    rw [lt_div_iff₀ hc]
    have h1 : (u + 1) ^ 2 / 2 + 3 ≤ 5 * u ^ 2 := by nlinarith
    have h2 : u ^ 4 / 4 ≤ t ^ 2 := by
      have : 0 ≤ u ^ 2 / 2 := by positivity
      nlinarith
    have h3 : 5 * u ^ 2 * c < u ^ 4 / 4 := by nlinarith
    nlinarith
  have hpi : √(2 * π * ((1 : ℝ≥0) : ℝ)) < 3 := by
    rw [NNReal.coe_one, mul_one, Real.sqrt_lt' (by norm_num)]
    nlinarith [Real.pi_lt_four]
  have hsq : 0 < √(2 * π * ((1 : ℝ≥0) : ℝ)) := by positivity
  have he3 : (6 : ℝ) < exp 3 := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3); nlinarith
  have hlt : exp 3 * exp (-t ^ 2 / c) < exp (-(u + 1 - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) := by
    rw [← exp_add, exp_lt_exp, NNReal.coe_one, sub_zero, neg_div, neg_div]
    linarith
  simp only [gaussianPDFReal]
  rw [inv_mul_eq_div, lt_div_iff₀ hsq]
  have hpos : 0 < exp (-t ^ 2 / c) := exp_pos _
  nlinarith

/-- **Main theorem.** Let `G` be a standard Gaussian random variable on a probability space
`(Ω, P)`, let the driver be `X_t = t G`, and let `Y ω` be any solution of
`dY = Y dX`, `Y_0 = 1` on `[0,1]` (vector field `V(y) = y`, growth constant `1`).
Let `N` be any path functional with `Y_1 - Y_0 ≤ N(Y)` on the solution paths.
Then for every `c > 0` and every threshold `T` there is `t ≥ T` with
`P(N(Y) > t) > 2 exp(-t^2/c)`. -/
theorem tail_not_fernique {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G : Ω → ℝ) (hG : Measurable G) (hlaw : P.map G = gaussianReal 0 1)
    (Y : Ω → ℝ → ℝ) (hY : ∀ ω, IsRDESolution id (linDriver (G ω)) 1 (Y ω))
    (N : (ℝ → ℝ) → ℝ) (hN : ∀ ω, Y ω 1 - Y ω 0 ≤ N (Y ω)) :
    ∀ c : ℝ, 0 < c → ∀ T : ℝ, ∃ t ≥ T,
      ENNReal.ofReal (2 * exp (-t ^ 2 / c)) < P {ω | t < N (Y ω)} := by
  intro c hc T
  have key := key_estimate c T hc
  set u : ℝ := 1 + 20 * c + max T 0 with hu
  have hT := le_max_right T 0
  have hT' := le_max_left T 0
  have hexp := Real.add_one_le_exp u
  refine ⟨exp u - 1, by linarith, ?_⟩
  have hsub : {ω | G ω ∈ Ioi u} ⊆ {ω | exp u - 1 < N (Y ω)} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_Ioi] at hω ⊢
    have h1 := isRDESolution_unique (hY ω) 1 ⟨zero_le_one, le_rfl⟩
    have h0 := (hY ω).1
    have h := hN ω
    rw [h1, h0, one_mul] at h
    have : exp u < exp (G ω) := exp_lt_exp.mpr hω
    linarith
  have hP : P {ω | G ω ∈ Ioi u} = gaussianReal 0 1 (Ioi u) := by
    rw [← hlaw, Measure.map_apply hG measurableSet_Ioi]; rfl
  calc ENNReal.ofReal (2 * exp (-(exp u - 1) ^ 2 / c))
      < ENNReal.ofReal (gaussianPDFReal 0 1 (u + 1)) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (gaussianPDFReal_pos _ _ _ one_ne_zero)]
        exact key
    _ ≤ gaussianReal 0 1 (Ioi u) := gaussian_tail_lower u (by linarith)
    _ = P {ω | G ω ∈ Ioi u} := hP.symm
    _ ≤ P {ω | exp u - 1 < N (Y ω)} := measure_mono hsub

/-- **The conjectured bound fails.** Under the hypotheses of `tail_not_fernique`, there is
no constant `c > 0` with `P(N(Y) > t) ≤ 2 exp(-t^2/c)` for all `t ≥ 0`. -/
theorem no_fernique_constant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G : Ω → ℝ) (hG : Measurable G) (hlaw : P.map G = gaussianReal 0 1)
    (Y : Ω → ℝ → ℝ) (hY : ∀ ω, IsRDESolution id (linDriver (G ω)) 1 (Y ω))
    (N : (ℝ → ℝ) → ℝ) (hN : ∀ ω, Y ω 1 - Y ω 0 ≤ N (Y ω)) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      P {ω | t < N (Y ω)} ≤ ENNReal.ofReal (2 * exp (-t ^ 2 / c)) := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨t, ht, hlt⟩ := tail_not_fernique P G hG hlaw Y hY N hN c hc 0
  exact absurd (hbound t ht) (not_le.mpr hlt)

/-- On a solution path, `Y_1 - Y_0` is at most the sup norm on `[0,1]`. -/
lemma increment_le_supNorm01 {g : ℝ} {y : ℝ → ℝ} (hy : IsRDESolution id (linDriver g) 1 y) :
    y 1 - y 0 ≤ supNorm01 y := by
  have hcont : ContinuousOn y (Icc 0 1) := fun t ht => (hy.2 t ht).continuousWithinAt
  have hbdd : BddAbove ((fun t => |y t|) '' Icc (0 : ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hcont.abs).bddAbove
  have h1 : |y 1| ≤ supNorm01 y := le_csSup hbdd ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  rw [hy.1]
  linarith [le_abs_self (y 1)]

/-- **Sup-norm version.** With `‖Y‖ = sup_{t ∈ [0,1]} |Y_t|`, no `c > 0` gives
`P(‖Y‖ > t) ≤ 2 exp(-t^2/c)` for all `t ≥ 0`. -/
theorem no_fernique_constant_supNorm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G : Ω → ℝ) (hG : Measurable G) (hlaw : P.map G = gaussianReal 0 1)
    (Y : Ω → ℝ → ℝ) (hY : ∀ ω, IsRDESolution id (linDriver (G ω)) 1 (Y ω)) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      P {ω | t < supNorm01 (Y ω)} ≤ ENNReal.ofReal (2 * exp (-t ^ 2 / c)) :=
  no_fernique_constant P G hG hlaw Y hY supNorm01 (fun ω => increment_le_supNorm01 (hY ω))

/-- The hypotheses are satisfiable: on `(ℝ, N(0,1))` with `G = id` and
`Y ω t = exp(t ω)`, all assumptions of `no_fernique_constant_supNorm` hold. -/
theorem concrete_instance :
    (∀ ω : ℝ, IsRDESolution id (linDriver ω) 1 (fun t => exp (t * ω))) ∧
    (gaussianReal 0 1).map (id : ℝ → ℝ) = gaussianReal 0 1 ∧
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      gaussianReal 0 1 {ω | t < supNorm01 (fun s => exp (s * ω))} ≤
        ENNReal.ofReal (2 * exp (-t ^ 2 / c)) :=
  ⟨exp_isRDESolution, Measure.map_id,
   no_fernique_constant_supNorm (gaussianReal 0 1) id measurable_id Measure.map_id
     (fun ω t => exp (t * ω)) exp_isRDESolution⟩

end C4011
