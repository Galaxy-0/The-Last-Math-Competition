import Mathlib

/-!
# Conjecture 00000007752 is false

**Conjecture (official text).** Definition: the Böttcher coordinate `φ_c` of `f(z) = z^2 + c` is the
unique univalent analytic function near infinity with `φ_c(f(z)) = φ_c(z)^2`. Conjecture: for every
algebraic `c` (with `0` non-escaping), the ratio `φ_c(z)/z` at algebraic points `z` of sufficiently
large modulus is transcendental; and for two distinct parameters `c₁, c₂`, the ratios
`φ_{c₁}(z)/φ_{c₂}(z)` are algebraically independent at algebraic points of the common domain.

**Refutation.** For `c = -2` (`z^2 - 2 = 2 T_2(z/2)`, linearly conjugate to the Chebyshev polynomial
`T_2(x) = 2x^2 - 1`; critical orbit `0 ↦ -2 ↦ 2 ↦ 2`) the Böttcher coordinate is
`ψ(z) = z/2 · (1 + (1 - 4/z^2)^{1/2})` (principal root), i.e. `(z + s)/2` where `s = z · (1 - 4/z^2)^{1/2}`
is the square root of `z^2 - 4` asymptotic to `z` at `∞` (not the principal root of `z^2 - 4`: they
differ in sign at `z = -4`). It is the root of `w^2 - z w + 1 = 0` of modulus `> 1` and takes algebraic
values at algebraic `z`. (Also `c = 0`, `ψ = id`.) So `ψ(z)/z` is algebraic at every algebraic `z` of
large modulus.

**Normalization.** The text omits the normalization `φ(z)/z → 1`. We treat both readings:
* `IsBottcherCoord`: normalized (Milnor, Thm 9.1). We prove uniqueness: every such `φ` equals `ψ`
  near `∞` (`coord_unique`).
* `IsBottcherSolution`: unnormalized, "analytic near `∞`" meaning meromorphic at `∞` on the Riemann
  sphere. Then `1/ψ` is also a solution (so "unique" fails), and we prove every solution is `ψ^m`
  (`m ∈ ℤ`) or `0` near `∞`; in every case its values at large algebraic `z` are algebraic.
The first clause is refuted for "every Böttcher coordinate" and for "some Böttcher coordinate", for both
readings of "non-escaping" (orbit bounded / orbit not tending to `∞`). The second clause is refuted
too (`clause2_false`).

**Formal scope.** `IsBottcherSolution` assumes `MeromorphicAt` at `∞`. The existential variant
"univalent near `∞` with no condition at `∞`" is covered only mathematically (univalence rules out an
essential singularity at `∞`), not in this file.
-/

open Filter Topology Complex Bornology

namespace C7752

/-! ## Definitions -/

/-- The quadratic family `f_c(z) = z^2 + c`. -/
def fc (c z : ℂ) : ℂ := z ^ 2 + c

/-- `0` is non-escaping: its forward orbit does not tend to `∞`. -/
def ZeroNonEscaping (c : ℂ) : Prop := ¬ Tendsto (fun n : ℕ => (fc c)^[n] 0) atTop (cobounded ℂ)

/-- The orbit of `0` is bounded (`c` lies in the Mandelbrot set). -/
def ZeroOrbitBounded (c : ℂ) : Prop := ∃ B : ℝ, ∀ n : ℕ, ‖(fc c)^[n] 0‖ ≤ B

/-- The neighbourhood `{z : R < ‖z‖}` of `∞`. -/
def nbhdInf (R : ℝ) : Set ℂ := {z | R < ‖z‖}

/-- Böttcher coordinate, normalized (Milnor, *Dynamics in One Complex Variable*, Thm 9.1): analytic
and injective near `∞`, conjugates `f_c` to `w ↦ w^2`, tangent to the identity at `∞`. -/
def IsBottcherCoord (c : ℂ) (φ : ℂ → ℂ) : Prop :=
  ∃ R : ℝ, AnalyticOnNhd ℂ φ (nbhdInf R) ∧ Set.InjOn φ (nbhdInf R) ∧
    (∀ z ∈ nbhdInf R, φ (fc c z) = φ z ^ 2) ∧ Tendsto (fun z => φ z / z) (cobounded ℂ) (𝓝 1)

/-- Unnormalized reading: analytic and injective near `∞`, meromorphic at `∞` (i.e. `ζ ↦ φ(1/ζ)` is
meromorphic at `0`), with `φ ∘ f_c = φ^2`. -/
def IsBottcherSolution (c : ℂ) (φ : ℂ → ℂ) : Prop :=
  ∃ R : ℝ, AnalyticOnNhd ℂ φ (nbhdInf R) ∧ Set.InjOn φ (nbhdInf R) ∧
    (∀ z ∈ nbhdInf R, φ (fc c z) = φ z ^ 2) ∧ MeromorphicAt (fun ζ => φ ζ⁻¹) 0

/-- First clause, "for the/every Böttcher coordinate". -/
def Clause1Forall (Hyp : ℂ → Prop) (IsBC : ℂ → (ℂ → ℂ) → Prop) : Prop :=
  ∀ c : ℂ, IsAlgebraic ℚ c → Hyp c → ∀ φ : ℂ → ℂ, IsBC c φ →
    ∃ R : ℝ, ∀ z : ℂ, IsAlgebraic ℚ z → R < ‖z‖ → Transcendental ℚ (φ z / z)

/-- First clause, "for some Böttcher coordinate". -/
def Clause1Exists (Hyp : ℂ → Prop) (IsBC : ℂ → (ℂ → ℂ) → Prop) : Prop :=
  ∀ c : ℂ, IsAlgebraic ℚ c → Hyp c → ∃ φ : ℂ → ℂ, IsBC c φ ∧
    ∃ R : ℝ, ∀ z : ℂ, IsAlgebraic ℚ z → R < ‖z‖ → Transcendental ℚ (φ z / z)

/-- Second clause: the family of ratios over the algebraic points of a neighbourhood of `∞` is
algebraically independent (a one-point family: the ratio is transcendental). -/
def Clause2 (Hyp : ℂ → Prop) (IsBC : ℂ → (ℂ → ℂ) → Prop) : Prop :=
  ∀ c₁ c₂ : ℂ, IsAlgebraic ℚ c₁ → IsAlgebraic ℚ c₂ → Hyp c₁ → Hyp c₂ → c₁ ≠ c₂ →
    ∀ φ₁ φ₂ : ℂ → ℂ, IsBC c₁ φ₁ → IsBC c₂ φ₂ → ∃ R : ℝ,
      AlgebraicIndependent ℚ (fun z : {z : ℂ // IsAlgebraic ℚ z ∧ R < ‖z‖} => φ₁ z / φ₂ z)

/-! ## Rigidity: a solution of `G ∘ f_c = G^2` tending to `1` at `∞` is `1` near `∞` -/

lemma eventually_norm {p : ℂ → Prop} (h : ∀ᶠ z in cobounded ℂ, p z) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → p z := by
  obtain ⟨R, -, hR⟩ := (hasBasis_cobounded_norm (E := ℂ)).eventually_iff.1 h
  exact ⟨R, fun z hz => hR (le_of_lt hz)⟩

section Rigid
variable {c : ℂ} {R : ℝ} (grow : ∀ z, R < ‖z‖ → 2 * ‖z‖ ≤ ‖fc c z‖)
include grow

lemma tendsto_fc : Tendsto (fc c) (cobounded ℂ) (cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  refine tendsto_atTop_mono' _ ?_ (tendsto_norm_cobounded_atTop.const_mul_atTop two_pos)
  filter_upwards [(tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop R] with z hz
  exact grow z hz

lemma limit_idem {G : ℂ → ℂ} {l : ℂ} (hfe : ∀ z, R < ‖z‖ → G (fc c z) = G z ^ 2)
    (hl : Tendsto G (cobounded ℂ) (𝓝 l)) : l ^ 2 = l := by
  have h1 : Tendsto (fun z => G (fc c z)) (cobounded ℂ) (𝓝 l) := hl.comp (tendsto_fc grow)
  have h2 : Tendsto (fun z => G (fc c z)) (cobounded ℂ) (𝓝 (l ^ 2)) := by
    refine (hl.pow 2).congr' ?_
    filter_upwards [(tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop R] with z hz
    exact (hfe z hz).symm
  exact tendsto_nhds_unique h2 h1

lemma rigid {G : ℂ → ℂ} (hfe : ∀ z, R < ‖z‖ → G (fc c z) = G z ^ 2)
    (hl : Tendsto G (cobounded ℂ) (𝓝 1)) : ∃ R' : ℝ, ∀ z, R' < ‖z‖ → G z = 1 := by
  obtain ⟨R1, hR1⟩ := eventually_norm (hl.eventually (Metric.ball_mem_nhds (1 : ℂ) one_half_pos))
  refine ⟨max R R1, fun z hz => ?_⟩
  set x : ℕ → ℂ := fun k => (fc c)^[k] z
  have hx : ∀ k, max R R1 < ‖x k‖ := by
    intro k; induction k with
    | zero => simpa [x] using hz
    | succ k ih =>
      have := grow (x k) (lt_of_le_of_lt (le_max_left _ _) ih)
      simp only [x, Function.iterate_succ_apply'] at this ⊢
      linarith [norm_nonneg (x k)]
  have hsmall : ∀ k, ‖G (x k) - 1‖ < 1 / 2 := fun k => by
    simpa [dist_eq_norm] using hR1 (x k) (lt_of_le_of_lt (le_max_right _ _) (hx k))
  have hgrow : ∀ k, (3 / 2 : ℝ) ^ k * ‖G z - 1‖ ≤ ‖G (x k) - 1‖ := by
    intro k; induction k with
    | zero => simp [x]
    | succ k ih =>
      have hstep : G (x (k + 1)) - 1 = (G (x k) - 1) * (G (x k) - 1 + 2) := by
        simp only [x, Function.iterate_succ_apply']
        rw [hfe _ (lt_of_le_of_lt (le_max_left _ _) (hx k))]; ring
      have h2 : (3 / 2 : ℝ) ≤ ‖G (x k) - 1 + 2‖ := by
        have := norm_sub_norm_le (2 : ℂ) (-(G (x k) - 1))
        simp only [norm_neg, sub_neg_eq_add] at this
        rw [add_comm]; norm_num at this ⊢; linarith [hsmall k]
      rw [hstep, norm_mul, pow_succ]
      nlinarith [norm_nonneg (G (x k) - 1), norm_nonneg (G z - 1), pow_nonneg
        (by norm_num : (0 : ℝ) ≤ 3 / 2) k]
  by_contra hne
  have hpos : 0 < ‖G z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3 / 2)).eventually_gt_atTop
    (1 / (2 * ‖G z - 1‖))).exists
  have := hgrow k
  have := hsmall k
  rw [div_lt_iff₀ (by positivity)] at hk
  nlinarith

end Rigid

/-! ## Models: an explicit Böttcher coordinate `ψ` with algebraic values -/

/-- Properties of an explicit Böttcher coordinate `ψ` for `f_c` on `{R₀ < ‖z‖}`. -/
structure Model (c : ℂ) (ψ : ℂ → ℂ) (R₀ : ℝ) : Prop where
  fe : ∀ z, R₀ < ‖z‖ → ψ (fc c z) = ψ z ^ 2
  ne : ∀ z, R₀ < ‖z‖ → ψ z ≠ 0
  lim : Tendsto (fun z => ψ z / z) (cobounded ℂ) (𝓝 1)
  grow : ∀ z, R₀ < ‖z‖ → 2 * ‖z‖ ≤ ‖fc c z‖
  alg : ∀ z, IsAlgebraic ℚ z → R₀ < ‖z‖ → IsAlgebraic ℚ (ψ z)

lemma isAlgebraic_zpow {x : ℂ} (hx : IsAlgebraic ℚ x) (m : ℤ) : IsAlgebraic ℚ (x ^ m) := by
  cases m with
  | ofNat k => simpa using hx.pow k
  | negSucc k => rw [zpow_negSucc]; exact (hx.pow _).inv

variable {c : ℂ} {ψ : ℂ → ℂ} {R₀ : ℝ}

/-- If `φ ∘ f_c = φ^2` near `∞` and `φ · ψ^n → l ≠ 0`, then `φ = ψ^{-n}` near `∞`. -/
theorem Model.classify (M : Model c ψ R₀) {φ : ℂ → ℂ} {R : ℝ}
    (hfe : ∀ z ∈ nbhdInf R, φ (fc c z) = φ z ^ 2) {n : ℤ} {l : ℂ} (hl0 : l ≠ 0)
    (hl : Tendsto (fun z => φ z * ψ z ^ n) (cobounded ℂ) (𝓝 l)) :
    ∃ R' : ℝ, ∀ z, R' < ‖z‖ → φ z = ψ z ^ (-n) := by
  have grow' : ∀ z, max R R₀ < ‖z‖ → 2 * ‖z‖ ≤ ‖fc c z‖ :=
    fun z hz => M.grow z (lt_of_le_of_lt (le_max_right _ _) hz)
  have hfeG : ∀ z, max R R₀ < ‖z‖ →
      φ (fc c z) * ψ (fc c z) ^ n = (φ z * ψ z ^ n) ^ 2 := by
    intro z hz
    rw [hfe z (lt_of_le_of_lt (le_max_left _ _) hz), M.fe z (lt_of_le_of_lt (le_max_right _ _) hz),
      mul_pow, ← zpow_natCast (ψ z) 2, ← zpow_natCast (ψ z ^ n) 2, ← zpow_mul, ← zpow_mul,
      mul_comm n]
  have hl1 : l = 1 := by
    have h := limit_idem grow' hfeG hl
    have : l * (l - 1) = 0 := by linear_combination h
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hl0)
  subst hl1
  obtain ⟨R2, hR2⟩ := rigid grow' hfeG hl
  refine ⟨max R2 R₀, fun z hz => ?_⟩
  have h1 := hR2 z (lt_of_le_of_lt (le_max_left _ _) hz)
  rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h1

/-- Uniqueness: every normalized Böttcher coordinate equals `ψ` near `∞`. -/
theorem Model.coord_unique (M : Model c ψ R₀) {φ : ℂ → ℂ} (h : IsBottcherCoord c φ) :
    ∃ R : ℝ, ∀ z, R < ‖z‖ → φ z = ψ z := by
  obtain ⟨R, -, -, hfe, hlim⟩ := h
  have hl : Tendsto (fun z => φ z * ψ z ^ (-1 : ℤ)) (cobounded ℂ) (𝓝 1) := by
    have := hlim.mul (M.lim.inv₀ one_ne_zero)
    rw [inv_one, mul_one] at this
    refine this.congr' ?_
    filter_upwards [(tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop 0] with z hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 hz
    rw [zpow_neg_one, div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv, mul_assoc,
      mul_comm (ψ z)⁻¹ z, inv_mul_cancel_left₀ hz0]
  obtain ⟨R', hR'⟩ := M.classify hfe one_ne_zero hl
  exact ⟨R', fun z hz => by simpa using hR' z hz⟩

/-- Every unnormalized solution is `0` or `ψ^m` near `∞`; in all cases its values at algebraic
points of large modulus are algebraic. -/
theorem Model.solution_alg (M : Model c ψ R₀) {φ : ℂ → ℂ} (h : IsBottcherSolution c φ) :
    ∃ R : ℝ, ∀ z, IsAlgebraic ℚ z → R < ‖z‖ → IsAlgebraic ℚ (φ z) := by
  obtain ⟨R, -, -, hfe, hmero⟩ := h
  by_cases htop : meromorphicOrderAt (fun ζ => φ ζ⁻¹) 0 = ⊤
  · have h0 := tendsto_inv₀_cobounded'.eventually (meromorphicOrderAt_eq_top_iff.1 htop)
    obtain ⟨R1, hR1⟩ := eventually_norm h0
    refine ⟨R1, fun z _ hz => ?_⟩
    have := hR1 z hz; simp only [inv_inv] at this; rw [this]; exact isAlgebraic_zero
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
  obtain ⟨g, hg, hg0, hφ⟩ := (meromorphicOrderAt_eq_int_iff hmero).1 hn.symm
  have hgl : Tendsto (fun z : ℂ => g z⁻¹) (cobounded ℂ) (𝓝 (g 0)) :=
    hg.continuousAt.tendsto.comp tendsto_inv₀_cobounded
  have hl : Tendsto (fun z => φ z * ψ z ^ n) (cobounded ℂ) (𝓝 (g 0)) := by
    have := (M.lim.zpow₀ n (Or.inl one_ne_zero)).mul hgl
    rw [one_zpow, one_mul] at this
    refine this.congr' ?_
    filter_upwards [tendsto_inv₀_cobounded'.eventually hφ] with z hz
    simp only [inv_inv, sub_zero, smul_eq_mul] at hz
    rw [hz, div_eq_mul_inv, mul_zpow, inv_zpow']; ring
  obtain ⟨R', hR'⟩ := M.classify hfe hg0 hl
  refine ⟨max R' R₀, fun z hz hzR => ?_⟩
  rw [hR' z (lt_of_le_of_lt (le_max_left _ _) hzR)]
  exact isAlgebraic_zpow (M.alg z hz (lt_of_le_of_lt (le_max_right _ _) hzR)) _

/-- Normalized coordinates also have algebraic values (they equal `ψ` near `∞`). -/
theorem Model.coord_alg (M : Model c ψ R₀) {φ : ℂ → ℂ} (h : IsBottcherCoord c φ) :
    ∃ R : ℝ, ∀ z, IsAlgebraic ℚ z → R < ‖z‖ → IsAlgebraic ℚ (φ z) := by
  obtain ⟨R, hR⟩ := M.coord_unique h
  exact ⟨max R R₀, fun z hz hzR => (hR z (lt_of_le_of_lt (le_max_left _ _) hzR)).symm ▸
    M.alg z hz (lt_of_le_of_lt (le_max_right _ _) hzR)⟩

/-! ## The two explicit models -/

/-- `c = 0`: `ψ = id`. -/
theorem model0 : Model 0 id 2 where
  fe z _ := by simp [fc]
  ne z hz := by simp only [id]; exact norm_pos_iff.1 (by linarith)
  lim := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop 0] with z hz
    exact (div_self (norm_pos_iff.1 hz)).symm
  grow z hz := by simp only [fc, add_zero, norm_pow]; nlinarith
  alg z hz _ := hz

/-- `c = -2`: `ψ(z) = z/2 · (1 + (1 - 4/z^2)^{1/2})` with the principal root; this is `(z + s)/2` for the
square root `s = z · (1 - 4/z^2)^{1/2}` of `z^2 - 4` asymptotic to `z` at `∞`. -/
noncomputable def psi2 (z : ℂ) : ℂ := z / 2 * (1 + (1 - 4 / z ^ 2) ^ (2⁻¹ : ℂ))

lemma psi2_quad {z : ℂ} (hz : z ≠ 0) : psi2 z ^ 2 - z * psi2 z + 1 = 0 := by
  have ht : ((1 - 4 / z ^ 2) ^ (2⁻¹ : ℂ)) ^ 2 = 1 - 4 / z ^ 2 := cpow_ofNat_inv_pow _ 2
  have ht' : z ^ 2 * ((1 - 4 / z ^ 2) ^ (2⁻¹ : ℂ)) ^ 2 = z ^ 2 - 4 := by
    rw [ht]; field_simp
  unfold psi2; linear_combination (1 / 4 : ℂ) * ht'

lemma norm_psi2 (z : ℂ) : ‖z‖ / 2 ≤ ‖psi2 z‖ := by
  have h1 : (1 : ℝ) ≤ ‖1 + (1 - 4 / z ^ 2) ^ (2⁻¹ : ℂ)‖ := by
    refine le_trans ?_ (re_le_norm _)
    rw [add_re, one_re, cpow_inv_two_re]; linarith [Real.sqrt_nonneg ((‖1 - 4 / z ^ 2‖ +
      (1 - 4 / z ^ 2).re) / 2)]
  unfold psi2; rw [norm_mul, norm_div, Complex.norm_two]
  nlinarith [norm_nonneg z]

lemma root_unique {a w₁ w₂ : ℂ} (h₁ : w₁ ^ 2 - a * w₁ + 1 = 0) (h₂ : w₂ ^ 2 - a * w₂ + 1 = 0)
    (n₁ : 1 < ‖w₁‖) (n₂ : 1 < ‖w₂‖) : w₁ = w₂ := by
  by_contra hne
  have hs : w₁ + w₂ = a := by
    have : (w₁ - w₂) * (w₁ + w₂ - a) = 0 := by linear_combination h₁ - h₂
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne))
  have hp : w₁ * w₂ = 1 := by rw [← hs] at h₁; linear_combination -h₁
  have := congrArg norm hp
  rw [norm_mul, norm_one] at this
  nlinarith

lemma grow2 {z : ℂ} (hz : 3 < ‖z‖) : 2 * ‖z‖ ≤ ‖fc (-2) z‖ := by
  have := norm_sub_norm_le (z ^ 2) 2
  simp only [fc, norm_pow, Complex.norm_two, ← sub_eq_add_neg] at this ⊢
  nlinarith

theorem model2 : Model (-2) psi2 3 where
  fe z hz := by
    have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
    have ha := grow2 hz
    have ha0 : fc (-2) z ≠ 0 := norm_pos_iff.1 (by linarith)
    refine root_unique (psi2_quad ha0) ?_ (by linarith [norm_psi2 (fc (-2) z)]) ?_
    · have hq := psi2_quad hz0; unfold fc; linear_combination (psi2 z ^ 2 + z * psi2 z + 1) * hq
    · rw [norm_pow]; nlinarith [norm_psi2 z]
  ne z hz := norm_pos_iff.1 (by linarith [norm_psi2 z])
  lim := by
    have h4 : Tendsto (fun z : ℂ => 1 - 4 / z ^ 2) (cobounded ℂ) (𝓝 1) := by
      have := ((tendsto_inv₀_cobounded (α := ℂ)).pow 2).const_mul 4
      simpa [div_eq_mul_inv, inv_pow] using (tendsto_const_nhds (x := (1 : ℂ))).sub this
    have ht := ((continuousAt_cpow_const (b := (2⁻¹ : ℂ)) (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp
      h4)
    rw [one_cpow] at ht
    have := (ht.const_add 1).div_const 2
    norm_num at this
    refine this.congr' ?_
    filter_upwards [(tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop 0] with z hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 hz
    simp only [psi2]; field_simp
  grow z hz := grow2 hz
  alg z hz hz3 := by
    have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
    have h4 : IsAlgebraic ℚ (4 : ℂ) := by simpa using isAlgebraic_natCast (R := ℚ) (A := ℂ) 4
    have h2 : IsAlgebraic ℚ (2 : ℂ) := by simpa using isAlgebraic_natCast (R := ℚ) (A := ℂ) 2
    have hb : IsAlgebraic ℚ (1 - 4 / z ^ 2) :=
      isAlgebraic_one.sub (by rw [div_eq_mul_inv]; exact h4.mul (hz.pow 2).inv)
    have ht : IsAlgebraic ℚ ((1 - 4 / z ^ 2) ^ (2⁻¹ : ℂ)) :=
      IsAlgebraic.of_pow two_pos (by rw [cpow_ofNat_inv_pow]; exact hb)
    unfold psi2; rw [div_eq_mul_inv]; exact (hz.mul h2.inv).mul (isAlgebraic_one.add ht)

/-! ## Both models are Böttcher coordinates in both senses -/

theorem coord0 : IsBottcherCoord 0 id :=
  ⟨2, analyticOnNhd_id, Set.injOn_id _, fun z hz => model0.fe z hz, model0.lim⟩

theorem sol0 : IsBottcherSolution 0 id :=
  ⟨2, analyticOnNhd_id, Set.injOn_id _, fun z hz => model0.fe z hz, (MeromorphicAt.id 0).inv⟩

lemma slit_of_large {z : ℂ} (hz : 2 < ‖z‖) : 1 - 4 / z ^ 2 ∈ slitPlane := by
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
  have hn : ‖4 / z ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, div_lt_one (by positivity)]; norm_num; nlinarith
  rw [mem_slitPlane_iff]; left
  rw [sub_re, one_re]; linarith [re_le_norm (4 / z ^ 2)]

lemma psi2_analyticOn : AnalyticOnNhd ℂ psi2 (nbhdInf 3) := by
  intro z hz
  have hz : (3 : ℝ) < ‖z‖ := hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
  unfold psi2
  exact (analyticAt_id.div_const).mul (analyticAt_const.add ((analyticAt_const.sub
    (analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hz0))).cpow analyticAt_const
    (by simpa using slit_of_large (z := z) (by linarith))))

lemma psi2_injOn : Set.InjOn psi2 (nbhdInf 3) := by
  intro z₁ h₁ z₂ h₂ he
  have h₁ : (3 : ℝ) < ‖z₁‖ := h₁
  have h₂ : (3 : ℝ) < ‖z₂‖ := h₂
  have q₁ := psi2_quad (norm_pos_iff.1 (by linarith : (0 : ℝ) < ‖z₁‖))
  have q₂ := psi2_quad (norm_pos_iff.1 (by linarith : (0 : ℝ) < ‖z₂‖))
  have hne := model2.ne z₁ h₁
  rw [he] at q₁ hne
  have : (z₁ - z₂) * psi2 z₂ = 0 := by linear_combination q₂ - q₁
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

lemma psi2_mero : MeromorphicAt (fun ζ => psi2 ζ⁻¹) 0 := by
  have heq : (fun ζ : ℂ => psi2 ζ⁻¹) =
      fun ζ => ζ⁻¹ * (2⁻¹ * (1 + (1 - 4 * ζ ^ 2) ^ (2⁻¹ : ℂ))) := by
    funext ζ; unfold psi2; rw [inv_pow, div_inv_eq_mul]; ring
  rw [heq]
  exact (MeromorphicAt.id 0).inv.mul (analyticAt_const.mul (analyticAt_const.add
    ((analyticAt_const.sub (analyticAt_const.mul (analyticAt_id.pow 2))).cpow analyticAt_const
    (by simp)))).meromorphicAt

theorem coord2 : IsBottcherCoord (-2) psi2 :=
  ⟨3, psi2_analyticOn, psi2_injOn, fun z hz => model2.fe z hz, model2.lim⟩

theorem sol2 : IsBottcherSolution (-2) psi2 :=
  ⟨3, psi2_analyticOn, psi2_injOn, fun z hz => model2.fe z hz, psi2_mero⟩

/-- Without the normalization the solution is not unique: `1/φ` is a solution whenever `φ` is. -/
theorem sol_inv {c : ℂ} {φ : ℂ → ℂ} {R : ℝ} (ha : AnalyticOnNhd ℂ φ (nbhdInf R))
    (hi : Set.InjOn φ (nbhdInf R)) (hfe : ∀ z ∈ nbhdInf R, φ (fc c z) = φ z ^ 2)
    (hm : MeromorphicAt (fun ζ => φ ζ⁻¹) 0) (hne : ∀ z ∈ nbhdInf R, φ z ≠ 0) :
    IsBottcherSolution c (fun z => (φ z)⁻¹) :=
  ⟨R, fun z hz => (ha z hz).inv (hne z hz), fun _ h₁ _ h₂ he => hi h₁ h₂ (inv_injective he),
    fun z hz => by simp [hfe z hz], hm.inv⟩

theorem sol0_inv : IsBottcherSolution 0 (fun z => (id z)⁻¹) :=
  sol_inv (R := 2) analyticOnNhd_id (Set.injOn_id _) (fun z hz => model0.fe z hz)
    (MeromorphicAt.id 0).inv (fun z hz => model0.ne z hz)

theorem sol2_inv : IsBottcherSolution (-2) (fun z => (psi2 z)⁻¹) :=
  sol_inv psi2_analyticOn psi2_injOn (fun z hz => model2.fe z hz) psi2_mero
    (fun z hz => model2.ne z hz)

/-! ## The parameters `c = 0` and `c = -2` are in scope -/

lemma nonEscaping_of_bounded {c : ℂ} (h : ZeroOrbitBounded c) : ZeroNonEscaping c := by
  obtain ⟨B, hB⟩ := h
  intro ht
  obtain ⟨n, hn⟩ := ((tendsto_norm_atTop_iff_cobounded.2 ht).eventually_gt_atTop B).exists
  exact absurd (hB n) (not_le.2 hn)

theorem bounded0 : ZeroOrbitBounded 0 :=
  ⟨0, fun n => by rw [Function.iterate_fixed (by simp [fc])]; simp⟩

theorem bounded2 : ZeroOrbitBounded (-2) := by
  have h : ∀ n, (fc (-2))^[n] 0 = 0 ∨ (fc (-2))^[n] 0 = -2 ∨ (fc (-2))^[n] 0 = 2 := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h | h <;> rw [h] <;> norm_num [fc]
  refine ⟨2, fun n => ?_⟩
  rcases h n with h | h | h <;> rw [h] <;> simp

theorem alg2 : IsAlgebraic ℚ (-2 : ℂ) := by
  simpa using (isAlgebraic_natCast (R := ℚ) (A := ℂ) 2).neg

/-! ## Refutation -/

lemma exists_big (R : ℝ) : ∃ z : ℂ, IsAlgebraic ℚ z ∧ R < ‖z‖ := by
  refine ⟨((⌈R⌉₊ + 1 : ℕ) : ℂ), isAlgebraic_natCast _, ?_⟩
  rw [Complex.norm_natCast]; push_cast; linarith [Nat.le_ceil R]

lemma refute {Hyp : ℂ → Prop} {IsBC : ℂ → (ℂ → ℂ) → Prop} {c : ℂ} (hc : IsAlgebraic ℚ c)
    (hH : Hyp c) {φ₀ : ℂ → ℂ} (hφ₀ : IsBC c φ₀)
    (hall : ∀ φ, IsBC c φ → ∃ R : ℝ, ∀ z, IsAlgebraic ℚ z → R < ‖z‖ → IsAlgebraic ℚ (φ z)) :
    ¬ Clause1Forall Hyp IsBC ∧ ¬ Clause1Exists Hyp IsBC := by
  have key : ∀ φ, IsBC c φ → ∀ R : ℝ,
      ¬ ∀ z : ℂ, IsAlgebraic ℚ z → R < ‖z‖ → Transcendental ℚ (φ z / z) := by
    intro φ hφ R h
    obtain ⟨R', hR'⟩ := hall φ hφ
    obtain ⟨z, hz, hzR⟩ := exists_big (max R R')
    refine h z hz (lt_of_le_of_lt (le_max_left _ _) hzR) ?_
    rw [div_eq_mul_inv]; exact (hR' z hz (lt_of_le_of_lt (le_max_right _ _) hzR)).mul hz.inv
  exact ⟨fun h => by obtain ⟨R, hR⟩ := h c hc hH φ₀ hφ₀; exact key φ₀ hφ₀ R hR,
    fun h => by obtain ⟨φ, hφ, R, hR⟩ := h c hc hH; exact key φ hφ R hR⟩

/-- A model `ψ` that is a Böttcher coordinate in both senses, at an algebraic `c` with bounded
critical orbit, refutes the first clause under all eight readings. -/
theorem refuted_by_model {c : ℂ} {ψ : ℂ → ℂ} {R₀ : ℝ} (M : Model c ψ R₀) (hc : IsAlgebraic ℚ c)
    (hb : ZeroOrbitBounded c) (hco : IsBottcherCoord c ψ) (hso : IsBottcherSolution c ψ) :
    ∀ Hyp ∈ [ZeroNonEscaping, ZeroOrbitBounded], ∀ IsBC ∈ [IsBottcherCoord, IsBottcherSolution],
      ¬ Clause1Forall Hyp IsBC ∧ ¬ Clause1Exists Hyp IsBC := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro Hyp (rfl | rfl) IsBC (rfl | rfl)
  · exact refute hc (nonEscaping_of_bounded hb) hco fun φ h => M.coord_alg h
  · exact refute hc (nonEscaping_of_bounded hb) hso fun φ h => M.solution_alg h
  · exact refute hc hb hco fun φ h => M.coord_alg h
  · exact refute hc hb hso fun φ h => M.solution_alg h

/-- The monomial witness `c = 0` (`φ = id`). -/
theorem refuted_by_zero :
    ∀ Hyp ∈ [ZeroNonEscaping, ZeroOrbitBounded], ∀ IsBC ∈ [IsBottcherCoord, IsBottcherSolution],
      ¬ Clause1Forall Hyp IsBC ∧ ¬ Clause1Exists Hyp IsBC :=
  refuted_by_model model0 isAlgebraic_zero bounded0 coord0 sol0

/-- The second clause fails as well (`c₁ = 0`, `c₂ = -2`: the ratio `z / ψ(z)` is algebraic). -/
theorem clause2_false :
    ∀ Hyp ∈ [ZeroNonEscaping, ZeroOrbitBounded], ∀ IsBC ∈ [IsBottcherCoord, IsBottcherSolution],
      ¬ Clause2 Hyp IsBC := by
  have key : ∀ R : ℝ, ¬ AlgebraicIndependent ℚ
      (fun z : {z : ℂ // IsAlgebraic ℚ z ∧ R < ‖z‖} => id (z : ℂ) / psi2 z) := by
    intro R hind
    obtain ⟨z, hz, hzR⟩ := exists_big (max R 3)
    refine hind.transcendental ⟨z, hz, lt_of_le_of_lt (le_max_left _ _) hzR⟩ ?_
    show IsAlgebraic ℚ (id z / psi2 z)
    rw [div_eq_mul_inv]
    exact hz.mul (model2.alg z hz (lt_of_le_of_lt (le_max_right _ _) hzR)).inv
  have h02 : (0 : ℂ) ≠ -2 := by norm_num
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro Hyp (rfl | rfl) IsBC (rfl | rfl) h
  · obtain ⟨R, hR⟩ := h 0 (-2) isAlgebraic_zero alg2 (nonEscaping_of_bounded bounded0)
      (nonEscaping_of_bounded bounded2) h02 id psi2 coord0 coord2
    exact key R hR
  · obtain ⟨R, hR⟩ := h 0 (-2) isAlgebraic_zero alg2 (nonEscaping_of_bounded bounded0)
      (nonEscaping_of_bounded bounded2) h02 id psi2 sol0 sol2
    exact key R hR
  · obtain ⟨R, hR⟩ := h 0 (-2) isAlgebraic_zero alg2 bounded0 bounded2 h02 id psi2 coord0 coord2
    exact key R hR
  · obtain ⟨R, hR⟩ := h 0 (-2) isAlgebraic_zero alg2 bounded0 bounded2 h02 id psi2 sol0 sol2
    exact key R hR

/-- **Conjecture 00000007752 is false**, witnessed by the non-monomial parameter `c = -2`. For both
readings of "`0` non-escaping" and both readings of "Böttcher coordinate" (normalized; unnormalized
meromorphic at `∞`), neither "every" nor "some" Böttcher coordinate has transcendental ratios
`φ_c(z)/z` at all algebraic `z` of large modulus; hence the conjecture (clause 1 together with any
second clause `P`) fails. -/
theorem conjecture_7752_false (P : Prop) :
    ∀ Hyp ∈ [ZeroNonEscaping, ZeroOrbitBounded], ∀ IsBC ∈ [IsBottcherCoord, IsBottcherSolution],
      ¬ (Clause1Forall Hyp IsBC ∧ P) ∧ ¬ (Clause1Exists Hyp IsBC ∧ P) :=
  fun Hyp hH IsBC hB =>
    let h := refuted_by_model model2 alg2 bounded2 coord2 sol2 Hyp hH IsBC hB
    ⟨fun h' => h.1 h'.1, fun h' => h.2 h'.1⟩

end C7752
