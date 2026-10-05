import Mathlib

/-!
# Conjecture 00000002251 (difference operator): the kernel claim is false

Conjecture (verbatim): "The difference operator Δ_c f = f(z+c) − f(z). Conjecture: The kernel of
Δ_c has dimension 1, and the spectrum of Δ_c on meromorphic function spaces (differences of
difference polynomials) is explicit of the {2 sin(kc/2)} type (difference spectrum)."

Reading: `Δ_c` acts on the complex vector space `MeroFun` of all meromorphic functions `ℂ → ℂ`
(Mathlib's `Meromorphic`: meromorphic at every point of `ℂ`), a submodule of `ℂ → ℂ`, and
`(Δ_c f) z = f (z + c) - f z` is Mathlib's forward difference `fwdDiff c f`.  Mathlib convention:
a meromorphic function is an honest function `ℂ → ℂ` (with some value at each pole); the germ-class
version is covered by `indep_mod_codiscrete`.  Dimension is `Module.rank` (a cardinal).

Results.
* `rank_ker_diffOp_gt_one`: for every `c : ℂ`, `1 < Module.rank ℂ (ker Δ_c)`; the kernel is not
  one-dimensional.  Witnesses: `1` and `exp (2πi z / c)` for `c ≠ 0`; `1` and `z` for `c = 0`.
* `indep_mod_codiscrete`: the two witnesses for `c ≠ 0` (both `c`-periodic at every point) stay
  independent when functions agreeing off a discrete set are identified.
* `spectrum_diffOp`: for `c ≠ 0`, the spectrum of `Δ_c` (in the algebra `Module.End ℂ MeroFun`)
  is exactly `{-1}ᶜ`, and every `μ ≠ -1` is an eigenvalue (`hasEigenvalue_diffOp`);
  `spectrum_not_countable`: this set is uncountable, so it is not the image of a countable index
  set; in particular it is not `{2 sin(kc/2) : k ∈ ℤ}` (`spectrum_ne_sine_set`).
-/

open Complex Filter Topology
open scoped Real

namespace Tlmc2251

/-- The complex vector space of meromorphic functions `ℂ → ℂ`, as a submodule of all functions. -/
def MeroFun : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | Meromorphic f}
  add_mem' hf hg := Meromorphic.add hf hg
  zero_mem' := Meromorphic.const (0 : ℂ)
  smul_mem' a _ hf := Meromorphic.const_smul hf a

lemma mem_MeroFun {f : ℂ → ℂ} : f ∈ MeroFun ↔ Meromorphic f := Iff.rfl

/-- The difference operator `Δ_c f = f(· + c) - f` (Mathlib's `fwdDiff c`) on `MeroFun`. -/
def diffOp (c : ℂ) : Module.End ℂ MeroFun where
  toFun f := ⟨fwdDiff c f.1,
    (Meromorphic.meromorphic_fun_comp_add_const_iff_meromorphic.2 (mem_MeroFun.1 f.2)).sub
      (mem_MeroFun.1 f.2)⟩
  map_add' f g := by ext z; simp only [fwdDiff, Submodule.coe_add, Pi.add_apply]; ring
  map_smul' a f := by
    ext z; simp only [fwdDiff, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] lemma diffOp_apply (c : ℂ) (f : MeroFun) (z : ℂ) :
    (diffOp c f : ℂ → ℂ) z = (f : ℂ → ℂ) (z + c) - (f : ℂ → ℂ) z := rfl

/-- The constant function `1`. -/
def oneMF : MeroFun := ⟨fun _ => 1, Meromorphic.const (1 : ℂ)⟩

/-- The identity function `z ↦ z`. -/
def idMF : MeroFun := ⟨fun z => z, fun _ => analyticAt_id.meromorphicAt⟩

/-- The exponential `z ↦ exp (b z)`, an entire function. -/
noncomputable def expMF (b : ℂ) : MeroFun :=
  ⟨fun z => exp (b * z), fun x => (by fun_prop : AnalyticAt ℂ (fun z => exp (b * z)) x).meromorphicAt⟩

@[simp] lemma oneMF_apply (z : ℂ) : (oneMF : ℂ → ℂ) z = 1 := rfl
@[simp] lemma idMF_apply (z : ℂ) : (idMF : ℂ → ℂ) z = z := rfl
@[simp] lemma expMF_apply (b z : ℂ) : (expMF b : ℂ → ℂ) z = exp (b * z) := rfl

/-- The witnesses `exp (b z)` are entire. -/
theorem expMF_differentiable (b : ℂ) : Differentiable ℂ (fun z => exp (b * z)) := by fun_prop

/-- ... and of exponential type: `‖exp (b z)‖ ≤ exp (‖b‖ ‖z‖)`. -/
theorem expMF_growth (b z : ℂ) : ‖exp (b * z)‖ ≤ Real.exp (‖b‖ * ‖z‖) := by
  rw [Complex.norm_exp, ← norm_mul]
  exact Real.exp_le_exp.2 (Complex.re_le_norm _)

/-- `exp (b z)` is an eigenfunction: `Δ_c exp(b·) = (exp (b c) - 1) • exp(b·)`. -/
theorem diffOp_expMF (c b : ℂ) : diffOp c (expMF b) = (exp (b * c) - 1) • expMF b := by
  ext z
  simp only [diffOp_apply, expMF_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_add,
    Complex.exp_add]
  ring

lemma diffOp_oneMF (c : ℂ) : diffOp c oneMF = 0 := by ext z; simp

lemma diffOp_zero (f : MeroFun) : diffOp 0 f = 0 := by ext z; simp

/-- The frequency `2πi / c`. -/
noncomputable def freq (c : ℂ) : ℂ := 2 * π * I / c

lemma freq_mul {c : ℂ} (hc : c ≠ 0) : freq c * c = 2 * π * I := by
  unfold freq; field_simp

/-- For `c ≠ 0`, `exp (2πi z / c)` is `c`-periodic, i.e. lies in `ker Δ_c`. -/
theorem diffOp_expMF_freq {c : ℂ} (hc : c ≠ 0) : diffOp c (expMF (freq c)) = 0 := by
  rw [diffOp_expMF, freq_mul hc, Complex.exp_two_pi_mul_I, sub_self, zero_smul]

/-- Value of the periodic witness at `c / 2`: `exp (πi) = -1`. -/
lemma exp_freq_half {c : ℂ} (hc : c ≠ 0) : exp (freq c * (c / 2)) = -1 := by
  have : freq c * (c / 2) = π * I := by rw [mul_div_assoc', freq_mul hc]; ring
  rw [this, Complex.exp_pi_mul_I]

/-- Key computation: two kernel elements that are linearly independent (stated in the
coefficient-comparison form, which is linear independence of the pair). -/
theorem kernel_pair (c : ℂ) : ∃ u v : MeroFun, diffOp c u = 0 ∧ diffOp c v = 0 ∧
    ∀ s t s' t' : ℂ, s • u + t • v = s' • u + t' • v → s = s' ∧ t = t' := by
  by_cases hc : c = 0
  · subst hc
    refine ⟨oneMF, idMF, diffOp_zero _, diffOp_zero _, fun s t s' t' h => ?_⟩
    have h0 := congrArg (fun F : MeroFun => (F : ℂ → ℂ) 0) h
    have h1 := congrArg (fun F : MeroFun => (F : ℂ → ℂ) 1) h
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      oneMF_apply, idMF_apply, mul_zero, mul_one, add_zero] at h0 h1
    exact ⟨h0, by linear_combination h1 - h0⟩
  · refine ⟨oneMF, expMF (freq c), diffOp_oneMF c, diffOp_expMF_freq hc, fun s t s' t' h => ?_⟩
    have h0 := congrArg (fun F : MeroFun => (F : ℂ → ℂ) 0) h
    have h1 := congrArg (fun F : MeroFun => (F : ℂ → ℂ) (c / 2)) h
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      oneMF_apply, expMF_apply, mul_zero, Complex.exp_zero, mul_one, exp_freq_half hc] at h0 h1
    exact ⟨by linear_combination (1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1,
      by linear_combination (1 / 2 : ℂ) * h0 - (1 / 2 : ℂ) * h1⟩

/-- **Main theorem.** For every `c : ℂ`, the kernel of `Δ_c` on meromorphic functions has rank
greater than one (indeed at least two). -/
theorem rank_ker_diffOp_gt_one (c : ℂ) : 1 < Module.rank ℂ (LinearMap.ker (diffOp c)) := by
  obtain ⟨u, v, hu, hv, huv⟩ := kernel_pair c
  have hli : LinearIndependent ℂ
      ![(⟨u, LinearMap.mem_ker.2 hu⟩ : LinearMap.ker (diffOp c)), ⟨v, LinearMap.mem_ker.2 hv⟩] := by
    refine LinearIndependent.pair_iffₛ.2 fun s t s' t' hst => ?_
    exact huv s t s' t' (congrArg Subtype.val hst)
  have h2 := hli.cardinal_le_rank
  rw [Cardinal.mk_fin] at h2
  exact lt_of_lt_of_le (by norm_num) h2

/-- The conjecture's kernel clause is false for every `c`. -/
theorem kernel_not_dim_one (c : ℂ) : Module.rank ℂ (LinearMap.ker (diffOp c)) ≠ 1 :=
  (rank_ker_diffOp_gt_one c).ne'

/-- `1` and `exp (2πi z / c)` stay independent when functions agreeing off a discrete set are
identified: a combination vanishing on a codiscrete set has zero coefficients. -/
theorem indep_mod_codiscrete {c : ℂ} (hc : c ≠ 0) (s t : ℂ)
    (h : ∀ᶠ z in codiscrete ℂ, s * 1 + t * exp (freq c * z) = 0) : s = 0 ∧ t = 0 := by
  have hval : ∀ x : ℂ, s * 1 + t * exp (freq c * x) = 0 := by
    intro x
    have hx : ∀ᶠ z in 𝓝[≠] x, s * 1 + t * exp (freq c * z) = 0 := by
      have := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h) x (Set.mem_univ x)
      rw [Set.compl_univ, Set.union_empty] at this
      exact this
    have hcont : Continuous (fun z : ℂ => s * 1 + t * exp (freq c * z)) := by fun_prop
    exact tendsto_nhds_unique ((hcont.tendsto x).mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hx.mono fun z hz => hz.symm))
  have h0 := hval 0
  have h1 := hval (c / 2)
  rw [mul_zero, Complex.exp_zero] at h0
  rw [exp_freq_half hc] at h1
  exact ⟨by linear_combination (1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1,
    by linear_combination (1 / 2 : ℂ) * h0 - (1 / 2 : ℂ) * h1⟩

/-- For `c ≠ 0`, every `μ ≠ -1` is an eigenvalue of `Δ_c`, with eigenfunction `exp (b z)`,
`b = log (1 + μ) / c`. -/
theorem hasEigenvalue_diffOp {c : ℂ} (hc : c ≠ 0) {μ : ℂ} (hμ : μ ≠ -1) :
    Module.End.HasEigenvalue (diffOp c) μ := by
  have h1 : (1 + μ) ≠ 0 := fun h => hμ (by linear_combination h)
  have hb : exp (log (1 + μ) / c * c) = 1 + μ := by rw [div_mul_cancel₀ _ hc, exp_log h1]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := expMF (log (1 + μ) / c)) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, diffOp_expMF, hb, add_sub_cancel_left]
  · intro h0
    have := congrArg (fun F : MeroFun => (F : ℂ → ℂ) 0) h0
    simp at this

/-- `-1` is not in the spectrum: `-1 - Δ_c` is `f ↦ -f(· + c)`, which is bijective. -/
theorem neg_one_not_mem_spectrum (c : ℂ) : (-1 : ℂ) ∉ spectrum ℂ (diffOp c) := by
  rw [spectrum.mem_iff, not_not, Module.End.isUnit_iff]
  have key : ∀ (f : MeroFun) (z : ℂ),
      ((algebraMap ℂ (Module.End ℂ MeroFun) (-1) - diffOp c) f : ℂ → ℂ) z = -(f : ℂ → ℂ) (z + c) := by
    intro f z
    simp
    ring
  constructor
  · intro f g hfg
    ext z
    have := congrArg (fun F : MeroFun => (F : ℂ → ℂ) (z - c)) hfg
    simp only [key, sub_add_cancel, neg_inj] at this
    exact this
  · intro g
    refine ⟨⟨fun z => -(g : ℂ → ℂ) (z - c),
      (Meromorphic.meromorphic_fun_comp_sub_const_iff_meromorphic.2 (mem_MeroFun.1 g.2)).neg⟩, ?_⟩
    ext z
    rw [key]
    simp

/-- For `c ≠ 0`, the spectrum of `Δ_c` on meromorphic functions is exactly `ℂ \ {-1}`. -/
theorem spectrum_diffOp {c : ℂ} (hc : c ≠ 0) : spectrum ℂ (diffOp c) = {-1}ᶜ := by
  ext μ
  constructor
  · intro h hμ
    rw [Set.mem_singleton_iff] at hμ
    exact neg_one_not_mem_spectrum c (hμ ▸ h)
  · intro hμ
    exact (hasEigenvalue_diffOp hc hμ).mem_spectrum

/-- This spectrum is uncountable, so it is not a set `{2 sin(kc/2) : k ∈ K}` with `K` countable. -/
theorem spectrum_not_countable {c : ℂ} (hc : c ≠ 0) : ¬ (spectrum ℂ (diffOp c)).Countable := by
  rw [spectrum_diffOp hc]
  intro h
  apply not_countable_complex
  rw [← Set.compl_union_self {(-1 : ℂ)}]
  exact h.union (Set.countable_singleton _)

/-- In particular the spectrum is not `{2 sin(kc/2) : k ∈ ℤ}`. -/
theorem spectrum_ne_sine_set {c : ℂ} (hc : c ≠ 0) :
    spectrum ℂ (diffOp c) ≠ Set.range (fun k : ℤ => 2 * Complex.sin (k * c / 2)) := fun h =>
  spectrum_not_countable hc (h ▸ Set.countable_range _)

/-- Summary: the kernel clause fails for every `c`, and for `c ≠ 0` the spectrum is `ℂ \ {-1}`,
which is uncountable. -/
theorem conjecture_2251_refuted :
    (∀ c : ℂ, 1 < Module.rank ℂ (LinearMap.ker (diffOp c))) ∧
    (∀ c : ℂ, c ≠ 0 → spectrum ℂ (diffOp c) = {-1}ᶜ ∧ ¬ (spectrum ℂ (diffOp c)).Countable) :=
  ⟨rank_ker_diffOp_gt_one, fun _ hc => ⟨spectrum_diffOp hc, spectrum_not_countable hc⟩⟩

end Tlmc2251
