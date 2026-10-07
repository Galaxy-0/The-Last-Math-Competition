import Mathlib

/-!
# Conjecture 00000001870: the third cumulant of `Tr U` for Haar-random `U ∈ U(N)`

The conjecture claims that the third cumulant of the trace of a Haar (CUE) random unitary
`N × N` matrix decays like `c₃ / N` with `c₃ = 2πi/3 ≠ 0`, the exponent `1` being exact.

We build the objects: `U(N) = Matrix.unitaryGroup (Fin N) ℂ` with the subspace topology of
`Matrix (Fin N) (Fin N) ℂ`, its Borel σ-algebra, a proof that it is compact, and the Haar
probability measure `haarU N = haarMeasure ⊤` (Mathlib's Haar measure normalized so that the
whole group has mass `1`). The third (joint) cumulant is defined from moments.

Since `-1 ∈ U(N)` and Haar measure is invariant under `U ↦ (-1) * U = -U`, every function that
is odd under `U ↦ -U` (such as `Tr U`, `conj (Tr U)`, `Re (Tr U)`, `Im (Tr U)`) has odd
moments zero, hence every third cumulant built from them vanishes, for every `N`.
So `κ₃(N) = 0` for all `N`, which is not asymptotic to `c / N^α` for any `c ≠ 0`, `α : ℝ`.
-/

open MeasureTheory Filter Topology Asymptotics

noncomputable section

namespace C1870

/-- The unitary group `U(N)`, as Mathlib's `Matrix.unitaryGroup (Fin N) ℂ`. -/
abbrev UN (N : ℕ) := Matrix.unitaryGroup (Fin N) ℂ

/-- Borel σ-algebra on `U(N)` (topology: subspace of `Matrix (Fin N) (Fin N) ℂ ≅ ℂ^(N×N)`). -/
instance (N : ℕ) : MeasurableSpace (UN N) := borel _
instance (N : ℕ) : BorelSpace (UN N) := ⟨rfl⟩

/-- `U(N)` is a compact subset of the matrix space: it is closed and entrywise bounded by 1. -/
theorem isCompact_unitaryGroup (N : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  have hK : IsCompact (Set.univ.pi (fun _ : Fin N => Set.univ.pi fun _ : Fin N =>
      Metric.closedBall (0 : ℂ) 1) : Set (Matrix (Fin N) (Fin N) ℂ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset ?_ ?_
  · exact isClosed_unitary (R := Matrix (Fin N) (Fin N) ℂ)
  · intro U hU i _ j _
    simpa using entry_norm_bound_of_unitary hU i j

instance (N : ℕ) : CompactSpace (UN N) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup N)

/-- The Haar probability measure on `U(N)` (the CUE): Mathlib's Haar measure normalized on the
whole compact group `⊤`. -/
def haarU (N : ℕ) : Measure (UN N) := Measure.haarMeasure ⊤

instance (N : ℕ) : (haarU N).IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _

instance (N : ℕ) : IsProbabilityMeasure (haarU N) :=
  ⟨by simpa [haarU, TopologicalSpace.PositiveCompacts.coe_top] using
    Measure.haarMeasure_self (G := UN N) (K₀ := ⊤)⟩

/-- The trace `Tr U` of a unitary matrix. -/
def trU {N : ℕ} (U : UN N) : ℂ := Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)

theorem continuous_trU (N : ℕ) : Continuous (trU : UN N → ℂ) :=
  continuous_subtype_val.matrix_trace

/-- Sanity check: every moment `E[(Tr U)^a (conj Tr U)^b]` is a genuine (integrable) integral,
since `Tr` is continuous on the compact group `U(N)` and `haarU N` is finite. -/
theorem integrable_trU_moment (N a b : ℕ) :
    Integrable (fun U => trU U ^ a * star (trU U) ^ b) (haarU N) :=
  (((continuous_trU N).pow a).mul ((continuous_star.comp (continuous_trU N)).pow b)
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Joint third cumulant of three `𝕜`-valued random variables under `μ`, from moments:
`κ(X,Y,Z) = E[XYZ] - E[XY]E[Z] - E[XZ]E[Y] - E[YZ]E[X] + 2 E[X]E[Y]E[Z]`. -/
def cumulant3 {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜] (μ : Measure Ω)
    (X Y Z : Ω → 𝕜) : 𝕜 :=
  (∫ ω, X ω * Y ω * Z ω ∂μ) - (∫ ω, X ω * Y ω ∂μ) * (∫ ω, Z ω ∂μ)
    - (∫ ω, X ω * Z ω ∂μ) * (∫ ω, Y ω ∂μ) - (∫ ω, Y ω * Z ω ∂μ) * (∫ ω, X ω ∂μ)
    + 2 * (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ) * (∫ ω, Z ω ∂μ)

/-- The third cumulant of a single variable is `E[X³] - 3 E[X²] E[X] + 2 E[X]³`. -/
theorem cumulant3_self {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜] (μ : Measure Ω)
    (X : Ω → 𝕜) : cumulant3 μ X X X =
      (∫ ω, X ω ^ 3 ∂μ) - 3 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, X ω ∂μ) + 2 * (∫ ω, X ω ∂μ) ^ 3 := by
  simp only [cumulant3, pow_succ, pow_zero, one_mul]
  ring

/-- If `μ` is invariant under a map `σ` and `f ∘ σ = -f`, then `∫ f dμ = 0`
(no integrability needed: for non-integrable `f` both sides are `0` by convention anyway). -/
theorem integral_eq_zero_of_odd {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {μ : Measure Ω}
    {σ : Ω → Ω} (hσ : ∀ f : Ω → 𝕜, ∫ ω, f (σ ω) ∂μ = ∫ ω, f ω ∂μ) {f : Ω → 𝕜}
    (hf : ∀ ω, f (σ ω) = - f ω) : ∫ ω, f ω ∂μ = 0 := by
  have h := hσ f
  simp only [hf, integral_neg] at h
  have : (2 : 𝕜) * ∫ ω, f ω ∂μ = 0 := by linear_combination -h
  simpa using this

/-- **Abstract vanishing.** If `μ` is invariant under `σ` and `X, Y, Z` are odd under `σ`,
then the joint third cumulant `κ(X,Y,Z)` vanishes. -/
theorem cumulant3_eq_zero_of_odd {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    {μ : Measure Ω} {σ : Ω → Ω} (hσ : ∀ f : Ω → 𝕜, ∫ ω, f (σ ω) ∂μ = ∫ ω, f ω ∂μ)
    {X Y Z : Ω → 𝕜} (hX : ∀ ω, X (σ ω) = - X ω) (hY : ∀ ω, Y (σ ω) = - Y ω)
    (hZ : ∀ ω, Z (σ ω) = - Z ω) : cumulant3 μ X Y Z = 0 := by
  have h3 : ∫ ω, X ω * Y ω * Z ω ∂μ = 0 :=
    integral_eq_zero_of_odd hσ (fun ω => by rw [hX, hY, hZ]; ring)
  simp only [cumulant3, h3, integral_eq_zero_of_odd hσ hX, integral_eq_zero_of_odd hσ hY,
    integral_eq_zero_of_odd hσ hZ]
  ring

/-- `-1 ∈ U(N)` acts by `U ↦ -U`, and `Tr(-U) = -Tr U`. -/
theorem trU_neg_one_mul {N : ℕ} (U : UN N) : trU ((-1 : UN N) * U) = - trU U := by
  simp [trU, Unitary.coe_neg, Matrix.trace_neg]

/-- **Main vanishing theorem.** For every left-invariant measure `μ` on `U(N)` (in particular
every Haar measure, whatever its normalization) and all `ℝ`-linear functionals
`L₁, L₂, L₃ : ℂ → 𝕜` (e.g. `id`, `conj`, `Re`, `Im`), the joint third cumulant of
`L₁(Tr U), L₂(Tr U), L₃(Tr U)` is `0`, for every `N`. -/
theorem cumulant3_linear_trace_eq_zero {𝕜 : Type*} [RCLike 𝕜] (N : ℕ) (μ : Measure (UN N))
    [μ.IsMulLeftInvariant] (L₁ L₂ L₃ : ℂ →ₗ[ℝ] 𝕜) :
    cumulant3 μ (fun U => L₁ (trU U)) (fun U => L₂ (trU U)) (fun U => L₃ (trU U)) = 0 :=
  cumulant3_eq_zero_of_odd (σ := fun U => (-1 : UN N) * U)
    (fun f => integral_mul_left_eq_self f (-1 : UN N))
    (fun U => by rw [trU_neg_one_mul, map_neg]) (fun U => by rw [trU_neg_one_mul, map_neg])
    (fun U => by rw [trU_neg_one_mul, map_neg])

/-- The same for right-invariant measures (`-1` is central, `U * (-1) = -U`). -/
theorem cumulant3_linear_trace_eq_zero_right {𝕜 : Type*} [RCLike 𝕜] (N : ℕ)
    (μ : Measure (UN N)) [μ.IsMulRightInvariant] (L₁ L₂ L₃ : ℂ →ₗ[ℝ] 𝕜) :
    cumulant3 μ (fun U => L₁ (trU U)) (fun U => L₂ (trU U)) (fun U => L₃ (trU U)) = 0 := by
  have hc : ∀ U : UN N, U * (-1 : UN N) = (-1 : UN N) * U := fun U => by simp
  exact cumulant3_eq_zero_of_odd (σ := fun U => U * (-1 : UN N))
    (fun f => integral_mul_right_eq_self f (-1 : UN N))
    (fun U => by rw [hc, trU_neg_one_mul, map_neg])
    (fun U => by rw [hc, trU_neg_one_mul, map_neg])
    (fun U => by rw [hc, trU_neg_one_mul, map_neg])

/-- The third cumulant `κ₃(N)` of `Tr U` for `U` Haar-distributed on `U(N)`:
`κ₃(N) = E[(Tr U)³] - 3 E[(Tr U)²] E[Tr U] + 2 E[Tr U]³`. -/
def kappa3 (N : ℕ) : ℂ := cumulant3 (haarU N) trU trU trU

/-- The third cumulant of `Re Tr U` under the Haar probability measure. -/
def kappa3Re (N : ℕ) : ℝ :=
  cumulant3 (haarU N) (fun U => (trU U).re) (fun U => (trU U).re) (fun U => (trU U).re)

theorem kappa3_eq_zero (N : ℕ) : kappa3 N = 0 :=
  cumulant3_linear_trace_eq_zero N (haarU N) LinearMap.id LinearMap.id LinearMap.id

theorem kappa3_eq_moments (N : ℕ) : kappa3 N = (∫ U, trU U ^ 3 ∂haarU N)
    - 3 * (∫ U, trU U ^ 2 ∂haarU N) * (∫ U, trU U ∂haarU N) + 2 * (∫ U, trU U ∂haarU N) ^ 3 :=
  cumulant3_self _ _

/-- Mixed third cumulants `κ(X,X,X̄)` and `κ(X,X̄,X̄)` of `X = Tr U` also vanish. -/
theorem mixed_cumulants_eq_zero (N : ℕ) :
    cumulant3 (haarU N) trU trU (fun U => star (trU U)) = 0 ∧
    cumulant3 (haarU N) trU (fun U => star (trU U)) (fun U => star (trU U)) = 0 :=
  ⟨cumulant3_linear_trace_eq_zero N (haarU N) LinearMap.id LinearMap.id
      (Complex.conjAe.toLinearMap.restrictScalars ℝ),
    cumulant3_linear_trace_eq_zero N (haarU N) LinearMap.id
      (Complex.conjAe.toLinearMap.restrictScalars ℝ)
      (Complex.conjAe.toLinearMap.restrictScalars ℝ)⟩

theorem kappa3Re_eq_zero (N : ℕ) : kappa3Re N = 0 :=
  cumulant3_linear_trace_eq_zero N (haarU N) Complex.reLm Complex.reLm Complex.reLm

/-- `0` is not asymptotically equivalent to an eventually nonzero sequence. -/
theorem not_isEquivalent_zero {E : Type*} [NormedAddCommGroup E] {v : ℕ → E}
    (hv : ∀ᶠ N in atTop, v N ≠ 0) : ¬ ((fun _ => (0 : E)) ~[atTop] v) := by
  intro h
  have h0 := isEquivalent_zero_iff_eventually_zero.mp h.symm
  obtain ⟨N, hN, hN'⟩ := (h0.and hv).exists
  exact hN' hN

/-- **Refutation (general form).** For no constant `c ≠ 0` and no exponent `α` does `κ₃(N)`
behave like `c · N^(-α)`, i.e. `κ₃(N) = c N^(-α) + o(N^(-α))` fails. -/
theorem kappa3_not_equivalent (c : ℂ) (hc : c ≠ 0) (α : ℝ) :
    ¬ (kappa3 ~[atTop] fun N : ℕ => c * (((N : ℝ) ^ (-α) : ℝ) : ℂ)) := by
  have : kappa3 = fun _ => 0 := funext kappa3_eq_zero
  rw [this]
  refine not_isEquivalent_zero ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hpos : (0 : ℝ) < (N : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  exact mul_ne_zero hc (by exact_mod_cast hpos.ne')

/-- The constant `c₃ = 2πi/3` from the conjecture. -/
def c3 : ℂ := 2 * Real.pi * Complex.I / 3

theorem c3_ne_zero : c3 ≠ 0 := by
  simp [c3, Complex.I_ne_zero, Real.pi_ne_zero]

/-- **Refutation of conjecture 00000001870.** The third cumulant of `Tr U` (Haar `U ∈ U(N)`)
is not `c₃/N + o(1/N)` with `c₃ = 2πi/3`; equivalently `N κ₃(N)` does not tend to `c₃`. -/
theorem conjecture_1870_false :
    ¬ (kappa3 ~[atTop] fun N : ℕ => c3 / N) ∧
    ¬ Tendsto (fun N : ℕ => (N : ℂ) * kappa3 N) atTop (𝓝 c3) := by
  refine ⟨?_, ?_⟩
  · have h := kappa3_not_equivalent c3 c3_ne_zero 1
    simpa [Real.rpow_neg_one, div_eq_mul_inv] using h
  · intro h
    have h0 : Tendsto (fun N : ℕ => (N : ℂ) * kappa3 N) atTop (𝓝 0) := by
      simp [kappa3_eq_zero]
    exact c3_ne_zero (tendsto_nhds_unique h h0)

end C1870

end
