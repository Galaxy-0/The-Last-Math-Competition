import Mathlib

/-!
# Conjecture 00000003891 (ghost inverse problem well-posedness) is false

Statement: "The recursion recovering Witt components from a ghost sequence always has a unique
solution, and ghost sequences making component p-adic valuations unbounded form a measure-zero
closed set in the compact topology."

We use Mathlib's p-typical Witt vectors `WittVector p R` and ghost components
`WittVector.ghostComponent n x = sum_{i <= n} p^i x_i^(p^(n-i))` (`ghost_formula`).
Ghost sequences live in the compact space `ℕ → ℤ_[p]` (product topology), for every prime `p`.

* Reading A (components in `ℤ_[p]`): the ghost sequence `(0,1,0,0,...)` has no preimage.
* Reading B (components in `ℚ_[p]`): unique solvability holds (Mathlib's `ghostEquiv`), but every
  ghost sequence with `‖w 1 - w 0 ^ p‖ = 1` has `v(x_n) = -(1 + p + ... + p^(n-1))` for `n >= 1`,
  so the unbounded-valuation set contains a nonempty open set and has positive measure for every
  measure that is positive on nonempty open sets (e.g. every additive Haar measure).
* Reading C ("unbounded" = unbounded above, with or without counting zero components as `+∞`):
  the set is not closed in `ℕ → ℤ_[p]`, nor relatively closed in the ghost image of `𝕎 ℤ_[p]`.
* Literal displayed formula `w_n = sum_{i <= n} x_i^(p^i)`: `(0,p,0,...)` has no `ℚ_[p]` solution.

Valuation convention: `Padic.valuation` has `valuation 0 = 0`; all sets below either exclude
zero components or count them as `+∞` explicitly, so this convention is never used.
-/

open Finset

namespace C3891

variable (p : ℕ) [hp : Fact p.Prime]

/-- Mathlib's ghost component is the standard Witt polynomial `sum_{i<=n} p^i x_i^(p^(n-i))`. -/
theorem ghost_formula {R : Type*} [CommRing R] (x : WittVector p R) (n : ℕ) :
    WittVector.ghostComponent n x =
      ∑ i ∈ range (n + 1), (p : R) ^ i * x.coeff i ^ p ^ (n - i) := by
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial]

noncomputable instance invP : Invertible (p : ℚ_[p]) :=
  invertibleOfNonzero (Nat.cast_ne_zero.2 hp.out.ne_zero)

/-- The unique Witt vector over `ℚ_[p]` whose ghost sequence is `w` (via `WittVector.ghostEquiv`). -/
noncomputable def cvec (w : ℕ → ℤ_[p]) : WittVector p ℚ_[p] :=
  (WittVector.ghostEquiv p ℚ_[p]).symm (fun n => (w n : ℚ_[p]))

/-- The Witt components (over `ℚ_[p]`) recovered from the ghost sequence `w ∈ ℤ_p^ℕ`. -/
noncomputable def comps (w : ℕ → ℤ_[p]) : ℕ → ℚ_[p] := (cvec p w).coeff

theorem ghostMap_cvec (w : ℕ → ℤ_[p]) :
    WittVector.ghostMap (cvec p w) = fun n => (w n : ℚ_[p]) :=
  (WittVector.ghostEquiv p ℚ_[p]).apply_symm_apply _

theorem comps_spec (w : ℕ → ℤ_[p]) (n : ℕ) :
    ∑ i ∈ range (n + 1), (p : ℚ_[p]) ^ i * comps p w i ^ p ^ (n - i) = w n := by
  have h := congrFun (ghostMap_cvec p w) n
  rw [WittVector.ghostMap_apply, ghost_formula] at h
  exact h

/-- Uniqueness: any `ℚ_[p]`-Witt vector with ghost sequence `w` equals `cvec p w`. -/
theorem cvec_unique (w : ℕ → ℤ_[p]) (x : WittVector p ℚ_[p])
    (hx : WittVector.ghostMap x = fun n => (w n : ℚ_[p])) : x = cvec p w := by
  unfold cvec
  rw [← hx]
  exact ((WittVector.ghostEquiv p ℚ_[p]).symm_apply_apply x).symm

/-- For a ghost sequence of an integral Witt vector, the recovered components are its own. -/
theorem comps_ghost (x : WittVector p ℤ_[p]) :
    comps p (WittVector.ghostMap x) = fun n => (x.coeff n : ℚ_[p]) := by
  have hy : WittVector.ghostMap (WittVector.mk p (fun n => (x.coeff n : ℚ_[p]))) =
      fun n => ((WittVector.ghostMap x n : ℤ_[p]) : ℚ_[p]) := by
    funext n
    simp only [WittVector.ghostMap_apply, ghost_formula, WittVector.coeff_mk]
    change _ = PadicInt.Coe.ringHom _
    simp [map_sum, map_mul, map_pow, map_natCast]
    rfl
  have := cvec_unique p _ _ hy
  unfold comps
  rw [← this, WittVector.coeff_mk]

/-- The ghost sequence `(0, 1, 0, 0, ...)`. -/
noncomputable def e1 : ℕ → ℤ_[p] := fun n => if n = 1 then 1 else 0

/-- Reading A: `(0,1,0,...)` is not the ghost sequence of any Witt vector over `ℤ_[p]`. -/
theorem e1_not_ghost (x : WittVector p ℤ_[p]) : WittVector.ghostMap x ≠ e1 p := by
  intro hx
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  simp [WittVector.ghostMap_apply, ghost_formula, e1, Finset.sum_range_succ] at h0 h1
  rw [h0, zero_pow hp.out.ne_zero, zero_add] at h1
  have h := congrArg norm h1
  rw [norm_mul, PadicInt.norm_p, norm_one] at h
  have hc := PadicInt.norm_le_one (x.coeff 1)
  have hP : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have h2 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hP
  have h3 : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  nlinarith

/-- `aexp p n = 1 + p + ... + p^(n-1) = (p^n - 1)/(p - 1)`. -/
def aexp : ℕ → ℕ
  | 0 => 0
  | n + 1 => p * aexp n + 1

lemma aexp_ge (n : ℕ) : n ≤ aexp p n := by
  induction n with
  | zero => simp [aexp]
  | succ n ih =>
    have := hp.out.two_le
    simp only [aexp]
    nlinarith

/-- Exponent comparison: the `i = n-1` term strictly dominates the others. -/
lemma key (i m : ℕ) : aexp p i * p ^ (m + 2) + m + 1 < aexp p (i + m + 1) * p := by
  have hp2 := hp.out.two_le
  induction m with
  | zero =>
    simp only [aexp, add_zero, zero_add, sq]
    nlinarith
  | succ m ih =>
    have e : aexp p (i + (m + 1) + 1) = p * aexp p (i + m + 1) + 1 := by
      rw [show i + (m + 1) + 1 = (i + m + 1) + 1 by ring]; rfl
    rw [e, pow_succ]
    nlinarith [ih]

/-- If `‖w 1 - w 0 ^ p‖ = 1` then `‖x_n‖ = p^(aexp p n)` for every `n >= 1`. -/
theorem norm_comps (w : ℕ → ℤ_[p]) (hw : ‖(w 1 - w 0 ^ p : ℤ_[p])‖ = 1) (n : ℕ) :
    ‖comps p w (n + 1)‖ = (p : ℝ) ^ aexp p (n + 1) := by
  set x := comps p w with hxdef
  have hP : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hx0 : x 0 = w 0 := by
    have := comps_spec p w 0
    simpa using this
  have hwn : ∀ n, ‖(w n : ℚ_[p])‖ ≤ 1 := fun n => PadicInt.norm_le_one (w n)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · have h1 := comps_spec p w 1
    simp [Finset.sum_range_succ] at h1
    have h2 : (p : ℚ_[p]) * x 1 = ((w 1 - w 0 ^ p : ℤ_[p]) : ℚ_[p]) := by
      push_cast
      rw [← hx0]
      linear_combination h1
    have hn := congrArg norm h2
    rw [norm_mul, Padic.norm_p, ← PadicInt.norm_def, hw] at hn
    simp only [aexp, mul_zero, zero_add, pow_one]
    field_simp at hn
    linarith
  · have hle : ∀ i ≤ n + 1, ‖x i‖ ≤ (p : ℝ) ^ aexp p i := by
      intro i hi
      rcases i with _ | i
      · simpa [aexp, hx0] using hwn 0
      · exact (ih i (by omega)).le
    have h := comps_spec p w (n + 2)
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
    simp only [show n + 2 - (n + 1) = 1 by omega, Nat.sub_self, pow_one, pow_zero] at h
    set S := ∑ i ∈ range (n + 1), (p : ℚ_[p]) ^ i * x i ^ p ^ (n + 2 - i) with hS
    set D := (p : ℚ_[p]) ^ (n + 1) * x (n + 1) ^ p with hDdef
    have hD : ‖D‖ = (p : ℝ) ^ (aexp p (n + 1) * p) / p ^ (n + 1) := by
      rw [hDdef, norm_mul, norm_pow, norm_pow, Padic.norm_p, ih n (by omega), ← pow_mul, inv_pow]
      ring
    have hSD : ‖S‖ < ‖D‖ := by
      obtain ⟨i, hi, hSi⟩ :=
        IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty (nonempty_range_add_one)
          (fun i => (p : ℚ_[p]) ^ i * x i ^ p ^ (n + 2 - i))
      refine hSi.trans_lt ?_
      have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
      rw [norm_mul, norm_pow, norm_pow, Padic.norm_p, hD, inv_pow]
      calc ((p : ℝ) ^ i)⁻¹ * ‖x i‖ ^ p ^ (n + 2 - i)
          ≤ ((p : ℝ) ^ i)⁻¹ * ((p : ℝ) ^ aexp p i) ^ p ^ (n + 2 - i) := by
            gcongr
            exact hle i (by omega)
        _ < (p : ℝ) ^ (aexp p (n + 1) * p) / p ^ (n + 1) := by
          rw [← pow_mul, inv_mul_eq_div, div_lt_div_iff₀ (by positivity) (by positivity),
            ← pow_add, ← pow_add]
          apply pow_lt_pow_right₀ hP
          have := key p i (n - i)
          rw [show n - i + 2 = n + 2 - i by omega, show i + (n - i) + 1 = n + 1 by omega] at this
          generalize aexp p i * p ^ (n + 2 - i) = A at this ⊢
          generalize aexp p (n + 1) * p = B at this ⊢
          omega
    have hwD : ‖(w (n + 2) : ℚ_[p])‖ < ‖D‖ := by
      refine (hwn _).trans_lt ?_
      rw [hD, one_lt_div (by positivity)]
      apply pow_lt_pow_right₀ hP
      have := aexp_ge p (n + 1)
      have := hp.out.two_le
      nlinarith
    have hxeq : (p : ℚ_[p]) ^ (n + 2) * x (n + 2) = ((w (n + 2) : ℚ_[p]) + -S) + -D := by
      linear_combination h
    have hR : ‖(w (n + 2) : ℚ_[p]) + -S‖ < ‖-D‖ := by
      rw [norm_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hwD (by rwa [norm_neg]))
    have hfin := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hR.ne
    rw [← hxeq, max_eq_right hR.le, norm_neg, norm_mul, norm_pow, Padic.norm_p, hD] at hfin
    have e : aexp p (n + 1 + 1) = p * aexp p (n + 1) + 1 := rfl
    have hx : ‖x (n + 2)‖ = (p : ℝ) ^ (n + 2) * ((p : ℝ) ^ (aexp p (n + 1) * p) / p ^ (n + 1)) := by
      rw [← hfin, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hp0.ne', one_pow, one_mul]
    rw [hx, e, mul_comm p (aexp p (n + 1)), pow_succ _ (aexp p (n + 1) * p),
      show n + 2 = (n + 1) + 1 from rfl, pow_succ _ (n + 1)]
    field_simp

lemma val_of_norm {y : ℚ_[p]} {k : ℤ} (hy : y ≠ 0) (h : ‖y‖ = (p : ℝ) ^ k) :
    y.valuation = -k := by
  have hP : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have h2 := Padic.norm_eq_zpow_neg_valuation hy
  rw [h] at h2
  have : k = -y.valuation := zpow_right_injective₀ (by linarith : (0 : ℝ) < p) hP.ne' h2
  omega

/-- Hence `x_n ≠ 0` and `v(x_n) = -(p^n - 1)/(p - 1)` for every `n >= 1`. -/
theorem comps_ne_zero_val (w : ℕ → ℤ_[p]) (hw : ‖(w 1 - w 0 ^ p : ℤ_[p])‖ = 1) (n : ℕ) :
    comps p w (n + 1) ≠ 0 ∧ (comps p w (n + 1)).valuation = -(aexp p (n + 1) : ℤ) := by
  have hn := norm_comps p w hw n
  have hne : comps p w (n + 1) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    have : (0 : ℝ) < (p : ℝ) ^ aexp p (n + 1) := pow_pos (by exact_mod_cast hp.out.pos) _
    linarith
  exact ⟨hne, val_of_norm p hne (by rw [hn, zpow_natCast])⟩

/-- Ghost sequences whose (nonzero) component valuations are unbounded below. -/
def UnbddBelow : Set (ℕ → ℤ_[p]) :=
  {w | ∀ M : ℤ, ∃ n, comps p w n ≠ 0 ∧ (comps p w n).valuation < M}

/-- Ghost sequences whose (nonzero) component valuations are unbounded in absolute value. -/
def Unbdd : Set (ℕ → ℤ_[p]) :=
  {w | ∀ M : ℤ, ∃ n, comps p w n ≠ 0 ∧ M < |(comps p w n).valuation|}

/-- Ghost sequences whose nonzero component valuations are unbounded above. -/
def UnbddAbove : Set (ℕ → ℤ_[p]) :=
  {w | ∀ M : ℤ, ∃ n, comps p w n ≠ 0 ∧ M < (comps p w n).valuation}

/-- Unbounded above, counting a zero component as valuation `+∞`. -/
def UnbddAboveTop : Set (ℕ → ℤ_[p]) :=
  {w | ∀ M : ℤ, ∃ n, comps p w n = 0 ∨ M < (comps p w n).valuation}

theorem unbddBelow_subset_unbdd : UnbddBelow p ⊆ Unbdd p := by
  intro w hw M
  obtain ⟨n, hn, hv⟩ := hw (-M)
  exact ⟨n, hn, by rw [lt_abs]; right; omega⟩

theorem unbddAbove_subset_top : UnbddAbove p ⊆ UnbddAboveTop p := by
  intro w hw M
  obtain ⟨n, -, hv⟩ := hw M
  exact ⟨n, Or.inr hv⟩

/-- The nonempty open set `{w | ‖w 1 - w 0 ^ p‖ = 1}`. -/
def U : Set (ℕ → ℤ_[p]) := {w | ‖w 1 - w 0 ^ p‖ = 1}

theorem isOpen_U : IsOpen (U p) := by
  have : U p = (fun w : ℕ → ℤ_[p] => w 1 - w 0 ^ p) ⁻¹' Metric.sphere 0 1 := by
    ext w; simp [U]
  rw [this]
  exact (IsUltrametricDist.isOpen_sphere _ one_ne_zero).preimage
    ((continuous_apply 1).sub ((continuous_apply 0).pow p))

theorem e1_mem_U : e1 p ∈ U p := by
  simp [U, e1, zero_pow hp.out.ne_zero]

theorem U_subset : U p ⊆ UnbddBelow p := by
  intro w hw M
  obtain ⟨hne, hv⟩ := comps_ne_zero_val p w hw (-M).toNat
  refine ⟨(-M).toNat + 1, hne, ?_⟩
  rw [hv]
  have := aexp_ge p ((-M).toNat + 1)
  omega

/-- Reading B: every set containing `UnbddBelow p` has nonzero measure for every measure
(on any σ-algebra) that is positive on nonempty open sets. -/
theorem measure_ne_zero {m : MeasurableSpace (ℕ → ℤ_[p])} (μ : MeasureTheory.Measure (ℕ → ℤ_[p]))
    [μ.IsOpenPosMeasure] {T : Set (ℕ → ℤ_[p])} (hT : UnbddBelow p ⊆ T) : μ T ≠ 0 := by
  intro h
  exact (isOpen_U p).measure_ne_zero μ ⟨e1 p, e1_mem_U p⟩
    (MeasureTheory.measure_mono_null ((U_subset p).trans hT) h)

/-- The Borel σ-algebra on `ℕ → ℤ_[p]` (Mathlib has no `MeasurableSpace ℤ_[p]` instance). -/
noncomputable instance : MeasurableSpace (ℕ → ℤ_[p]) := borel _
instance : BorelSpace (ℕ → ℤ_[p]) := ⟨rfl⟩

/-- The Haar probability measure on the compact group `ℕ → ℤ_[p]`. -/
noncomputable def haarP : MeasureTheory.Measure (ℕ → ℤ_[p]) :=
  MeasureTheory.Measure.addHaarMeasure ⊤

instance : (haarP p).IsAddHaarMeasure := MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure _

instance : MeasureTheory.IsProbabilityMeasure (haarP p) :=
  ⟨by simpa [haarP, TopologicalSpace.PositiveCompacts.coe_top] using
    MeasureTheory.Measure.addHaarMeasure_self (G := ℕ → ℤ_[p]) (K₀ := ⊤)⟩

/-- Reading B for every additive Haar measure (in particular `haarP p`). -/
theorem haar_ne_zero (μ : MeasureTheory.Measure (ℕ → ℤ_[p])) [μ.IsAddHaarMeasure]
    {T : Set (ℕ → ℤ_[p])} (hT : UnbddBelow p ⊆ T) : μ T ≠ 0 :=
  measure_ne_zero p μ hT

/-- `x^(k)_n = 1` for `n < k` and `p^n` for `n >= k`. -/
noncomputable def xk (k : ℕ) : WittVector p ℤ_[p] :=
  WittVector.mk p (fun n => if n < k then 1 else (p : ℤ_[p]) ^ n)

noncomputable def xone : WittVector p ℤ_[p] := WittVector.mk p (fun _ => 1)

noncomputable def wk (k : ℕ) : ℕ → ℤ_[p] := WittVector.ghostMap (xk p k)

noncomputable def wstar : ℕ → ℤ_[p] := WittVector.ghostMap (xone p)

/-- `ghost(x^(k)) → ghost(1,1,1,...)` in the product topology. -/
theorem tendsto_wk : Filter.Tendsto (wk p) Filter.atTop (nhds (wstar p)) := by
  rw [tendsto_pi_nhds]
  intro n
  apply tendsto_atTop_of_eventually_const (i₀ := n + 1)
  intro k hk
  simp only [wk, wstar, WittVector.ghostMap_apply, ghost_formula, xk, xone, WittVector.coeff_mk]
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_pos (by simp at hi; omega)]

/-- Each `ghost(x^(k))` has component valuations unbounded above. -/
theorem wk_mem (k : ℕ) : wk p k ∈ UnbddAbove p := by
  intro M
  refine ⟨max k (M.toNat + 1), ?_⟩
  rw [wk, comps_ghost]
  simp only [xk, WittVector.coeff_mk]
  rw [if_neg (by omega)]
  push_cast
  refine ⟨pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero), ?_⟩
  rw [Padic.valuation_pow, Padic.valuation_p]
  omega

/-- The limit `ghost(1,1,1,...)` has all component valuations `0`. -/
theorem wstar_not_mem : wstar p ∉ UnbddAboveTop p := by
  intro h
  obtain ⟨n, hn⟩ := h 0
  rw [wstar, comps_ghost] at hn
  simp [xone] at hn

/-- The ghost image of `𝕎 ℤ_[p]` in `ℕ → ℤ_[p]`. -/
def ghostImage : Set (ℕ → ℤ_[p]) :=
  Set.range (WittVector.ghostMap : WittVector p ℤ_[p] → ℕ → ℤ_[p])

/-- Reading C: no set between `UnbddAbove` and `UnbddAboveTop` is closed. -/
theorem not_closed {T : Set (ℕ → ℤ_[p])} (h1 : UnbddAbove p ⊆ T) (h2 : T ⊆ UnbddAboveTop p) :
    ¬ IsClosed T := fun hT => wstar_not_mem p (h2 (hT.mem_of_tendsto (tendsto_wk p)
      (Filter.Eventually.of_forall fun k => h1 (wk_mem p k))))

/-- Reading C inside any subspace containing the ghost image of `𝕎 ℤ_[p]`. -/
theorem not_closed_in {A : Set (ℕ → ℤ_[p])} (hA : ghostImage p ⊆ A) {T : Set (ℕ → ℤ_[p])}
    (h1 : UnbddAbove p ⊆ T) (h2 : T ⊆ UnbddAboveTop p) :
    ¬ IsClosed ((Subtype.val : A → ℕ → ℤ_[p]) ⁻¹' T) := by
  intro hT
  have hmem : ∀ k, wk p k ∈ A := fun k => hA ⟨xk p k, rfl⟩
  have hs : wstar p ∈ A := hA ⟨xone p, rfl⟩
  have ht : Filter.Tendsto (fun k => (⟨wk p k, hmem k⟩ : A)) Filter.atTop (nhds ⟨wstar p, hs⟩) :=
    tendsto_subtype_rng.2 (tendsto_wk p)
  exact wstar_not_mem p (h2 (hT.mem_of_tendsto ht
    (Filter.Eventually.of_forall fun k => h1 (wk_mem p k))))

/-- On the ghost image the recursion has a unique integral solution. -/
theorem ghost_injective_Zp : Function.Injective (WittVector.ghostMap : WittVector p ℤ_[p] → ℕ → ℤ_[p]) := by
  intro x y hxy
  have h := congrArg (comps p) hxy
  rw [comps_ghost, comps_ghost] at h
  ext n
  exact Subtype.ext (congrFun h n)

/-- The literal displayed formula `w_n = sum_{i <= n} x_i^(p^i)`. -/
def litGhost {R : Type*} [CommRing R] (x : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ range (n + 1), x i ^ p ^ i

noncomputable def ep : ℕ → ℤ_[p] := fun n => if n = 1 then (p : ℤ_[p]) else 0

/-- Literal reading: `(0, p, 0, ...)` has no solution over `ℚ_[p]` (hence none over `ℤ_[p]`). -/
theorem lit_no_solution (x : ℕ → ℚ_[p]) : litGhost p x ≠ fun n => (ep p n : ℚ_[p]) := by
  intro hx
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  simp [litGhost, ep, Finset.sum_range_succ] at h0 h1
  rw [h0, zero_add] at h1
  have h2 := congrArg Padic.valuation h1
  rw [Padic.valuation_pow, Padic.valuation_p] at h2
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  rcases le_or_gt (x 1).valuation 0 with hv | hv <;> nlinarith

/-- Main theorem, for every prime `p`: (A) over `ℤ_[p]` the recursion is not always solvable;
(B) over `ℚ_[p]` it is uniquely solvable, but the unbounded-below (hence the unbounded) valuation
set has nonzero measure for every open-positive measure; (C) the unbounded-above set (either zero
convention) is not closed, in `ℕ → ℤ_[p]` or in the ghost image; (L) the literal formula is not
always solvable over `ℚ_[p]`. -/
theorem main_theorem :
    (¬ ∀ w : ℕ → ℤ_[p], ∃! x : WittVector p ℤ_[p], WittVector.ghostMap x = w) ∧
    (∀ w : ℕ → ℤ_[p], ∃! x : WittVector p ℚ_[p],
      WittVector.ghostMap x = fun n => (w n : ℚ_[p])) ∧
    (∀ (m : MeasurableSpace (ℕ → ℤ_[p])) (μ : @MeasureTheory.Measure (ℕ → ℤ_[p]) m),
      μ.IsOpenPosMeasure → ∀ T : Set (ℕ → ℤ_[p]), UnbddBelow p ⊆ T → μ T ≠ 0) ∧
    UnbddBelow p ⊆ Unbdd p ∧
    (∀ T : Set (ℕ → ℤ_[p]), UnbddAbove p ⊆ T → T ⊆ UnbddAboveTop p →
      ¬ IsClosed T ∧ ¬ IsClosed ((Subtype.val : ghostImage p → ℕ → ℤ_[p]) ⁻¹' T)) ∧
    (¬ ∀ w : ℕ → ℤ_[p], ∃ x : ℕ → ℚ_[p], litGhost p x = fun n => (w n : ℚ_[p])) := by
  refine ⟨?_, ?_, ?_, unbddBelow_subset_unbdd p, ?_, ?_⟩
  · intro h
    obtain ⟨x, hx, -⟩ := h (e1 p)
    exact e1_not_ghost p x hx
  · intro w
    exact ⟨cvec p w, ghostMap_cvec p w, fun x hx => cvec_unique p w x hx⟩
  · intro m μ hμ T hT
    exact @measure_ne_zero p hp m μ hμ T hT
  · intro T h1 h2
    exact ⟨not_closed p h1 h2, not_closed_in p subset_rfl h1 h2⟩
  · intro h
    obtain ⟨x, hx⟩ := h (ep p)
    exact lit_no_solution p x hx

end C3891
