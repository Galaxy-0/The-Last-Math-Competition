import Mathlib

/-!
# Conjecture 00000001857 (refutation)

Statement: for a random 3-regular graph `G` on `n` vertices, the spanning-tree count `τ(G)` is
asymptotically `c₃ ^ n` with
`c₃ = ((√3 - 1)/2)^2 * exp ((∫ log (3 - 2 cos θ) dθ) / (4π))`, and the numerical limit is
`1.175…`.

We formalize:
* `tau G`: the number of spanning trees of `G` (subgraphs `T ≤ G` on the full vertex set that
  are trees), and `tau_eq_card_edgeSets`: the same number counts the edge subsets of `G` whose
  edge-induced spanning graph is a tree.
* `c3On a b`: the closed form with the integral over `[a, b]`; `c3 = c3On 0 (2π)`.
* `c3On_lt_one`: for every window `a ≤ b ≤ a + 4π` (so `[0, 2π]`, `[-π, π]`, `[0, π]`, ...)
  the closed form is `< 1`; in particular it is not `1.175…` (`c3On_not_numerical`).
* `integral_eq`, `c3_eq`, `c3_bounds`: on `[0, 2π]`, exactly
  `∫₀^{2π} log (3 - 2 cos θ) dθ = 2π log ((3+√5)/2)` and `c₃ = (2-√3)/2 · (1+√5)/2 ∈ (0.2167, 0.2169)`.
* `tau_ratio_tendsto_atTop`, `not_tau_isBigO`, `not_tau_rpow_tendsto`: for ANY sequence of
  connected finite graphs with vertex count `→ ∞`, `τ / c₃ⁿ → ∞`, `τ ≠ O(c₃ⁿ)`, and
  `τ^(1/n) ↛ c₃`, because `τ ≥ 1` (`one_le_tau`) while `c₃ⁿ → 0`.
* `prob_good_le_prob_disconnected`: for the uniform random 3-regular graph on `Fin n`, the
  probability that `|τ/c₃ⁿ - 1| < ε` (`ε ≤ 1`) is at most the probability of being
  disconnected, for all large `n`; `not_prob_good_tendsto_one` derives the failure of
  `τ ~ c₃ⁿ` in probability from the (cited, hypothesised) a.a.s. connectivity.
-/

open Real Filter Topology Asymptotics

namespace C1857

/-! ## The spanning-tree count -/

/-- `τ(G)`: the number of spanning trees of `G`, i.e. of subgraphs `T ≤ G` with the same
vertex set that are trees. -/
noncomputable def tau {V : Type*} (G : SimpleGraph V) : ℕ :=
  Nat.card {T : SimpleGraph V // T ≤ G ∧ T.IsTree}

/-- `τ(G)` equals the number of edge subsets `s ⊆ E(G)` such that the spanning graph with edge
set `s` is a tree. -/
theorem tau_eq_card_edgeSets {V : Type*} (G : SimpleGraph V) :
    tau G = Nat.card {s : Set (Sym2 V) //
      s ⊆ G.edgeSet ∧ (SimpleGraph.fromEdgeSet s).IsTree} := by
  unfold tau
  refine Nat.card_congr
    { toFun := fun T => ⟨T.1.edgeSet, SimpleGraph.edgeSet_subset_edgeSet.mpr T.2.1, by
        rw [SimpleGraph.fromEdgeSet_edgeSet]; exact T.2.2⟩
      invFun := fun s => ⟨SimpleGraph.fromEdgeSet s.1, ?_, s.2.2⟩
      left_inv := fun T => by ext1; exact SimpleGraph.fromEdgeSet_edgeSet T.1
      right_inv := fun s => ?_ }
  · intro v w h
    rw [SimpleGraph.fromEdgeSet_adj] at h
    exact (SimpleGraph.mem_edgeSet G).mp (s.2.1 h.1)
  · refine Subtype.ext ?_
    simp only [SimpleGraph.edgeSet_fromEdgeSet]
    exact Set.ext fun e => ⟨fun h => h.1,
      fun he => ⟨he, fun hd => G.not_isDiag_of_mem_edgeSet (s.2.1 he) hd⟩⟩

/-- Every connected finite graph has at least one spanning tree. -/
theorem one_le_tau {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) :
    1 ≤ tau G := by
  obtain ⟨T, hle, hT⟩ := hG.exists_isTree_le
  have hne : Nonempty {T : SimpleGraph V // T ≤ G ∧ T.IsTree} := ⟨⟨T, hle, hT⟩⟩
  exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨hne, inferInstance⟩)

/-! ## The closed form -/

/-- The closed form with the integral taken over `[a, b]`. -/
noncomputable def c3On (a b : ℝ) : ℝ :=
  ((√3 - 1) / 2) ^ 2 * Real.exp ((∫ θ in a..b, Real.log (3 - 2 * Real.cos θ)) / (4 * π))

/-- The closed form with the integral over the full period `[0, 2π]`. -/
noncomputable def c3 : ℝ := c3On 0 (2 * π)

lemma arg_pos (θ : ℝ) : 0 < 3 - 2 * Real.cos θ := by
  have := Real.cos_le_one θ; linarith

lemma integrand_continuous : Continuous fun θ : ℝ => Real.log (3 - 2 * Real.cos θ) :=
  Continuous.log (by fun_prop) (fun θ => (arg_pos θ).ne')

lemma integrand_le (θ : ℝ) : Real.log (3 - 2 * Real.cos θ) ≤ Real.log 5 := by
  refine Real.log_le_log (arg_pos θ) ?_
  have := Real.neg_one_le_cos θ; linarith

lemma integral_le {a b : ℝ} (hab : a ≤ b) :
    (∫ θ in a..b, Real.log (3 - 2 * Real.cos θ)) ≤ (b - a) * Real.log 5 := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    (integrand_continuous.intervalIntegrable a b)
    ((continuous_const : Continuous fun _ : ℝ => Real.log 5).intervalIntegrable a b)
    (fun θ _ => integrand_le θ)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using h

lemma sqrt3_bounds : 1.732 < √3 ∧ √3 < 2 := by
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h0 := Real.sqrt_nonneg 3
  constructor <;> nlinarith

lemma prefactor_eq : ((√3 - 1) / 2) ^ 2 = (2 - √3) / 2 := by
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  linear_combination h3 / 4

lemma prefactor_pos : 0 < ((√3 - 1) / 2) ^ 2 := by
  rw [prefactor_eq]; linarith [sqrt3_bounds.2]

lemma c3On_pos (a b : ℝ) : 0 < c3On a b :=
  mul_pos prefactor_pos (Real.exp_pos _)

/-- For every integration window of length at most `4π` the closed form is `< 1`. -/
theorem c3On_lt_one {a b : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 4 * π) : c3On a b < 1 := by
  have hpi := Real.pi_pos
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hI : (∫ θ in a..b, Real.log (3 - 2 * Real.cos θ)) / (4 * π) ≤ Real.log 5 := by
    rw [div_le_iff₀ (by positivity)]
    have := integral_le hab
    nlinarith
  have hE : Real.exp ((∫ θ in a..b, Real.log (3 - 2 * Real.cos θ)) / (4 * π)) ≤ 5 := by
    calc _ ≤ Real.exp (Real.log 5) := Real.exp_le_exp.mpr hI
      _ = 5 := Real.exp_log (by norm_num)
  unfold c3On
  rw [prefactor_eq]
  have hs := sqrt3_bounds
  have hp : 0 < (2 - √3) / 2 := by linarith
  calc (2 - √3) / 2 * _ ≤ (2 - √3) / 2 * 5 := mul_le_mul_of_nonneg_left hE hp.le
    _ < 1 := by linarith

/-- Hence the closed form is not the claimed numerical value `1.175…` (any real whose decimal
expansion starts `1.175`), for any window `a ≤ b ≤ a + 4π`. -/
theorem c3On_not_numerical {a b : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 4 * π) :
    c3On a b ∉ Set.Ico (1.175 : ℝ) 1.176 := by
  intro h
  have := c3On_lt_one hab hlen
  linarith [h.1]

/-- The two standard full-period windows. -/
theorem c3_lt_one : c3 < 1 ∧ c3On (-π) π < 1 := by
  have hpi := Real.pi_pos
  exact ⟨c3On_lt_one (by linarith) (by linarith), c3On_lt_one (by linarith) (by linarith)⟩

/-! ## The asymptotic clause fails for every sequence of connected graphs -/

section Deterministic

variable {V : ℕ → Type*} [∀ k, Finite (V k)] (G : ∀ k, SimpleGraph (V k))

/-- For any `0 < c < 1` and any sequence of connected finite graphs whose vertex count
`n_k = |V k|` tends to infinity, `τ(G_k) / c^(n_k) → ∞`. -/
theorem tau_ratio_tendsto_atTop {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hN : Tendsto (fun k => Nat.card (V k)) atTop atTop) (hG : ∀ k, (G k).Connected) :
    Tendsto (fun k => (tau (G k) : ℝ) / c ^ Nat.card (V k)) atTop atTop := by
  have h1 : Tendsto (fun k => c ^ Nat.card (V k)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨(tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1).comp hN,
      Eventually.of_forall fun k => pow_pos hc0 _⟩
  refine tendsto_atTop_mono (fun k => ?_) h1.inv_tendsto_nhdsGT_zero
  have hτ : (1 : ℝ) ≤ tau (G k) := by exact_mod_cast one_le_tau (hG k)
  simp only [Pi.inv_apply, div_eq_mul_inv]
  exact le_mul_of_one_le_left (inv_nonneg.mpr (pow_pos hc0 _).le) hτ

/-- Main theorem (asymptotic clause, ratio reading): with `c₃` the closed form over `[0, 2π]`
(or any window of length `≤ 4π`), `τ(G_k) / c₃^(n_k)` does not tend to `1`; it tends to `∞`. -/
theorem not_tau_asymp {a b : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 4 * π)
    (hN : Tendsto (fun k => Nat.card (V k)) atTop atTop) (hG : ∀ k, (G k).Connected) :
    Tendsto (fun k => (tau (G k) : ℝ) / c3On a b ^ Nat.card (V k)) atTop atTop ∧
    ¬ Tendsto (fun k => (tau (G k) : ℝ) / c3On a b ^ Nat.card (V k)) atTop (𝓝 1) := by
  have h := tau_ratio_tendsto_atTop G (c3On_pos a b) (c3On_lt_one hab hlen) hN hG
  exact ⟨h, fun h1 => not_tendsto_atTop_of_tendsto_nhds h1 h⟩

/-- Big-O reading: `τ(G_k)` is not `O(c₃^(n_k))` (so not `Θ(c₃^(n_k))` either). -/
theorem not_tau_isBigO {a b : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 4 * π)
    (hN : Tendsto (fun k => Nat.card (V k)) atTop atTop) (hG : ∀ k, (G k).Connected) :
    ¬ (fun k => (tau (G k) : ℝ)) =O[atTop] (fun k => c3On a b ^ Nat.card (V k)) := by
  intro hO
  have h0 := hO.trans_tendsto
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (c3On_pos a b).le (c3On_lt_one hab hlen)).comp hN)
  have : (1 : ℝ) ≤ 0 := ge_of_tendsto h0 (Eventually.of_forall fun k => by
    exact_mod_cast one_le_tau (hG k))
  linarith

/-- Exponential-rate reading: `τ(G_k)^(1/n_k)` does not tend to `c₃` (it is always `≥ 1`). -/
theorem not_tau_rpow_tendsto {a b : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 4 * π)
    (hG : ∀ k, (G k).Connected) :
    ¬ Tendsto (fun k => (tau (G k) : ℝ) ^ ((1 : ℝ) / Nat.card (V k))) atTop
      (𝓝 (c3On a b)) := by
  intro h
  have : (1 : ℝ) ≤ c3On a b := ge_of_tendsto h (Eventually.of_forall fun k =>
    Real.one_le_rpow (by exact_mod_cast one_le_tau (hG k)) (by positivity))
  linarith [c3On_lt_one hab hlen]

end Deterministic

/-- Main theorem (`[0, 2π]` reading): the closed form is not `1.175…`, and for every sequence of
connected finite graphs with vertex count `n_k → ∞`, `τ(G_k) / c₃^(n_k)` does not tend to `1`. -/
theorem conjecture1857_false :
    c3 ∉ Set.Ico (1.175 : ℝ) 1.176 ∧
    ∀ {V : ℕ → Type} [∀ k, Finite (V k)] (G : ∀ k, SimpleGraph (V k)),
      Tendsto (fun k => Nat.card (V k)) atTop atTop → (∀ k, (G k).Connected) →
      ¬ Tendsto (fun k => (tau (G k) : ℝ) / c3 ^ Nat.card (V k)) atTop (𝓝 1) := by
  have hpi := Real.pi_pos
  refine ⟨c3On_not_numerical (by linarith) (by linarith), fun G hN hG => ?_⟩
  exact (not_tau_asymp G (by linarith) (by linarith) hN hG).2

/-! ## Uniform random 3-regular graphs on `Fin n` -/

open Classical in
/-- The 3-regular simple graphs on the vertex set `Fin n`. -/
noncomputable def reg3 (n : ℕ) : Finset (SimpleGraph (Fin n)) :=
  Finset.univ.filter fun G => G.IsRegularOfDegree 3

open Classical in
/-- Probability of an event `P` for a uniformly random 3-regular graph on `Fin n`. -/
noncomputable def prob (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  ((reg3 n).filter P).card / (reg3 n).card

/-- For every `0 < ε ≤ 1` and every window of length `≤ 4π`, for all large `n` the event
`|τ(G)/c₃ⁿ - 1| < ε` has probability at most that of `G` being disconnected. -/
theorem prob_good_le_prob_disconnected {a b : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 4 * π)
    {ε : ℝ} (hε : ε ≤ 1) : ∃ N, ∀ n ≥ N,
      prob n (fun G => |(tau G : ℝ) / c3On a b ^ n - 1| < ε) ≤ prob n (fun G => ¬ G.Connected) := by
  have hc0 := c3On_pos a b
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le (c3On_lt_one hab hlen)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 / 2 by norm_num)))
  refine ⟨N, fun n hn => ?_⟩
  classical
  unfold prob
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine Nat.cast_le.mpr (Finset.card_le_card fun G hG => ?_)
  simp only [Finset.mem_filter] at hG ⊢
  refine ⟨hG.1, fun hconn => ?_⟩
  have hcn : 0 < c3On a b ^ n := pow_pos hc0 n
  have hτ : (1 : ℝ) ≤ tau G := by exact_mod_cast one_le_tau hconn
  have hge : 2 ≤ (tau G : ℝ) / c3On a b ^ n := by
    rw [le_div_iff₀ hcn]; linarith [hN n hn]
  have := (abs_lt.mp hG.2).2
  linarith

/-- Conditional on the a.a.s. connectivity of random 3-regular graphs (taken as the explicit
hypothesis `hconn`, along the even vertex counts `n = 2m`), the probability that
`|τ(G)/c₃ⁿ - 1| < ε` tends to `0`, so `τ(G) ~ c₃ⁿ` fails in probability. -/
theorem not_prob_good_tendsto_one {a b : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 4 * π)
    {ε : ℝ} (hε : ε ≤ 1)
    (hconn : Tendsto (fun m => prob (2 * m) (fun G => ¬ G.Connected)) atTop (𝓝 0)) :
    Tendsto (fun m => prob (2 * m) (fun G => |(tau G : ℝ) / c3On a b ^ (2 * m) - 1| < ε))
      atTop (𝓝 0) ∧
    ¬ Tendsto (fun m => prob (2 * m) (fun G => |(tau G : ℝ) / c3On a b ^ (2 * m) - 1| < ε))
      atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := prob_good_le_prob_disconnected hab hlen hε
  have h0 : Tendsto (fun m => prob (2 * m) (fun G => |(tau G : ℝ) / c3On a b ^ (2 * m) - 1| < ε))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconn
      (Eventually.of_forall fun m => by unfold prob; positivity) ?_
    filter_upwards [eventually_ge_atTop N] with m hm
    exact hN (2 * m) (by omega)
  exact ⟨h0, fun h1 => by
    have := tendsto_nhds_unique h0 h1
    norm_num at this⟩

/-! ## Exact value on `[0, 2π]` (via Mathlib's circle average of `log ‖z - a‖`) -/

lemma norm_sq_eq (θ : ℝ) :
    ‖circleMap 0 1 θ - (((3 + √5) / 2 : ℝ) : ℂ)‖ ^ 2 = (3 + √5) / 2 * (3 - 2 * Real.cos θ) := by
  have h5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  linear_combination Real.sin_sq_add_cos_sq θ + h5 / 4

/-- `∫₀^{2π} log (3 - 2 cos θ) dθ = 2π · log ((3 + √5)/2)`. -/
theorem integral_eq :
    (∫ θ in (0:ℝ)..2 * π, Real.log (3 - 2 * Real.cos θ)) = 2 * π * Real.log ((3 + √5) / 2) := by
  set q : ℝ := (3 + √5) / 2 with hq
  have h5 : (2:ℝ) < √5 := by
    have := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num); nlinarith [Real.sqrt_nonneg 5]
  have hq0 : 0 < q := by rw [hq]; linarith
  have hpt : ∀ θ : ℝ, Real.log ‖circleMap 0 1 θ - (q : ℂ)‖
      = (Real.log (3 - 2 * Real.cos θ) + Real.log q) / 2 := by
    intro θ
    have h0 : ‖circleMap 0 1 θ - (q : ℂ)‖ ^ 2 = q * (3 - 2 * Real.cos θ) := norm_sq_eq θ
    have h := congrArg Real.log h0
    rw [Real.log_pow, Real.log_mul hq0.ne' (arg_pos θ).ne'] at h
    push_cast at h; linarith
  have hA := circleAverage_log_norm_sub_const₂ (a := (q : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]; rw [hq]; linarith)
  rw [Real.circleAverage_def] at hA
  simp only [hpt, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0, smul_eq_mul] at hA
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (integrand_continuous.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hA
  have hpi := Real.pi_pos
  field_simp at hA
  linarith

/-- The exact value: `c₃ = (2 - √3)/2 · (1 + √5)/2 ≈ 0.2168` on `[0, 2π]`. -/
theorem c3_eq : c3 = (2 - √3) / 2 * ((1 + √5) / 2) := by
  have h5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hφ : 0 < (1 + √5) / 2 := by positivity
  unfold c3 c3On
  rw [prefactor_eq, integral_eq,
    show (3 + √5) / 2 = ((1 + √5) / 2) ^ 2 by linear_combination -h5 / 4, Real.log_pow]
  have hpi := Real.pi_pos
  rw [show 2 * π * ((2 : ℕ) * Real.log ((1 + √5) / 2)) / (4 * π) = Real.log ((1 + √5) / 2) by
    field_simp; ring, Real.exp_log hφ]

/-- Numerical enclosure on `[0, 2π]`: `0.2167 < c₃ < 0.2169`. -/
theorem c3_bounds : 0.2167 < c3 ∧ c3 < 0.2169 := by
  rw [c3_eq]
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have a1 : 1.7320 < √3 := by nlinarith [Real.sqrt_nonneg 3]
  have a2 : √3 < 1.7321 := by nlinarith [Real.sqrt_nonneg 3]
  have b1 : 2.2360 < √5 := by nlinarith [Real.sqrt_nonneg 5]
  have b2 : √5 < 2.2361 := by nlinarith [Real.sqrt_nonneg 5]
  constructor
  · nlinarith [mul_pos (show (0:ℝ) < 1.7321 - √3 by linarith) (show (0:ℝ) < √5 - 2.2360 by linarith)]
  · nlinarith [mul_pos (show (0:ℝ) < √3 - 1.7320 by linarith) (show (0:ℝ) < 2.2361 - √5 by linarith)]

end C1857
