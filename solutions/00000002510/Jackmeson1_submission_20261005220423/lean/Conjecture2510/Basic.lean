import Mathlib

/-!
# Conjecture 00000002510: best low-rank approximation of tensors

We formalize, for real `2 × 2 × 2` tensors, the de Silva--Lim phenomenon:

* matrices: for every `m n r`, the set of real `m × n` matrices of rank `≤ r` (Mathlib's
  `Matrix.rank`) is closed, so every matrix has a best rank-`≤ r` approximation;
* in any proper metric space, a nonempty set `S` gives every point a best approximation
  iff `S` is closed; in particular this holds for the tensor sets `rankLE r`;
* tensors: `rankLE 2` is not closed. The W tensor is a limit of rank-2 tensors but has rank 3,
  so it has no best rank-`≤ 2` approximation (infimum `0`, not attained);
* diverging components: along any sequence of two-term decompositions converging to `W`,
  the norm of each of the two rank-one summands tends to infinity.

Norm: the default sup norm on `Fin 2 → Fin 2 → Fin 2 → ℝ`.
-/

open Filter Topology Metric

namespace C2510

/-- Real `2 × 2 × 2` tensors. -/
abbrev Tensor3 := Fin 2 → Fin 2 → Fin 2 → ℝ

/-- The rank-one (outer product) tensor `a ⊗ b ⊗ c`. -/
def outer3 (a b c : Fin 2 → ℝ) : Tensor3 := fun i j k => a i * b j * c k

/-- `T` is a sum of `r` rank-one tensors. -/
def HasRankLE (T : Tensor3) (r : ℕ) : Prop :=
  ∃ a b c : Fin r → Fin 2 → ℝ, T = ∑ s, outer3 (a s) (b s) (c s)

/-- The set of tensors of rank at most `r`. -/
def rankLE (r : ℕ) : Set Tensor3 := {T | HasRankLE T r}

/-- Tensor rank: the least `r` such that `T` is a sum of `r` rank-one tensors (`sInf`; the
set is nonempty for the tensor `W` used below, see `W_hasRankLE_three`). -/
noncomputable def tensorRank (T : Tensor3) : ℕ := sInf {r | HasRankLE T r}

/-- `y` is a best approximation of `x` from the set `A`: `y ∈ A` and `y` minimizes the distance. -/
def IsBestApprox {X : Type*} [MetricSpace X] (A : Set X) (x y : X) : Prop :=
  y ∈ A ∧ ∀ z ∈ A, dist x y ≤ dist x z

/-- Standard basis vectors `e₁ = (1,0)`, `e₂ = (0,1)` of `ℝ²` (indices `0`, `1`). -/
def e₁ : Fin 2 → ℝ := ![1, 0]
def e₂ : Fin 2 → ℝ := ![0, 1]

/-- The W tensor `e₁⊗e₁⊗e₂ + e₁⊗e₂⊗e₁ + e₂⊗e₁⊗e₁`. -/
def W : Tensor3 := outer3 e₁ e₁ e₂ + outer3 e₁ e₂ e₁ + outer3 e₂ e₁ e₁

/-! ## General metric fact: best approximations exist for all targets iff the set is closed -/

theorem bestApprox_forall_iff_isClosed {X : Type*} [MetricSpace X] [ProperSpace X]
    (A : Set X) (hA : A.Nonempty) : (∀ x, ∃ y, IsBestApprox A x y) ↔ IsClosed A := by
  constructor
  · intro h
    refine isClosed_iff_clusterPt.2 fun x hx => ?_
    have hx' : x ∈ closure A := mem_closure_iff_clusterPt.2 hx
    obtain ⟨y, hyA, hy⟩ := h x
    have : dist x y = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) dist_nonneg
      obtain ⟨z, hzA, hz⟩ := Metric.mem_closure_iff.1 hx' ε hε
      linarith [hy z hzA]
    rwa [dist_eq_zero.1 this]
  · intro hc x
    obtain ⟨y, hyA, hy⟩ := hc.exists_infDist_eq_dist hA x
    exact ⟨y, hyA, fun z hz => hy ▸ infDist_le_dist_of_mem hz⟩

/-! ## Matrices: the rank-`≤ r` locus is closed -/

theorem matrix_rankLE_isClosed (m n r : ℕ) :
    IsClosed {M : Matrix (Fin m) (Fin n) ℝ | M.rank ≤ r} := by
  let g : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ Matrix.toLin'.toLinearMap
  have hg : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have key : ∀ M : Matrix (Fin m) (Fin n) ℝ,
      ((g M : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))).rank = (M.rank : Cardinal) := by
    intro M
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.coe_toContinuousLinearMap]
    rw [Matrix.rank, LinearMap.rank, Matrix.toLin'_apply', Module.finrank_eq_rank]
  have : {M : Matrix (Fin m) (Fin n) ℝ | M.rank ≤ r} =
      (g ⁻¹' {f | ((r + 1 : ℕ) : Cardinal) ≤ (f : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)).rank})ᶜ := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_preimage, key, Nat.cast_le]
    omega
  rw [this]
  exact ((isOpen_setOfPred_nat_le_rank (r + 1)).preimage hg).isClosed_compl

/-- Matrices (viewed as arrays `Fin m → Fin n → ℝ` with the sup norm) always have a best
rank-`≤ r` approximation. -/
theorem matrix_bestApprox_exists (m n r : ℕ) (A : Fin m → Fin n → ℝ) :
    ∃ B, IsBestApprox {M : Fin m → Fin n → ℝ | (Matrix.of M).rank ≤ r} A B :=
  (bestApprox_forall_iff_isClosed _ ⟨0, by simp⟩).2 (matrix_rankLE_isClosed m n r) A

/-! ## Basic facts about tensor rank -/

@[simp] theorem outer3_zero_left (b c : Fin 2 → ℝ) : outer3 0 b c = 0 := by
  funext i j k; simp [outer3]

theorem zero_mem_rankLE (r : ℕ) : (0 : Tensor3) ∈ rankLE r :=
  ⟨0, 0, 0, by simp⟩

theorem HasRankLE.mono {T : Tensor3} {r s : ℕ} (h : HasRankLE T r) (hrs : r ≤ s) :
    HasRankLE T s := by
  induction s, hrs using Nat.le_induction with
  | base => exact h
  | succ s _ ih =>
    obtain ⟨a, b, c, rfl⟩ := ih
    refine ⟨Fin.snoc a 0, Fin.snoc b 0, Fin.snoc c 0, ?_⟩
    simp [Fin.sum_univ_castSucc]

/-- The purely algebraic core: the eight equations `W = a⊗b⊗c + p⊗q⊗r` have no real solution.
(Cramer's rule on the first-mode slices, then a vanishing `2 × 2` determinant.) -/
theorem W_eqns_inconsistent (a0 a1 p0 p1 b0 b1 q0 q1 c0 c1 r0 r1 : ℝ)
    (h000 : a0*b0*c0 + p0*q0*r0 = 0) (h001 : a0*b0*c1 + p0*q0*r1 = 1)
    (h010 : a0*b1*c0 + p0*q1*r0 = 1) (h011 : a0*b1*c1 + p0*q1*r1 = 0)
    (h100 : a1*b0*c0 + p1*q0*r0 = 1) (h101 : a1*b0*c1 + p1*q0*r1 = 0)
    (h110 : a1*b1*c0 + p1*q1*r0 = 0) (h111 : a1*b1*c1 + p1*q1*r1 = 0) : False := by
  set D := a0*p1 - a1*p0
  have g00 : D*b0*c0 = -p0 := by linear_combination p1*h000 - p0*h100
  have g01 : D*b0*c1 = p1 := by linear_combination p1*h001 - p0*h101
  have g10 : D*b1*c0 = p1 := by linear_combination p1*h010 - p0*h110
  have g11 : D*b1*c1 = 0 := by linear_combination p1*h011 - p0*h111
  have k00 : D*q0*r0 = a0 := by linear_combination a0*h100 - a1*h000
  have k01 : D*q0*r1 = -a1 := by linear_combination a0*h101 - a1*h001
  have k10 : D*q1*r0 = -a1 := by linear_combination a0*h110 - a1*h010
  have k11 : D*q1*r1 = 0 := by linear_combination a0*h111 - a1*h011
  have hp : p1^2 = 0 := by
    linear_combination (-(D*b1*c0)) * g01 - p1 * g10 + (D*b1*c1) * g00 - p0 * g11
  have ha : a1^2 = 0 := by
    linear_combination (-(D*q1*r0)) * k01 + a1 * k10 + (D*q1*r1) * k00 + a0 * k11
  have hp' : p1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hp
  have ha' : a1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ha
  rw [ha', hp'] at h100
  norm_num at h100

/-- The W tensor is not a sum of two rank-one tensors. -/
theorem W_not_rankLE_two : ¬ HasRankLE W 2 := by
  rintro ⟨a, b, c, h⟩
  have E : ∀ i j k, a 0 i * b 0 j * c 0 k + a 1 i * b 1 j * c 1 k = W i j k := by
    intro i j k; rw [h]; simp [outer3, Fin.sum_univ_two]
  exact W_eqns_inconsistent (a 0 0) (a 0 1) (a 1 0) (a 1 1) (b 0 0) (b 0 1) (b 1 0) (b 1 1)
    (c 0 0) (c 0 1) (c 1 0) (c 1 1)
    ((E 0 0 0).trans (by simp [W, outer3, e₁, e₂])) ((E 0 0 1).trans (by simp [W, outer3, e₁, e₂]))
    ((E 0 1 0).trans (by simp [W, outer3, e₁, e₂])) ((E 0 1 1).trans (by simp [W, outer3, e₁, e₂]))
    ((E 1 0 0).trans (by simp [W, outer3, e₁, e₂])) ((E 1 0 1).trans (by simp [W, outer3, e₁, e₂]))
    ((E 1 1 0).trans (by simp [W, outer3, e₁, e₂])) ((E 1 1 1).trans (by simp [W, outer3, e₁, e₂]))

theorem W_hasRankLE_three : HasRankLE W 3 :=
  ⟨![e₁, e₁, e₂], ![e₁, e₂, e₁], ![e₂, e₁, e₁], by simp [W, Fin.sum_univ_three]⟩

/-- The W tensor has tensor rank exactly 3. -/
theorem tensorRank_W : tensorRank W = 3 := by
  refine le_antisymm (Nat.sInf_le W_hasRankLE_three) (le_csInf ⟨3, W_hasRankLE_three⟩ ?_)
  intro r hr
  by_contra hlt
  exact W_not_rankLE_two (HasRankLE.mono hr (by omega))

/-! ## The approximating rank-2 sequence `Tseq n → W` -/

/-- `t n = 1/(n+1)`. -/
noncomputable def t (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- `u n = e₁ + t n • e₂`. -/
noncomputable def u (n : ℕ) : Fin 2 → ℝ := ![1, t n]

/-- `Tseq n = (n+1) (e₁ + e₂/(n+1))^{⊗3} - (n+1) e₁^{⊗3}`, a sum of two rank-one tensors. -/
noncomputable def Tseq (n : ℕ) : Tensor3 :=
  outer3 (((n : ℝ) + 1) • u n) (u n) (u n) + outer3 (-((n : ℝ) + 1) • e₁) e₁ e₁

theorem Tseq_mem (n : ℕ) : Tseq n ∈ rankLE 2 :=
  ⟨![((n : ℝ) + 1) • u n, -((n : ℝ) + 1) • e₁], ![u n, e₁], ![u n, e₁], by
    simp [Tseq, Fin.sum_univ_two]⟩

/-- Second- and third-order correction terms. -/
def P : Tensor3 := outer3 e₁ e₂ e₂ + outer3 e₂ e₁ e₂ + outer3 e₂ e₂ e₁
def Q : Tensor3 := outer3 e₂ e₂ e₂

theorem Tseq_eq (n : ℕ) : Tseq n = W + t n • P + (t n) ^ 2 • Q := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Tseq, W, P, Q, outer3, e₁, e₂, u, t] <;> field_simp

theorem Tseq_tendsto : Tendsto Tseq atTop (𝓝 W) := by
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have := (tendsto_const_nhds (x := W)).add (ht.smul_const P) |>.add ((ht.pow 2).smul_const Q)
  simp only [zero_smul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at this
  rw [show Tseq = fun n => W + t n • P + t n ^ 2 • Q from funext Tseq_eq]
  exact this

theorem W_mem_closure : W ∈ closure (rankLE 2) :=
  mem_closure_of_tendsto Tseq_tendsto (Eventually.of_forall Tseq_mem)

theorem rankLE_two_not_isClosed : ¬ IsClosed (rankLE 2) := fun hc =>
  W_not_rankLE_two (by have h := W_mem_closure; rw [hc.closure_eq] at h; exact h)

theorem infDist_W : infDist W (rankLE 2) = 0 :=
  (mem_closure_iff_infDist_zero ⟨0, zero_mem_rankLE 2⟩).1 W_mem_closure

theorem W_no_best_approx : ¬ ∃ S, IsBestApprox (rankLE 2) W S := by
  rintro ⟨S, hS, hbest⟩
  have : dist W S = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) dist_nonneg
    obtain ⟨z, hzA, hz⟩ := Metric.mem_closure_iff.1 W_mem_closure ε hε
    linarith [hbest z hzA]
  exact W_not_rankLE_two (dist_eq_zero.1 this ▸ hS)

/-! ## Diverging components -/

theorem norm_attained (v : Fin 2 → ℝ) : ∃ i, ‖v‖ = |v i| := by
  rcases le_total |v 0| |v 1| with h | h
  · refine ⟨1, le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 ?_) ?_⟩
    · intro i; fin_cases i <;> simp [h]
    · simpa using norm_le_pi_norm v 1
  · refine ⟨0, le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 ?_) ?_⟩
    · intro i; fin_cases i <;> simp [h]
    · simpa using norm_le_pi_norm v 0

/-- In the sup norm, `‖a‖ ‖b‖ ‖c‖ ≤ ‖a ⊗ b ⊗ c‖` (in fact equality holds). -/
theorem norm_mul_le_norm_outer3 (a b c : Fin 2 → ℝ) : ‖a‖ * ‖b‖ * ‖c‖ ≤ ‖outer3 a b c‖ := by
  obtain ⟨i, hi⟩ := norm_attained a
  obtain ⟨j, hj⟩ := norm_attained b
  obtain ⟨k, hk⟩ := norm_attained c
  calc ‖a‖ * ‖b‖ * ‖c‖ = ‖outer3 a b c i j k‖ := by
        rw [hi, hj, hk, Real.norm_eq_abs, outer3, abs_mul, abs_mul]
    _ ≤ ‖outer3 a b c i j‖ := norm_le_pi_norm _ k
    _ ≤ ‖outer3 a b c i‖ := norm_le_pi_norm _ j
    _ ≤ ‖outer3 a b c‖ := norm_le_pi_norm _ i

/-- Rebalancing: every rank-one tensor `T` has factors of norm `≤ max ‖T‖ 1`. -/
theorem rebalance (a b c : Fin 2 → ℝ) : ∃ x : (Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ),
    outer3 x.1 x.2.1 x.2.2 = outer3 a b c ∧ ‖x‖ ≤ max ‖outer3 a b c‖ 1 := by
  by_cases hbc : b = 0 ∨ c = 0
  · refine ⟨0, ?_, by simp⟩
    rcases hbc with rfl | rfl <;> funext i j k <;> simp [outer3]
  · push Not at hbc
    have hb : ‖b‖ ≠ 0 := norm_ne_zero_iff.2 hbc.1
    have hc : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hbc.2
    refine ⟨((‖b‖ * ‖c‖) • a, ‖b‖⁻¹ • b, ‖c‖⁻¹ • c), ?_, ?_⟩
    · funext i j k; simp only [outer3, Pi.smul_apply, smul_eq_mul]; field_simp
    · simp only [norm_prod_le_iff, norm_smul, norm_mul, norm_inv, norm_norm]
      refine ⟨le_max_of_le_left ?_, le_max_of_le_right (by rw [inv_mul_cancel₀ hb]),
        le_max_of_le_right (by rw [inv_mul_cancel₀ hc])⟩
      nlinarith [norm_mul_le_norm_outer3 a b c]

/-- Any sequence of two-term decompositions converging to `W` has unbounded summands:
the larger of the two summand norms tends to infinity. -/
theorem max_summand_tendsto (a b c : ℕ → Fin 2 → Fin 2 → ℝ)
    (h : Tendsto (fun n => ∑ s, outer3 (a n s) (b n s) (c n s)) atTop (𝓝 W)) :
    Tendsto (fun n => max ‖outer3 (a n 0) (b n 0) (c n 0)‖ ‖outer3 (a n 1) (b n 1) (c n 1)‖)
      atTop atTop := by
  rw [Filter.tendsto_atTop]
  by_contra hne
  push Not at hne
  obtain ⟨C, hC⟩ := hne
  have hfreq : ∃ᶠ n in atTop,
      max ‖outer3 (a n 0) (b n 0) (c n 0)‖ ‖outer3 (a n 1) (b n 1) (c n 1)‖ < C := by
    simpa [Filter.not_eventually, not_le] using hC
  obtain ⟨φ, hφ, hφC⟩ := extraction_of_frequently_atTop hfreq
  choose F hF hFn using rebalance
  let G : ℕ → Fin 2 → (Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
    fun n s => F (a (φ n) s) (b (φ n) s) (c (φ n) s)
  have hGb : ∀ n, G n ∈ closedBall 0 (max C 1) := by
    intro n
    rw [mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg (le_max_of_le_right zero_le_one)]
    intro s
    refine (hFn _ _ _).trans (max_le_max ?_ le_rfl)
    have := (hφC n).le
    fin_cases s
    · exact (le_max_left _ _).trans this
    · exact (le_max_right _ _).trans this
  obtain ⟨L, -, ψ, hψ, hL⟩ := tendsto_subseq_of_bounded isBounded_closedBall hGb
  let Φ : (Fin 2 → (Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ)) → Tensor3 :=
    fun x => ∑ s, outer3 (x s).1 (x s).2.1 (x s).2.2
  have hΦ : Continuous Φ := by
    refine continuous_finsetSum _ fun s _ => ?_
    refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun k => ?_
    simp only [outer3]
    fun_prop
  have h1 : Tendsto (fun n => Φ (G (ψ n))) atTop (𝓝 (Φ L)) := (hΦ.tendsto L).comp hL
  have h2 : Tendsto (fun n => Φ (G (ψ n))) atTop (𝓝 W) := by
    have : (fun n => Φ (G (ψ n))) =
        (fun n => ∑ s, outer3 (a n s) (b n s) (c n s)) ∘ (φ ∘ ψ) := by
      funext n; simp [Φ, G, hF]
    rw [this]
    exact h.comp (hφ.comp hψ).tendsto_atTop
  exact W_not_rankLE_two ⟨fun s => (L s).1, fun s => (L s).2.1, fun s => (L s).2.2,
    tendsto_nhds_unique h2 h1⟩

/-- Diverging components: along any sequence of two-term decompositions converging to `W`,
the norm of *each* rank-one summand tends to infinity (the two summands cancel). -/
theorem summand_tendsto (a b c : ℕ → Fin 2 → Fin 2 → ℝ)
    (h : Tendsto (fun n => ∑ s, outer3 (a n s) (b n s) (c n s)) atTop (𝓝 W)) (s : Fin 2) :
    Tendsto (fun n => ‖outer3 (a n s) (b n s) (c n s)‖) atTop atTop := by
  have hb : ∀ᶠ n in atTop, ‖∑ s, outer3 (a n s) (b n s) (c n s)‖ < ‖W‖ + 1 :=
    h.norm.eventually_lt_const (lt_add_one _)
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right atTop (-(‖W‖ + 1)) (max_summand_tendsto a b c h))
  filter_upwards [hb] with n hn
  rw [Fin.sum_univ_two] at hn
  set S0 := outer3 (a n 0) (b n 0) (c n 0)
  set S1 := outer3 (a n 1) (b n 1) (c n 1)
  have e0 : ‖S0‖ ≤ ‖S0 + S1‖ + ‖S1‖ := by
    simpa using norm_sub_le (S0 + S1) S1
  have e1 : ‖S1‖ ≤ ‖S0 + S1‖ + ‖S0‖ := by
    simpa using norm_sub_le (S0 + S1) S0
  fin_cases s
  · show max ‖S0‖ ‖S1‖ + -(‖W‖ + 1) ≤ ‖S0‖
    rcases max_cases ‖S0‖ ‖S1‖ with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;> linarith [norm_nonneg W]
  · show max ‖S0‖ ‖S1‖ + -(‖W‖ + 1) ≤ ‖S1‖
    rcases max_cases ‖S0‖ ‖S1‖ with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;> linarith [norm_nonneg W]

/-! ## Main theorem -/

/-- **Conjecture 00000002510** (de Silva--Lim), for real `2 × 2 × 2` tensors with the sup norm:
(1) unlike tensors, real matrices of rank `≤ r` form a closed set, so best rank-`≤ r`
approximations of matrices always exist; (2) best rank-`≤ r` tensor approximations exist for
every target iff `rankLE r` is closed; (3) `rankLE 2` is not closed: the W tensor (tensor rank 3)
lies in its closure, at distance `0`, with no best rank-`≤ 2` approximation; (4) every sequence
of two-term decompositions converging to `W` has both summand norms tending to infinity. -/
theorem conjecture_2510 :
    (∀ m n r : ℕ, IsClosed {M : Matrix (Fin m) (Fin n) ℝ | M.rank ≤ r} ∧
      ∀ A : Fin m → Fin n → ℝ,
        ∃ B, IsBestApprox {M : Fin m → Fin n → ℝ | (Matrix.of M).rank ≤ r} A B) ∧
    (∀ r : ℕ, (∀ T : Tensor3, ∃ S, IsBestApprox (rankLE r) T S) ↔ IsClosed (rankLE r)) ∧
    ¬ IsClosed (rankLE 2) ∧ W ∈ closure (rankLE 2) ∧ tensorRank W = 3 ∧
    infDist W (rankLE 2) = 0 ∧ (¬ ∃ S, IsBestApprox (rankLE 2) W S) ∧
    ∀ a b c : ℕ → Fin 2 → Fin 2 → ℝ,
      Tendsto (fun n => ∑ s, outer3 (a n s) (b n s) (c n s)) atTop (𝓝 W) →
      ∀ s, Tendsto (fun n => ‖outer3 (a n s) (b n s) (c n s)‖) atTop atTop :=
  ⟨fun m n r => ⟨matrix_rankLE_isClosed m n r, matrix_bestApprox_exists m n r⟩,
    fun r => bestApprox_forall_iff_isClosed _ ⟨0, zero_mem_rankLE r⟩,
    rankLE_two_not_isClosed, W_mem_closure, tensorRank_W, infDist_W, W_no_best_approx,
    summand_tendsto⟩

end C2510
