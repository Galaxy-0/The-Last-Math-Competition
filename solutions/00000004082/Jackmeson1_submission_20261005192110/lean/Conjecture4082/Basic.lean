import Mathlib

/-!
# Conjecture 00000004082 (spectral formula of the Kuramoto critical coupling) is false

The all-to-all Kuramoto model of `n` oscillators with intrinsic frequencies `ω : Fin n → ℝ`
and coupling `K` is
  `θᵢ' = ωᵢ + (K/n) Σⱼ sin(θⱼ - θᵢ)`.
A phase-locked solution is one in which all phase differences `θᵢ(t) - θⱼ(t)` are constant.
`Locked ω K` says that a phase-locked state exists; `locked_iff_phaseLockedSolution` proves that
this is equivalent to the existence of a phase-locked trajectory of the ODE.
The critical coupling is `Kc ω = inf {K ≥ 0 | Locked ω K}`.

The conjecture asserts `Kc ω = c₁ · (Σᵢ |ωᵢ - ω̄|)/n` for a universal constant `c₁`.
For every `n ≥ 6` we give two frequency vectors with the same mean absolute deviation `1`:
`clusterFreq n 3` (two clusters; for `n = 6` it is `(1,1,1,-1,-1,-1)`), which locks for every
`K ≥ n²/(6(n-3))`, and `clusterFreq n 1` (one outlier; for `n = 6` it is `(3,-3/5,…,-3/5)`),
which cannot lock for any `K < n/2`. Since `n²/(6(n-3)) < n/2`, the two critical couplings
differ, so `Kc` is not a function of the mean absolute deviation at all.
The same holds for the unnormalised coupling `K Σⱼ sin(θⱼ - θᵢ)`, for phase-cohesive locking
(`|θᵢ - θⱼ| < π/2`), and for the threshold `inf {K ≥ 0 | locked for every K' ≥ K}`.
-/

open Finset Real

noncomputable section

namespace C4082

/-- Existence of a phase-locked state of the all-to-all Kuramoto model with coupling `K/n`:
phases `θ` and a common frequency `Ω` with `ωᵢ + (K/n) Σⱼ sin(θⱼ - θᵢ) = Ω` for all `i`. -/
def Locked {n : ℕ} (ω : Fin n → ℝ) (K : ℝ) : Prop :=
  ∃ Ω : ℝ, ∃ θ : Fin n → ℝ, ∀ i, ω i + K / n * ∑ j, Real.sin (θ j - θ i) = Ω

/-- `θ` solves the all-to-all Kuramoto ODE `θᵢ' = ωᵢ + (K/n) Σⱼ sin(θⱼ - θᵢ)` on all of `ℝ`. -/
def IsKuramotoSolution {n : ℕ} (ω : Fin n → ℝ) (K : ℝ) (θ : ℝ → Fin n → ℝ) : Prop :=
  ∀ t i, HasDerivAt (fun s => θ s i) (ω i + K / n * ∑ j, Real.sin (θ t j - θ t i)) t

/-- A trajectory is phase locked if all phase differences are constant in time. -/
def IsPhaseLocked {n : ℕ} (θ : ℝ → Fin n → ℝ) : Prop :=
  ∀ t i j, θ t i - θ t j = θ 0 i - θ 0 j

/-- Critical coupling: the infimum of the couplings `K ≥ 0` admitting a phase-locked state. -/
def Kc {n : ℕ} (ω : Fin n → ℝ) : ℝ := sInf {K : ℝ | 0 ≤ K ∧ Locked ω K}

/-- The mean frequency `ω̄ = (Σᵢ ωᵢ)/n`. -/
def mean {n : ℕ} (ω : Fin n → ℝ) : ℝ := (∑ i, ω i) / n

/-- The conjecture's dispersion `(Σᵢ |ωᵢ - ω̄|)/n` (mean absolute deviation). -/
def meanAbsDev {n : ℕ} (ω : Fin n → ℝ) : ℝ := (∑ i, |ω i - mean ω|) / n

/-! ## `Locked` is exactly the existence of a phase-locked trajectory -/

theorem locked_iff_phaseLockedSolution {n : ℕ} (ω : Fin n → ℝ) (K : ℝ) :
    Locked ω K ↔ ∃ θ : ℝ → Fin n → ℝ, IsKuramotoSolution ω K θ ∧ IsPhaseLocked θ := by
  constructor
  · rintro ⟨Ω, θ₀, h⟩
    refine ⟨fun t i => θ₀ i + Ω * t, fun t i => ?_, fun t i j => by ring⟩
    have hd : HasDerivAt (fun s => θ₀ i + Ω * s) Ω t := by
      simpa using ((hasDerivAt_id t).const_mul Ω).const_add (θ₀ i)
    convert hd using 1
    rw [← h i]
    congr 2
    exact Finset.sum_congr rfl (fun j _ => by congr 1; ring)
  · rintro ⟨θ, hsol, hpl⟩
    set d : Fin n → ℝ := fun i => ω i + K / n * ∑ j, Real.sin (θ 0 j - θ 0 i) with hd
    have hdiff : ∀ i j, d i = d j := by
      intro i j
      have h1 := (hsol 0 i).sub (hsol 0 j)
      have hconst : (fun s => θ s i - θ s j) = fun _ => θ 0 i - θ 0 j :=
        funext fun s => hpl s i j
      have h2 : HasDerivAt (fun s => θ s i - θ s j) 0 0 := by
        rw [hconst]; exact hasDerivAt_const 0 _
      have := h1.unique h2
      simp only [hd]
      linarith
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun _ => 0, fun i => i.elim0⟩
    · exact ⟨d ⟨0, hn⟩, θ 0, fun i => hdiff i ⟨0, hn⟩⟩

/-! ## A necessary condition: `|ωᵢ - ω̄| ≤ K` at any locked state -/

lemma double_sum_sin_eq_zero {n : ℕ} (θ : Fin n → ℝ) :
    ∑ i, ∑ j, Real.sin (θ j - θ i) = 0 := by
  have h : ∑ i, ∑ j, Real.sin (θ j - θ i) = -∑ i, ∑ j, Real.sin (θ j - θ i) := by
    conv_rhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Real.sin_neg, neg_sub]
  linarith

theorem abs_sub_mean_le_of_locked {n : ℕ} (hn : 0 < n) {ω : Fin n → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : Locked ω K) (i : Fin n) : |ω i - mean ω| ≤ K := by
  obtain ⟨Ω, θ, hθ⟩ := h
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hsum : ∑ i, ω i = n * Ω := by
    have := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hθ i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, double_sum_sin_eq_zero, mul_zero, add_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hmean : mean ω = Ω := by
    unfold mean; rw [hsum]; field_simp
  have hS : |∑ j, Real.sin (θ j - θ i)| ≤ n := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      Real.abs_sin_le_one (θ j - θ i))
    simpa using this
  have hi : ω i - Ω = -(K / n * ∑ j, Real.sin (θ j - θ i)) := by linarith [hθ i]
  rw [hmean, hi, abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ K / n)]
  calc K / n * |∑ j, Real.sin (θ j - θ i)| ≤ K / n * n :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = K := by field_simp

/-! ## Two-cluster frequency vectors -/

/-- `a` oscillators at `n/(2a)` and `n - a` oscillators at `-n/(2(n-a))`. -/
def clusterFreq (n a : ℕ) (i : Fin n) : ℝ :=
  if (i : ℕ) < a then (n : ℝ) / (2 * a) else -((n : ℝ) / (2 * ((n : ℝ) - a)))

/-- The coupling from which `clusterFreq n a` locks. -/
def clusterThr (n a : ℕ) : ℝ := (n : ℝ) ^ 2 / (2 * a * ((n : ℝ) - a))

/-- The two-cluster phases at coupling `K`. -/
def clusterPhase (n a : ℕ) (K : ℝ) (j : Fin n) : ℝ :=
  if (j : ℕ) < a then Real.arcsin (clusterThr n a / K) else 0

lemma sum_ite_lt (n a : ℕ) (h : a ≤ n) (c d : ℝ) :
    ∑ j : Fin n, (if (j : ℕ) < a then c else d) = a * c + ((n : ℝ) - a) * d := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < a then c else d) n,
    ← Finset.sum_range_add_sum_Ico _ h]
  have h1 : ∑ k ∈ Finset.range a, (if k < a then c else d) = ∑ k ∈ Finset.range a, c :=
    Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))
  have h2 : ∑ k ∈ Finset.Ico a n, (if k < a then c else d) = ∑ k ∈ Finset.Ico a n, d :=
    Finset.sum_congr rfl (fun k hk => if_neg (by simp at hk; omega))
  rw [h1, h2, Finset.sum_const, Finset.sum_const, Finset.card_range, Nat.card_Ico, nsmul_eq_mul,
    nsmul_eq_mul, Nat.cast_sub h]

lemma clusterThr_pos {n a : ℕ} (ha : 0 < a) (han : a < n) : 0 < clusterThr n a := by
  have : (a : ℝ) < n := by exact_mod_cast han
  have : (0 : ℝ) < a := by exact_mod_cast ha
  unfold clusterThr
  exact div_pos (pow_pos (by linarith) 2) (mul_pos (by linarith) (by linarith))

lemma mean_clusterFreq {n a : ℕ} (ha : 0 < a) (han : a < n) : mean (clusterFreq n a) = 0 := by
  have h1 : (a : ℝ) < n := by exact_mod_cast han
  have h2 : (0 : ℝ) < a := by exact_mod_cast ha
  have h3 : (n : ℝ) - a ≠ 0 := by linarith
  unfold mean clusterFreq
  rw [sum_ite_lt n a han.le]
  field_simp
  ring

theorem meanAbsDev_clusterFreq {n a : ℕ} (ha : 0 < a) (han : a < n) :
    meanAbsDev (clusterFreq n a) = 1 := by
  have h1 : (a : ℝ) < n := by exact_mod_cast han
  have h2 : (0 : ℝ) < a := by exact_mod_cast ha
  have h3 : (0 : ℝ) < (n : ℝ) - a := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hp : 0 < (n : ℝ) / (2 * a) := div_pos (by linarith) (by linarith)
  have hq : 0 < (n : ℝ) / (2 * ((n : ℝ) - a)) := div_pos (by linarith) (by linarith)
  unfold meanAbsDev
  rw [mean_clusterFreq ha han]
  have : ∀ i, |clusterFreq n a i - 0| =
      if (i : ℕ) < a then (n : ℝ) / (2 * a) else (n : ℝ) / (2 * ((n : ℝ) - a)) := by
    intro i
    unfold clusterFreq
    split_ifs
    · rw [sub_zero, abs_of_pos hp]
    · rw [sub_zero, abs_neg, abs_of_pos hq]
  rw [Finset.sum_congr rfl (fun i _ => this i), sum_ite_lt n a han.le]
  field_simp
  ring

/-- For every `K ≥ clusterThr n a`, `clusterPhase n a K` is a locked state with `Ω = 0`. -/
theorem clusterPhase_locked {n a : ℕ} (ha : 0 < a) (han : a < n) {K : ℝ}
    (hK : clusterThr n a ≤ K) (i : Fin n) :
    clusterFreq n a i + K / n * ∑ j, Real.sin (clusterPhase n a K j - clusterPhase n a K i) = 0 := by
  have h1 : (a : ℝ) < n := by exact_mod_cast han
  have h2 : (0 : ℝ) < a := by exact_mod_cast ha
  have h3 : (0 : ℝ) < (n : ℝ) - a := by linarith
  have hs := clusterThr_pos ha han
  have hK0 : 0 < K := hs.trans_le hK
  have hx : Real.sin (Real.arcsin (clusterThr n a / K)) = clusterThr n a / K :=
    Real.sin_arcsin (by have := div_pos hs hK0; linarith) ((div_le_one hK0).mpr hK)
  set δ := Real.arcsin (clusterThr n a / K)
  unfold clusterPhase clusterFreq
  by_cases hi : (i : ℕ) < a
  · have e : ∀ j : Fin n, Real.sin ((if (j : ℕ) < a then δ else 0) - δ) =
        if (j : ℕ) < a then 0 else -(clusterThr n a / K) := by
      intro j; split_ifs <;> simp [hx]
    simp only [hi, if_true]
    rw [Finset.sum_congr rfl (fun j _ => e j), sum_ite_lt n a han.le]
    unfold clusterThr
    field_simp
    ring
  · have e : ∀ j : Fin n, Real.sin ((if (j : ℕ) < a then δ else 0) - 0) =
        if (j : ℕ) < a then clusterThr n a / K else 0 := by
      intro j; split_ifs <;> simp [hx]
    simp only [hi, if_false]
    rw [Finset.sum_congr rfl (fun j _ => e j), sum_ite_lt n a han.le]
    unfold clusterThr
    field_simp
    ring

/-- Above the threshold the two-cluster state is phase cohesive: all gaps are `< π/2`. -/
theorem clusterPhase_cohesive {n a : ℕ} (ha : 0 < a) (han : a < n) {K : ℝ}
    (hK : clusterThr n a < K) (i j : Fin n) :
    |clusterPhase n a K i - clusterPhase n a K j| < π / 2 := by
  have hs := clusterThr_pos ha han
  have hK0 : 0 < K := hs.trans hK
  have h0 : 0 ≤ Real.arcsin (clusterThr n a / K) :=
    Real.arcsin_nonneg.mpr (div_pos hs hK0).le
  have h1 : Real.arcsin (clusterThr n a / K) < π / 2 :=
    Real.arcsin_lt_pi_div_two.mpr ((div_lt_one hK0).mpr hK)
  have hpi := Real.pi_pos
  have hlt1 : clusterThr n a / K < 1 := (div_lt_one hK0).mpr hK
  unfold clusterPhase
  split_ifs <;> simp [abs_of_nonneg h0] <;> linarith

/-! ## Separation of the thresholds -/

lemma clusterThr_three_lt {n : ℕ} (hn : 6 ≤ n) : clusterThr n 3 < (n : ℝ) / 2 := by
  have h : (6 : ℝ) ≤ n := by exact_mod_cast hn
  unfold clusterThr
  rw [div_lt_div_iff₀ (by push_cast; nlinarith) (by norm_num)]
  push_cast
  nlinarith

lemma clusterFreq_one_zero {n : ℕ} (hn : 0 < n) : clusterFreq n 1 ⟨0, hn⟩ = (n : ℝ) / 2 := by
  simp [clusterFreq]

/-- For any locking notion `P` that implies `Locked` at coupling `lam * K` and holds for the
cluster vectors once `lam * K` exceeds `clusterThr`, the threshold `inf {K ≥ 0 | P ω K}` of
`clusterFreq n 3` is strictly smaller than that of `clusterFreq n 1`. -/
theorem threshold_separation {n : ℕ} (hn : 6 ≤ n) (lam : ℝ) (hlam : 0 < lam)
    (P : (Fin n → ℝ) → ℝ → Prop)
    (hsound : ∀ ω K, 0 ≤ K → P ω K → Locked ω (lam * K))
    (hcomp : ∀ a K, 0 < a → a < n → clusterThr n a < lam * K → P (clusterFreq n a) K) :
    sInf {K | 0 ≤ K ∧ P (clusterFreq n 3) K} < sInf {K | 0 ≤ K ∧ P (clusterFreq n 1) K} := by
  have hn0 : 0 < n := by omega
  have hlt := clusterThr_three_lt hn
  have hs3 := clusterThr_pos (n := n) (a := 3) (by norm_num) (by omega)
  set m := (clusterThr n 3 + (n : ℝ) / 2) / 2 with hm
  have hup : sInf {K | 0 ≤ K ∧ P (clusterFreq n 3) K} ≤ m / lam := by
    apply csInf_le ⟨0, fun K hK => hK.1⟩
    refine ⟨by positivity, hcomp 3 _ (by norm_num) (by omega) ?_⟩
    rw [mul_div_cancel₀ _ hlam.ne']; linarith
  have hlow : (n : ℝ) / 2 / lam ≤ sInf {K | 0 ≤ K ∧ P (clusterFreq n 1) K} := by
    have hs1 := clusterThr_pos (n := n) (a := 1) (by norm_num) (by omega)
    apply le_csInf
    · refine ⟨(clusterThr n 1 + 1) / lam, by positivity, hcomp 1 _ (by norm_num) (by omega) ?_⟩
      rw [mul_div_cancel₀ _ hlam.ne']; linarith
    · rintro K ⟨hK0, hP⟩
      have := abs_sub_mean_le_of_locked hn0 (by positivity) (hsound _ K hK0 hP) ⟨0, hn0⟩
      rw [mean_clusterFreq (by norm_num) (by omega), clusterFreq_one_zero hn0, sub_zero,
        abs_of_pos (by positivity)] at this
      rw [div_le_iff₀ hlam]; linarith
  have : m / lam < (n : ℝ) / 2 / lam := by
    apply div_lt_div_of_pos_right _ hlam; linarith
  linarith

/-- No function of the mean absolute deviation equals a threshold `T` separating the clusters. -/
theorem not_function_of_meanAbsDev {n : ℕ} (hn : 6 ≤ n) (T : (Fin n → ℝ) → ℝ)
    (hT : T (clusterFreq n 3) < T (clusterFreq n 1)) :
    ¬ ∃ F : ℝ → ℝ, ∀ ω : Fin n → ℝ, T ω = F (meanAbsDev ω) := by
  rintro ⟨F, hF⟩
  have h3 := hF (clusterFreq n 3)
  have h1 := hF (clusterFreq n 1)
  rw [meanAbsDev_clusterFreq (by norm_num) (by omega)] at h3 h1
  linarith

/-! ## Main results -/

theorem Kc_lt {n : ℕ} (hn : 6 ≤ n) : Kc (clusterFreq n 3) < Kc (clusterFreq n 1) :=
  threshold_separation hn 1 one_pos (fun ω K => Locked ω K)
    (fun ω K _ h => by simpa using h)
    (fun a K ha han hK => ⟨0, clusterPhase n a K, clusterPhase_locked ha han (by linarith)⟩)

/-- **Main theorem.** For every `n ≥ 6`, the critical coupling of `n` all-to-all Kuramoto
oscillators is not `c₁ · (Σᵢ |ωᵢ - ω̄|)/n` for any constant `c₁` (even one depending on `n`). -/
theorem conjecture4082_false {n : ℕ} (hn : 6 ≤ n) :
    ¬ ∃ c₁ : ℝ, ∀ ω : Fin n → ℝ, Kc ω = c₁ * ((∑ i, |ω i - mean ω|) / n) := by
  rintro ⟨c, hc⟩
  exact not_function_of_meanAbsDev hn Kc (Kc_lt hn) ⟨fun x => c * x, hc⟩

/-- The universal-constant statement of the conjecture is false. -/
theorem conjecture4082_false_universal :
    ¬ ∃ c₁ : ℝ, ∀ n : ℕ, ∀ ω : Fin n → ℝ, Kc ω = c₁ * ((∑ i, |ω i - mean ω|) / n) := by
  rintro ⟨c, hc⟩
  exact conjecture4082_false (n := 6) le_rfl ⟨c, hc 6⟩

/-- Stronger: `Kc` is not a function of the mean absolute deviation, for any `n ≥ 6`. -/
theorem Kc_not_function_of_meanAbsDev {n : ℕ} (hn : 6 ≤ n) :
    ¬ ∃ F : ℝ → ℝ, ∀ ω : Fin n → ℝ, Kc ω = F (meanAbsDev ω) :=
  not_function_of_meanAbsDev hn Kc (Kc_lt hn)

/-! ## Variant readings -/

/-- Unnormalised coupling: `ωᵢ + K Σⱼ sin(θⱼ - θᵢ) = Ω`. -/
def LockedUnnorm {n : ℕ} (ω : Fin n → ℝ) (K : ℝ) : Prop :=
  ∃ Ω : ℝ, ∃ θ : Fin n → ℝ, ∀ i, ω i + K * ∑ j, Real.sin (θ j - θ i) = Ω

/-- Phase-cohesive locking: a locked state with all `|θᵢ - θⱼ| < π/2`. -/
def LockedCohesive {n : ℕ} (ω : Fin n → ℝ) (K : ℝ) : Prop :=
  ∃ Ω : ℝ, ∃ θ : Fin n → ℝ, (∀ i j, |θ i - θ j| < π / 2) ∧
    ∀ i, ω i + K / n * ∑ j, Real.sin (θ j - θ i) = Ω

theorem conjecture4082_false_unnormalised {n : ℕ} (hn : 6 ≤ n) :
    ¬ ∃ F : ℝ → ℝ, ∀ ω : Fin n → ℝ,
      sInf {K : ℝ | 0 ≤ K ∧ LockedUnnorm ω K} = F (meanAbsDev ω) := by
  have h6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (n : ℝ) ≠ 0 := by linarith
  refine not_function_of_meanAbsDev hn _ (threshold_separation hn n (by linarith)
    (fun ω K => LockedUnnorm ω K) ?_ ?_)
  · rintro ω K _ ⟨Ω, θ, h⟩
    exact ⟨Ω, θ, fun i => by rw [mul_div_cancel_left₀ _ hn']; exact h i⟩
  · intro a K ha han hK
    refine ⟨0, clusterPhase n a (n * K), fun i => ?_⟩
    have := clusterPhase_locked ha han hK.le i
    rwa [mul_div_cancel_left₀ _ hn'] at this

theorem conjecture4082_false_cohesive {n : ℕ} (hn : 6 ≤ n) :
    ¬ ∃ F : ℝ → ℝ, ∀ ω : Fin n → ℝ,
      sInf {K : ℝ | 0 ≤ K ∧ LockedCohesive ω K} = F (meanAbsDev ω) :=
  not_function_of_meanAbsDev hn _ (threshold_separation hn 1 one_pos
    (fun ω K => LockedCohesive ω K)
    (fun ω K _ ⟨Ω, θ, _, h⟩ => ⟨Ω, θ, by simpa using h⟩)
    (fun a K ha han hK => ⟨0, clusterPhase n a K,
      clusterPhase_cohesive ha han (by simpa using hK),
      clusterPhase_locked ha han (by simpa using hK.le)⟩))

/-- Threshold read as `inf {K ≥ 0 | locked for every K' ≥ K}`. -/
theorem conjecture4082_false_eventual {n : ℕ} (hn : 6 ≤ n) :
    ¬ ∃ F : ℝ → ℝ, ∀ ω : Fin n → ℝ,
      sInf {K : ℝ | 0 ≤ K ∧ ∀ K' ≥ K, Locked ω K'} = F (meanAbsDev ω) :=
  not_function_of_meanAbsDev hn _ (threshold_separation hn 1 one_pos
    (fun ω K => ∀ K' ≥ K, Locked ω K')
    (fun ω K _ h => by simpa using h K le_rfl)
    (fun a K ha han hK K' hK' => ⟨0, clusterPhase n a K',
      clusterPhase_locked ha han (by linarith)⟩))

end C4082

end
