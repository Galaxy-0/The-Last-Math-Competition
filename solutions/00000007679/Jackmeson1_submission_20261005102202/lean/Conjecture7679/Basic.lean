import Mathlib

/-!
# Conjecture 00000007679 (disproof)

For `0 < q < 1` let `[N choose n]_q` be the Gaussian binomial coefficient and
`S_N(z) = ∑_{n=0}^{N} (-1)^n q^{n(n-1)/2} [N choose n]_q z^n`.
The conjecture claims that the zero set of `S_N` converges, as `N → ∞`, to a (quasicircle)
Jordan curve. We prove `S_N(z) = ∏_{k<N} (1 - z q^k)` (finite q-binomial theorem), so every zero
is the real number `q^{-k}`. A Jordan curve cannot lie on the real line, and every notion of
set convergence used below forces the limit curve into the closure of the union of the zero
sets. Hence no Jordan curve (in particular no quasicircle) is such a limit, for every
`q ∈ (0,1)`, also after any real affine normalisation `z ↦ a_N z + b_N` of the zero sets.
-/

open Polynomial Finset Filter Topology Set Metric Real

namespace C7679

/-- The q-Pochhammer symbol `(q;q)_n = ∏_{i<n} (1 - q^{i+1})`. -/
noncomputable def qPoch (q : ℝ) (n : ℕ) : ℝ := ∏ i ∈ range n, (1 - q ^ (i + 1))

/-- The Gaussian binomial coefficient `[N choose k]_q = (q;q)_N / ((q;q)_k (q;q)_{N-k})` for
`k ≤ N`, and `0` for `k > N`. -/
noncomputable def gaussBinom (q : ℝ) (N k : ℕ) : ℝ :=
  if k ≤ N then qPoch q N / (qPoch q k * qPoch q (N - k)) else 0

/-- `S_N(z) = ∑_{n=0}^{N} (-1)^n q^{n(n-1)/2} [N choose n]_q z^n`. -/
noncomputable def S (q : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ range (N + 1), (-1) ^ n * (q : ℂ) ^ (n * (n - 1) / 2) * (gaussBinom q N n : ℂ) * z ^ n

/-- The zero set of `S_N` in the complex plane. -/
def zeroSet (q : ℝ) (N : ℕ) : Set ℂ := {z | S q N z = 0}

/-- A Jordan curve in the plane: the image of a continuous injective map of the circle. -/
def IsJordanCurve (Γ : Set ℂ) : Prop :=
  ∃ γ : Circle → ℂ, Continuous γ ∧ Function.Injective γ ∧ range γ = Γ

lemma qPoch_succ (q : ℝ) (n : ℕ) : qPoch q (n + 1) = qPoch q n * (1 - q ^ (n + 1)) := by
  simp [qPoch, prod_range_succ]

lemma one_sub_pow_pos {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (i : ℕ) : 0 < 1 - q ^ (i + 1) := by
  have : q ^ (i + 1) < 1 := pow_lt_one₀ h0.le h1 (by omega)
  linarith

lemma qPoch_pos {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (n : ℕ) : 0 < qPoch q n :=
  prod_pos fun i _ => one_sub_pow_pos h0 h1 i

lemma gaussBinom_zero_right {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (N : ℕ) :
    gaussBinom q N 0 = 1 := by
  have := (qPoch_pos h0 h1 N).ne'
  have h00 : qPoch q 0 = 1 := by simp [qPoch]
  simp only [gaussBinom, Nat.zero_le, if_true, Nat.sub_zero, h00, one_mul, div_self this]

lemma gaussBinom_of_lt (q : ℝ) {N k : ℕ} (h : N < k) : gaussBinom q N k = 0 := by
  simp [gaussBinom, not_le.mpr h]

/-- The q-Pascal rule `[N+1, k+1] = [N, k+1] + q^{N-k} [N, k]`. -/
lemma gaussBinom_pascal {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (N k : ℕ) :
    gaussBinom q (N + 1) (k + 1) = gaussBinom q N (k + 1) + q ^ (N - k) * gaussBinom q N k := by
  rcases lt_trichotomy k N with hk | rfl | hk
  · obtain ⟨m, rfl⟩ : ∃ m, N = k + 1 + m := ⟨N - (k + 1), by omega⟩
    have e1 : k + 1 + m + 1 - (k + 1) = m + 1 := by omega
    have e2 : k + 1 + m - (k + 1) = m := by omega
    have e3 : k + 1 + m - k = m + 1 := by omega
    simp only [gaussBinom, show k + 1 ≤ k + 1 + m + 1 by omega, show k + 1 ≤ k + 1 + m by omega,
      show k ≤ k + 1 + m by omega, if_true, e1, e2, e3]
    rw [qPoch_succ q (k + 1 + m), qPoch_succ q k, qPoch_succ q m]
    have a := (qPoch_pos h0 h1 (k + 1 + m)).ne'
    have b := (qPoch_pos h0 h1 k).ne'
    have c := (qPoch_pos h0 h1 m).ne'
    have d := (one_sub_pow_pos h0 h1 k).ne'
    have e := (one_sub_pow_pos h0 h1 m).ne'
    field_simp
    ring
  · have a := (qPoch_pos h0 h1 (k + 1)).ne'
    have b := (qPoch_pos h0 h1 k).ne'
    have h00 : qPoch q 0 = 1 := by simp [qPoch]
    rw [gaussBinom_of_lt q (Nat.lt_succ_self k)]
    simp only [gaussBinom, le_refl, if_true, Nat.sub_self, h00, mul_one, div_self a, div_self b,
      pow_zero, zero_add]
  · rw [gaussBinom_of_lt q (by omega : N + 1 < k + 1), gaussBinom_of_lt q (by omega : N < k + 1),
      gaussBinom_of_lt q hk]
    simp

/-- The `n`-th term of `S_N(z)`; it vanishes for `n > N`. -/
noncomputable def term (q : ℝ) (N n : ℕ) (z : ℂ) : ℂ :=
  (-1) ^ n * (q : ℂ) ^ (n * (n - 1) / 2) * (gaussBinom q N n : ℂ) * z ^ n

lemma term_succ {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (N m : ℕ) (z : ℂ) :
    term q (N + 1) (m + 1) z = term q N (m + 1) z - z * (q : ℂ) ^ N * term q N m z := by
  unfold term
  rw [gaussBinom_pascal h0 h1]
  by_cases hm : m ≤ N
  · have hexp : (m + 1) * (m + 1 - 1) / 2 + (N - m) = N + m * (m - 1) / 2 := by
      rw [Nat.triangle_succ]; omega
    have : (q : ℂ) ^ ((m + 1) * (m + 1 - 1) / 2) * (q : ℂ) ^ (N - m) =
        (q : ℂ) ^ N * (q : ℂ) ^ (m * (m - 1) / 2) := by
      rw [← pow_add, ← pow_add, hexp]
    rw [Nat.add_sub_cancel] at this
    push_cast
    linear_combination (-1) ^ (m + 1) * (gaussBinom q N m : ℂ) * z ^ (m + 1) * this
  · rw [gaussBinom_of_lt q (by omega : N < m)]
    simp

lemma S_eq_sum_term (q : ℝ) (N : ℕ) (z : ℂ) : S q N z = ∑ n ∈ range (N + 1), term q N n z := rfl

lemma S_succ {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (N : ℕ) (z : ℂ) :
    S q (N + 1) z = (1 - z * (q : ℂ) ^ N) * S q N z := by
  have t0 : ∀ M, term q M 0 z = 1 := fun M => by
    simp [term, gaussBinom_zero_right h0 h1]
  have tN : term q N (N + 1) z = 0 := by
    simp [term, gaussBinom_of_lt q (Nat.lt_succ_self N)]
  have hS : S q N z = ∑ n ∈ range (N + 2), term q N n z := by
    rw [S_eq_sum_term, sum_range_succ _ (N + 1), tN, add_zero]
  rw [S_eq_sum_term, sum_range_succ', t0]
  simp only [term_succ h0 h1, sum_sub_distrib, ← mul_sum]
  rw [← S_eq_sum_term]
  have h2 : ∑ m ∈ range (N + 1), term q N (m + 1) z = S q N z - 1 := by
    rw [hS, sum_range_succ' (fun n => term q N n z) (N + 1), t0]; ring
  rw [h2]; ring

/-- Finite q-binomial theorem: `S_N(z) = ∏_{k<N} (1 - z q^k)`. -/
theorem S_eq_prod {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (N : ℕ) (z : ℂ) :
    S q N z = ∏ k ∈ range N, (1 - z * (q : ℂ) ^ k) := by
  induction N with
  | zero => simp [S, gaussBinom, qPoch]
  | succ N ih => rw [S_succ h0 h1, ih, prod_range_succ, mul_comm]

/-- The zero set of `S_N` is exactly `{q^{-k} : k < N}`. -/
theorem zeroSet_eq {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (N : ℕ) :
    zeroSet q N = (fun k : ℕ => ((q ^ k)⁻¹ : ℝ) : ℕ → ℂ) '' Set.Iio N := by
  ext z
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  simp only [zeroSet, Set.mem_ofPred_eq, S_eq_prod h0 h1, prod_eq_zero_iff, Set.mem_image,
    Finset.mem_range, Set.mem_Iio, sub_eq_zero]
  refine exists_congr fun k => and_congr_right fun _ => ?_
  push_cast
  constructor
  · intro h; field_simp; linear_combination h
  · intro h; rw [← h]; field_simp

/-- Every zero of `S_N` is real. -/
lemma zeroSet_real {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (N : ℕ) : zeroSet q N ⊆ {z : ℂ | z.im = 0} := by
  rw [zeroSet_eq h0 h1]
  rintro _ ⟨k, -, rfl⟩
  exact Complex.ofReal_im _

/-- A Jordan curve is not contained in the real line. -/
theorem jordan_not_subset_real {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) : ¬ Γ ⊆ {z : ℂ | z.im = 0} := by
  obtain ⟨γ, hc, hi, rfl⟩ := hΓ
  intro hsub
  have him : ∀ t, (γ (Circle.exp t)).im = 0 := fun t => hsub ⟨_, rfl⟩
  have key : ∀ s t, (γ (Circle.exp s)).re = (γ (Circle.exp t)).re → Circle.exp s = Circle.exp t :=
    fun s t h => hi (Complex.ext h (by rw [him, him]))
  set f : ℝ → ℝ := fun t => (γ (Circle.exp t)).re with hf
  have fc : Continuous f := Complex.continuous_re.comp (hc.comp Circle.exp.continuous)
  have inj : InjOn Circle.exp (Ico 0 (2 * π)) := Circle.exp_injOn_Ico (by linarith)
  have hπ := Real.pi_pos
  have f2 : f (2 * π) = f 0 := by simp [hf, Circle.exp_zero]
  have f0π : f 0 ≠ f π := by
    intro h
    have := inj ⟨le_rfl, by linarith⟩ ⟨hπ.le, by linarith⟩ (key 0 π h)
    linarith
  set c := (f 0 + f π) / 2 with hcdef
  have hc0 : c ≠ f 0 := by intro h; apply f0π; linarith
  have hcπ : c ≠ f π := by intro h; apply f0π; linarith
  have mem1 : c ∈ uIcc (f 0) (f π) := by
    rcases le_total (f 0) (f π) with h | h
    · rw [Set.uIcc_of_le h]; constructor <;> linarith
    · rw [Set.uIcc_of_ge h]; constructor <;> linarith
  have mem2 : c ∈ uIcc (f π) (f (2 * π)) := by rw [f2, Set.uIcc_comm]; exact mem1
  obtain ⟨s, hs, hfs⟩ := intermediate_value_uIcc fc.continuousOn mem1
  obtain ⟨t, ht, hft⟩ := intermediate_value_uIcc fc.continuousOn mem2
  rw [Set.uIcc_of_le hπ.le] at hs
  rw [Set.uIcc_of_le (by linarith : π ≤ 2 * π)] at ht
  have hsπ : s ≠ π := by rintro rfl; exact hcπ hfs.symm
  have htπ : t ≠ π := by rintro rfl; exact hcπ hft.symm
  have ht2 : t ≠ 2 * π := by rintro rfl; rw [f2] at hft; exact hc0 hft.symm
  have hst := inj ⟨hs.1, by linarith [hs.2]⟩ ⟨by linarith [ht.1], lt_of_le_of_ne ht.2 ht2⟩
    (key s t (hfs.trans hft.symm))
  have : s < π := lt_of_le_of_ne hs.2 hsπ
  have : π < t := lt_of_le_of_ne ht.1 (Ne.symm htπ)
  linarith

/-- If sets `Y N` of real numbers converge to `Γ` in the Hausdorff (extended) distance, then
`Γ` lies in the closure of their union. -/
lemma subset_closure_of_tendsto {Y : ℕ → Set ℂ} {Γ : Set ℂ}
    (h : Tendsto (fun N => hausdorffEDist (Y N) Γ) atTop (𝓝 0)) : Γ ⊆ closure (⋃ N, Y N) := by
  intro x hx
  rw [mem_closure_iff_infEDist_zero]
  refine le_antisymm (ge_of_tendsto' h fun N => ?_) bot_le
  calc infEDist x (⋃ N, Y N) ≤ infEDist x (Y N) := infEDist_anti (subset_iUnion Y N)
    _ ≤ hausdorffEDist Γ (Y N) := infEDist_le_hausdorffEDist_of_mem hx
    _ = hausdorffEDist (Y N) Γ := hausdorffEDist_comm

/-- The real affine normalisation `z ↦ a z + b` of a set. -/
def affineImage (a b : ℝ) (Y : Set ℂ) : Set ℂ := (fun z => (a : ℂ) * z + b) '' Y

/-- **Main theorem.** For every `q ∈ (0,1)`:
1. `S_N(z) = ∏_{k<N} (1 - z q^k)` and its zero set is `{q^{-k} : k < N}`;
2. for all real normalising sequences `a N, b N` (e.g. `a = 1, b = 0`: no normalisation), no
   Jordan curve lies in the closure of the union of the normalised zero sets; so no Jordan curve
   is a limit of them in any sense in which every point of the limit is a limit (or cluster
   point) of zeros;
3. in particular no Jordan curve is the Hausdorff limit of the (normalised) zero sets. -/
theorem conjecture_7679_false (q : ℝ) (h0 : 0 < q) (h1 : q < 1) :
    (∀ N z, S q N z = ∏ k ∈ range N, (1 - z * (q : ℂ) ^ k)) ∧
    (∀ N, zeroSet q N = (fun k : ℕ => ((q ^ k)⁻¹ : ℝ) : ℕ → ℂ) '' Set.Iio N) ∧
    (∀ (a b : ℕ → ℝ) (Γ : Set ℂ), IsJordanCurve Γ →
      ¬ Γ ⊆ closure (⋃ N, affineImage (a N) (b N) (zeroSet q N))) ∧
    (∀ (a b : ℕ → ℝ), ¬ ∃ Γ : Set ℂ, IsJordanCurve Γ ∧
      Tendsto (fun N => hausdorffEDist (affineImage (a N) (b N) (zeroSet q N)) Γ) atTop (𝓝 0)) := by
  have real : ∀ (a b : ℕ → ℝ), closure (⋃ N, affineImage (a N) (b N) (zeroSet q N)) ⊆
      {z : ℂ | z.im = 0} := by
    intro a b
    refine closure_minimal (iUnion_subset fun N => ?_) (isClosed_eq Complex.continuous_im
      continuous_const)
    rintro _ ⟨z, hz, rfl⟩
    have : z.im = 0 := zeroSet_real h0 h1 N hz
    simp [this]
  refine ⟨S_eq_prod h0 h1, zeroSet_eq h0 h1, fun a b Γ hΓ hsub =>
    jordan_not_subset_real hΓ (hsub.trans (real a b)), fun a b ⟨Γ, hΓ, ht⟩ =>
    jordan_not_subset_real hΓ ((subset_closure_of_tendsto ht).trans (real a b))⟩

end C7679
