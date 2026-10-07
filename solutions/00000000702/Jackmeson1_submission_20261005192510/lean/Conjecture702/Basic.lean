import Mathlib

/-!
# Conjecture 00000000702 (disproved)

Conjecture: the Browkin expansion of an algebraic number is never eventually periodic, and its
partial quotients are unbounded.

For every odd prime `p` we build `α ∈ ℚ_[p]` with `p α² - α - p = 0` and `α - 1/p ∈ pℤ_p`
(Hensel's lemma).  It is algebraic and irrational.  Browkin's first algorithm gives the purely
periodic expansion `[1/p; 1/p, 1/p, ...]`, and Browkin's second algorithm gives an eventually
periodic expansion (period 4 from index 2).  In both cases the partial quotients take finitely
many values, so their `p`-adic absolute values are bounded.

Definitions follow Capuano-Murru-Terracini (arXiv:2010.07364, Sec. 2) for `s` and the first
algorithm, and Murru-Romeo-Santilli (arXiv:2201.12019, eq. (2)) for `t` and the second algorithm.
-/

open Polynomial

namespace C702

variable {p : ℕ} [hp : Fact p.Prime]

/-- `ℤ[1/p]`, as a subset of `ℚ`. -/
def ZInvP (p : ℕ) : Set ℚ := {y | ∃ k : ℕ, ∃ m : ℤ, y = m / (p : ℚ) ^ k}

/-- Browkin's digit set `J_p = ℤ[1/p] ∩ (-p/2, p/2)`. -/
def browkinJ (p : ℕ) : Set ℚ := {y | y ∈ ZInvP p ∧ |y| < (p : ℚ) / 2}

/-- The set `K_p = ℤ[1/p] ∩ (-1/2, 1/2)` used by `t`. -/
def browkinK (p : ℕ) : Set ℚ := {y | y ∈ ZInvP p ∧ |y| < 1 / 2}

/-- Browkin's `s`-function: the element `s(x) ∈ J_p` with `|x - s(x)|_p < 1`
(unique and existent for odd `p`, see `browkinS_spec` and `browkinS_eq`). -/
noncomputable def browkinS (x : ℚ_[p]) : ℚ :=
  Classical.epsilon fun y : ℚ => y ∈ browkinJ p ∧ ‖x - (y : ℚ_[p])‖ < 1

/-- Browkin's `t`-function: the element `t(x) ∈ K_p` with `|x - t(x)|_p ≤ 1`
(this is the sum of the digits of `x` at negative powers of `p`). -/
noncomputable def browkinT (x : ℚ_[p]) : ℚ :=
  Classical.epsilon fun y : ℚ => y ∈ browkinK p ∧ ‖x - (y : ℚ_[p])‖ ≤ 1

/-- Complete quotients of Browkin's first algorithm: `α₀ = α`, `α_{n+1} = 1/(α_n - s(α_n))`. -/
noncomputable def bcfCQ (α : ℚ_[p]) : ℕ → ℚ_[p]
  | 0 => α
  | n + 1 => (bcfCQ α n - (browkinS (bcfCQ α n) : ℚ_[p]))⁻¹

/-- Partial quotients of Browkin's first algorithm: `a_n = s(α_n)`. -/
noncomputable def bcfPQ (α : ℚ_[p]) (n : ℕ) : ℚ := browkinS (bcfCQ α n)

/-- The `n`-th step of Browkin's second algorithm: `s` at even steps; at odd steps `t(x)` if
`v_p(x - t(x)) = 0` (equivalently `|x - t(x)|_p = 1`), and `t(x) - sign(t(x))` otherwise. -/
noncomputable def browkin2Digit (n : ℕ) (x : ℚ_[p]) : ℚ :=
  if Even n then browkinS x
  else if ‖x - (browkinT x : ℚ_[p])‖ = 1 then browkinT x
  else browkinT x - (SignType.sign (browkinT x) : ℚ)

/-- Complete quotients of Browkin's second algorithm. -/
noncomputable def bcf2CQ (α : ℚ_[p]) : ℕ → ℚ_[p]
  | 0 => α
  | n + 1 => (bcf2CQ α n - (browkin2Digit n (bcf2CQ α n) : ℚ_[p]))⁻¹

/-- Partial quotients of Browkin's second algorithm. -/
noncomputable def bcf2PQ (α : ℚ_[p]) (n : ℕ) : ℚ := browkin2Digit n (bcf2CQ α n)

/-- A sequence is eventually periodic. -/
def EventuallyPeriodic {β : Type*} (b : ℕ → β) : Prop :=
  ∃ N k : ℕ, 0 < k ∧ ∀ n, N ≤ n → b (n + k) = b n

/-- The partial quotients have bounded `p`-adic absolute value. -/
def PadicBounded (p : ℕ) [Fact p.Prime] (b : ℕ → ℚ) : Prop :=
  ∃ C : ℝ, ∀ n, ‖((b n : ℚ) : ℚ_[p])‖ ≤ C

/-! ### Uniqueness and existence of `s` and `t` -/

lemma zinvp_sub {y y' : ℚ} (hy : y ∈ ZInvP p) (hy' : y' ∈ ZInvP p) : y - y' ∈ ZInvP p := by
  obtain ⟨k, m, rfl⟩ := hy
  obtain ⟨k', m', rfl⟩ := hy'
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  refine ⟨k + k', m * p ^ k' - m' * p ^ k, ?_⟩
  push_cast
  field_simp
  ring

lemma eq_zero_of_small {d : ℚ} (hd : d ∈ ZInvP p) (j : ℕ)
    (hn : ‖(d : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(j : ℤ))) (ha : |d| < (p : ℚ) ^ j) : d = 0 := by
  obtain ⟨K, M, rfl⟩ := hd
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp0' : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hM : ‖((M : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((j + K : ℕ) : ℤ)) := by
    have : ((M : ℤ) : ℚ_[p]) = (((M : ℚ) / (p : ℚ) ^ K : ℚ) : ℚ_[p]) * (p : ℚ_[p]) ^ K := by
      push_cast
      field_simp
    rw [this, norm_mul, Padic.norm_p_pow]
    calc _ ≤ (p : ℝ) ^ (-(j : ℤ)) * (p : ℝ) ^ (-(K : ℤ)) := by gcongr
      _ = _ := by rw [← zpow_add₀ hpR.ne']; push_cast; ring_nf
  obtain ⟨c, hc⟩ := (Padic.norm_int_le_pow_iff_dvd M (j + K)).1 hM
  subst hc
  have hval : ((((p : ℤ) ^ (j + K) * c : ℤ) : ℚ) / (p : ℚ) ^ K) = (p : ℚ) ^ j * c := by
    push_cast
    field_simp
    ring
  rw [hval] at ha ⊢
  have hpj : (0 : ℚ) < (p : ℚ) ^ j := by positivity
  rw [abs_mul, abs_of_pos hpj] at ha
  have hc1 : |(c : ℚ)| < 1 := by
    by_contra h
    push Not at h
    nlinarith
  have : c = 0 := by
    have : |c| < 1 := by exact_mod_cast hc1
    exact Int.abs_lt_one_iff.mp this
  simp [this]

lemma s_unique {x : ℚ_[p]} {y z : ℚ} (hy : y ∈ browkinJ p) (hz : z ∈ browkinJ p)
    (hxy : ‖x - (y : ℚ_[p])‖ < 1) (hxz : ‖x - (z : ℚ_[p])‖ < 1) : z = y := by
  have hlt : ‖((z - y : ℚ) : ℚ_[p])‖ < 1 := by
    have : ((z - y : ℚ) : ℚ_[p]) = (x - y) + ((z : ℚ_[p]) - x) := by push_cast; ring
    rw [this]
    exact (Padic.nonarchimedean _ _).trans_lt (max_lt hxy (by rwa [norm_sub_rev]))
  have hle : ‖((z - y : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ)) :=
    (Padic.norm_le_pow_iff_norm_lt_pow_add_one _ _).2 (by simpa using hlt)
  have h0 := eq_zero_of_small (zinvp_sub hz.1 hy.1) 1 hle (by
    have := hy.2; have := hz.2
    calc |z - y| ≤ |z| + |y| := abs_sub _ _
      _ < (p : ℚ) / 2 + (p : ℚ) / 2 := by linarith
      _ = (p : ℚ) ^ 1 := by ring)
  linarith

lemma t_unique {x : ℚ_[p]} {y z : ℚ} (hy : y ∈ browkinK p) (hz : z ∈ browkinK p)
    (hxy : ‖x - (y : ℚ_[p])‖ ≤ 1) (hxz : ‖x - (z : ℚ_[p])‖ ≤ 1) : z = y := by
  have hle : ‖((z - y : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((0 : ℕ) : ℤ)) := by
    have : ((z - y : ℚ) : ℚ_[p]) = (x - y) + ((z : ℚ_[p]) - x) := by push_cast; ring
    rw [this, show (p : ℝ) ^ (-((0 : ℕ) : ℤ)) = 1 by simp]
    exact (Padic.nonarchimedean _ _).trans (max_le hxy (by rwa [norm_sub_rev]))
  have h0 := eq_zero_of_small (zinvp_sub hz.1 hy.1) 0 hle (by
    have := hy.2; have := hz.2
    calc |z - y| ≤ |z| + |y| := abs_sub _ _
      _ < 1 / 2 + 1 / 2 := by linarith
      _ = (p : ℚ) ^ 0 := by ring)
  linarith

/-- `s(x)` is determined by its defining property. -/
lemma browkinS_eq {x : ℚ_[p]} {y : ℚ} (hy : y ∈ browkinJ p) (hxy : ‖x - (y : ℚ_[p])‖ < 1) :
    browkinS x = y :=
  let h := Classical.epsilon_spec
    (p := fun y : ℚ => y ∈ browkinJ p ∧ ‖x - (y : ℚ_[p])‖ < 1) ⟨y, hy, hxy⟩
  s_unique hy h.1 hxy h.2

/-- `t(x)` is determined by its defining property. -/
lemma browkinT_eq {x : ℚ_[p]} {y : ℚ} (hy : y ∈ browkinK p) (hxy : ‖x - (y : ℚ_[p])‖ ≤ 1) :
    browkinT x = y :=
  let h := Classical.epsilon_spec
    (p := fun y : ℚ => y ∈ browkinK p ∧ ‖x - (y : ℚ_[p])‖ ≤ 1) ⟨y, hy, hxy⟩
  t_unique hy h.1 hxy h.2

/-- Balanced approximation: `x` is within `p^{-j}` of some `m / p^k` with `2|m| < p^(k+j)`. -/
lemma exists_approx (hp2 : p ≠ 2) (x : ℚ_[p]) (j : ℕ) :
    ∃ k : ℕ, ∃ m : ℤ, ‖x - (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(j : ℤ)) ∧
      2 * |m| < (p : ℤ) ^ (k + j) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖x‖ hpR
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  have hu : ‖(p : ℚ_[p]) ^ k * x‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast, inv_mul_le_iff₀ hpk]
    linarith
  let u : ℤ_[p] := ⟨(p : ℚ_[p]) ^ k * x, hu⟩
  have hucoe : (u : ℚ_[p]) = (p : ℚ_[p]) ^ k * x := rfl
  have : NeZero (p ^ (k + j)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  let m0 : ℕ := u.appr (k + j)
  let m : ℤ := ((m0 : ZMod (p ^ (k + j)))).valMinAbs
  have h1 : ‖u - (m0 : ℤ_[p])‖ ≤ (p : ℝ) ^ (-((k + j : ℕ) : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 (PadicInt.appr_spec _ _)
  have hdvd : ((p : ℤ) ^ (k + j)) ∣ ((m0 : ℤ) - m) := by
    have h : ((m : ℤ) : ZMod (p ^ (k + j))) = ((m0 : ℤ) : ZMod (p ^ (k + j))) := by
      simp [m, ZMod.coe_valMinAbs]
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
    exact_mod_cast this
  have h2 : ‖(((m0 : ℤ) - m : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-((k + j : ℕ) : ℤ)) :=
    PadicInt.norm_int_le_pow_iff_dvd.2 (by exact_mod_cast hdvd)
  have h3 : ‖u - (m : ℤ_[p])‖ ≤ (p : ℝ) ^ (-((k + j : ℕ) : ℤ)) := by
    have : u - (m : ℤ_[p]) = (u - (m0 : ℤ_[p])) + (((m0 : ℤ) - m : ℤ) : ℤ_[p]) := by
      push_cast; ring
    rw [this]
    exact (PadicInt.nonarchimedean _ _).trans (max_le h1 h2)
  refine ⟨k, m, ?_, ?_⟩
  · have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have heq : x - (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p]) =
        ((p : ℚ_[p]) ^ k)⁻¹ * ((u : ℚ_[p]) - (m : ℚ_[p])) := by
      rw [hucoe]; push_cast; field_simp
    have h3' : ‖(u : ℚ_[p]) - (m : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k + j : ℕ) : ℤ)) := by
      simpa [PadicInt.norm_def] using h3
    rw [heq, norm_mul, norm_inv, Padic.norm_p_pow]
    calc ((p : ℝ) ^ (-(k : ℤ)))⁻¹ * ‖(u : ℚ_[p]) - (m : ℚ_[p])‖
        ≤ ((p : ℝ) ^ (-(k : ℤ)))⁻¹ * (p : ℝ) ^ (-((k + j : ℕ) : ℤ)) := by gcongr
      _ = (p : ℝ) ^ (-(j : ℤ)) := by
        rw [← zpow_neg, ← zpow_add₀ (by positivity)]; push_cast; ring_nf
  · have hodd : Odd (p ^ (k + j)) := (hp.out.eq_two_or_odd'.resolve_left hp2).pow
    have hle := ZMod.natAbs_valMinAbs_le (n := p ^ (k + j)) (m0 : ZMod (p ^ (k + j)))
    have : 2 * m.natAbs < p ^ (k + j) := by
      obtain ⟨r, hr⟩ := hodd
      have : m.natAbs ≤ p ^ (k + j) / 2 := hle
      omega
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this

/-- For odd `p`, `s(x)` exists: `s(x) ∈ J_p` and `|x - s(x)|_p < 1`. -/
theorem browkinS_spec (hp2 : p ≠ 2) (x : ℚ_[p]) :
    browkinS x ∈ browkinJ p ∧ ‖x - (browkinS x : ℚ_[p])‖ < 1 := by
  obtain ⟨k, m, h1, h2⟩ := exists_approx hp2 x 1
  refine Classical.epsilon_spec (p := fun y : ℚ => y ∈ browkinJ p ∧ ‖x - (y : ℚ_[p])‖ < 1)
    ⟨(m : ℚ) / (p : ℚ) ^ k, ⟨⟨k, m, rfl⟩, ?_⟩, h1.trans_lt ?_⟩
  · have hpk : (0 : ℚ) < (p : ℚ) ^ k := pow_pos (by exact_mod_cast hp.out.pos) _
    have h2' : (2 * |(m : ℚ)| : ℚ) < (p : ℚ) ^ (k + 1) := by exact_mod_cast h2
    rw [abs_div, abs_of_pos hpk, div_lt_div_iff₀ hpk (by norm_num), pow_succ] at *
    linarith
  · have hpR : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    simpa using inv_lt_one_of_one_lt₀ hpR

/-- For odd `p`, `t(x)` exists: `t(x) ∈ K_p` and `|x - t(x)|_p ≤ 1`. -/
theorem browkinT_spec (hp2 : p ≠ 2) (x : ℚ_[p]) :
    browkinT x ∈ browkinK p ∧ ‖x - (browkinT x : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨k, m, h1, h2⟩ := exists_approx hp2 x 0
  refine Classical.epsilon_spec (p := fun y : ℚ => y ∈ browkinK p ∧ ‖x - (y : ℚ_[p])‖ ≤ 1)
    ⟨(m : ℚ) / (p : ℚ) ^ k, ⟨⟨k, m, rfl⟩, ?_⟩, by simpa using h1⟩
  have hpk : (0 : ℚ) < (p : ℚ) ^ k := pow_pos (by exact_mod_cast hp.out.pos) _
  have h2' : (2 * |(m : ℚ)| : ℚ) < (p : ℚ) ^ k := by exact_mod_cast h2
  rw [abs_div, abs_of_pos hpk, div_lt_div_iff₀ hpk (by norm_num)]
  linarith

/-! ### Generic facts about eventually periodic sequences -/

lemma exists_lt_of_periodic {β : Type*} {b : ℕ → β} {N k : ℕ} (hk : 0 < k)
    (h : ∀ n, N ≤ n → b (n + k) = b n) : ∀ n, ∃ m < N + k, b n = b m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < N + k
    · exact ⟨n, hn, rfl⟩
    · obtain ⟨m, hm, he⟩ := ih (n - k) (by omega)
      refine ⟨m, hm, ?_⟩
      have := h (n - k) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at this
      rw [this, he]

lemma EventuallyPeriodic.finite_range {β : Type*} {b : ℕ → β} (h : EventuallyPeriodic b) :
    (Set.range b).Finite := by
  classical
  obtain ⟨N, k, hk, h⟩ := h
  apply ((Finset.range (N + k)).image b).finite_toSet.subset
  rintro _ ⟨n, rfl⟩
  obtain ⟨m, hm, he⟩ := exists_lt_of_periodic hk h n
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
  exact ⟨m, hm, he.symm⟩

lemma padicBounded_of_finite {b : ℕ → ℚ} (h : (Set.range b).Finite) : PadicBounded p b := by
  obtain ⟨C, hC⟩ := (h.image (fun q : ℚ => ‖(q : ℚ_[p])‖)).bddAbove
  exact ⟨C, fun n => hC ⟨b n, ⟨n, rfl⟩, rfl⟩⟩

/-! ### The counterexample -/

/-- Hensel's lemma at `0` for `p X² + X - p`: a root `β` with `|β|_p < 1`. -/
lemma exists_beta : ∃ b : ℚ_[p], (p : ℚ_[p]) * b ^ 2 + b - p = 0 ∧ ‖b‖ < 1 := by
  let F : Polynomial ℤ := C (p : ℤ) * X ^ 2 + X - C (p : ℤ)
  have hF0 : F.aeval (0 : ℤ_[p]) = -(p : ℤ_[p]) := by simp [F]
  have hF1 : (derivative F).aeval (0 : ℤ_[p]) = 1 := by simp [F]
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hnorm : ‖F.aeval (0 : ℤ_[p])‖ < ‖(derivative F).aeval (0 : ℤ_[p])‖ ^ 2 := by
    rw [hF0, hF1, norm_neg, PadicInt.norm_p, norm_one, one_pow]
    exact inv_lt_one_of_one_lt₀ hpR
  obtain ⟨z, hz, hz1, -, -⟩ := hensels_lemma hnorm
  refine ⟨(z : ℚ_[p]), ?_, ?_⟩
  · have h : (p : ℤ_[p]) * z ^ 2 + z - p = 0 := by simpa [F] using hz
    have := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) h
    push_cast at this
    exact this
  · rw [hF1, norm_one, sub_zero] at hz1
    exact hz1

lemma alpha_algebraic {α : ℚ_[p]} (hα : (p : ℚ_[p]) * α ^ 2 - α - p = 0) :
    IsAlgebraic ℚ α := by
  refine ⟨C (p : ℚ) * X ^ 2 - X - C (p : ℚ), ?_, ?_⟩
  · intro h
    have := congrArg (fun q => Polynomial.coeff q 0) h
    simp at this
    exact hp.out.ne_zero this
  · simpa using hα

lemma alpha_irrational {α : ℚ_[p]} (hα : (p : ℚ_[p]) * α ^ 2 - α - p = 0) (r : ℚ) :
    (r : ℚ_[p]) ≠ α := by
  intro h
  have hr : (p : ℚ) * r ^ 2 - r - p = 0 := by
    have : (((p : ℚ) * r ^ 2 - r - p : ℚ) : ℚ_[p]) = 0 := by push_cast; rw [h]; exact hα
    exact_mod_cast this
  have hsq : IsSquare ((4 * p ^ 2 + 1 : ℕ) : ℚ) :=
    ⟨2 * p * r - 1, by push_cast; linear_combination (-(4 * (p : ℚ))) * hr⟩
  obtain ⟨m, hm⟩ := Rat.isSquare_natCast_iff.1 hsq
  rcases le_or_gt m (2 * p) with h1 | h1
  · have := Nat.mul_le_mul h1 h1
    nlinarith
  · have := Nat.mul_le_mul h1 h1
    nlinarith [hp.out.pos]

lemma three_le (hp2 : p ≠ 2) : (3 : ℚ) ≤ p := by
  have := hp.out.two_le
  have : 3 ≤ p := by omega
  exact_mod_cast this

lemma inv_p_mem_J (hp2 : p ≠ 2) : (1 / p : ℚ) ∈ browkinJ p := by
  have h3 := three_le hp2
  refine ⟨⟨1, 1, by simp⟩, ?_⟩
  rw [abs_of_pos (by positivity), div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma inv_p_mem_K (hp2 : p ≠ 2) : (1 / p : ℚ) ∈ browkinK p := by
  have h3 := three_le hp2
  refine ⟨⟨1, 1, by simp⟩, ?_⟩
  rw [abs_of_pos (by positivity), div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

lemma neg_inv_p_mem_K (hp2 : p ≠ 2) : (-1 / p : ℚ) ∈ browkinK p := by
  have h3 := three_le hp2
  refine ⟨⟨1, -1, by simp⟩, ?_⟩
  rw [neg_div, abs_neg, abs_of_pos (by positivity), div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

lemma pm_one_mem_J (hp2 : p ≠ 2) (e : ℤ) (he : e = 1 ∨ e = -1) : (e : ℚ) ∈ browkinJ p := by
  have h3 := three_le hp2
  refine ⟨⟨0, e, by simp⟩, ?_⟩
  rcases he with rfl | rfl <;> norm_num <;> linarith

lemma browkin2Digit_add_four (n : ℕ) : browkin2Digit (p := p) (n + 4) = browkin2Digit n := by
  have h : Even (n + 4) ↔ Even n := by
    rw [Nat.even_add]; have : Even 4 := ⟨2, rfl⟩; tauto
  funext x
  simp only [browkin2Digit, h]

section Example

variable (hp2 : p ≠ 2) {b : ℚ_[p]} (hb : (p : ℚ_[p]) * b ^ 2 + b - p = 0) (hb1 : ‖b‖ < 1)
include hp2 hb hb1

omit hp2 hb1 in
lemma b_ne_zero : b ≠ 0 := by
  rintro rfl
  simp at hb
  exact hp.out.ne_zero hb

omit hp2 hb1 in
lemma alpha_sub : b⁻¹ - (((1 / p : ℚ)) : ℚ_[p]) = b := by
  have hb0 := b_ne_zero hb
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  push_cast
  field_simp
  linear_combination -hb

omit hp2 hb1 in
lemma alpha_eq : (p : ℚ_[p]) * b⁻¹ ^ 2 - b⁻¹ - p = 0 := by
  have hb0 := b_ne_zero hb
  field_simp
  linear_combination -hb

omit hp2 hb in
lemma one_add_b : ‖1 + b‖ = 1 := by
  rw [Padic.add_eq_max_of_ne (by rw [norm_one]; exact hb1.ne'), norm_one]
  exact max_eq_left hb1.le

lemma s_alpha : browkinS b⁻¹ = 1 / p :=
  browkinS_eq (inv_p_mem_J hp2) (by rw [alpha_sub hb]; exact hb1)

/-- Browkin I: every complete quotient of `α = 1/β` is `α` itself. -/
lemma bcfCQ_alpha (n : ℕ) : bcfCQ b⁻¹ n = b⁻¹ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bcfCQ, ih, s_alpha hp2 hb hb1, alpha_sub hb]

lemma bcfPQ_alpha (n : ℕ) : bcfPQ b⁻¹ n = 1 / p := by
  rw [bcfPQ, bcfCQ_alpha hp2 hb hb1, s_alpha hp2 hb hb1]

/-- Browkin II, explicitly: complete quotients `α, α, w, -α-1, -w, α+1, w` with
`w = 1/(1+β)`, and partial quotients `1/p, 1/p - 1, 1, -1/p, -1, 1/p`. -/
lemma bcf2_first_steps :
    bcf2CQ b⁻¹ 1 = b⁻¹ ∧ bcf2CQ b⁻¹ 2 = (1 + b)⁻¹ ∧ bcf2CQ b⁻¹ 3 = -b⁻¹ - 1 ∧
    bcf2CQ b⁻¹ 4 = -(1 + b)⁻¹ ∧ bcf2CQ b⁻¹ 5 = b⁻¹ + 1 ∧ bcf2CQ b⁻¹ 6 = (1 + b)⁻¹ ∧
    bcf2PQ b⁻¹ 0 = 1 / p ∧ bcf2PQ b⁻¹ 1 = 1 / p - 1 ∧ bcf2PQ b⁻¹ 2 = 1 ∧
    bcf2PQ b⁻¹ 3 = -1 / p ∧ bcf2PQ b⁻¹ 4 = -1 ∧ bcf2PQ b⁻¹ 5 = 1 / p := by
  have hb0 := b_ne_zero hb
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h1b := one_add_b hb1
  have h1b0 : 1 + b ≠ 0 := by intro h; rw [h, norm_zero] at h1b; exact zero_ne_one h1b
  have hsub := alpha_sub hb
  have hpinv : (((1 / p : ℚ)) : ℚ_[p]) = (p : ℚ_[p])⁻¹ := by push_cast; ring
  rw [hpinv] at hsub
  have hw : ‖(1 + b)⁻¹ - ((1 : ℤ) : ℚ)‖ < 1 := by
    have : (1 + b)⁻¹ - (((1 : ℤ) : ℚ) : ℚ_[p]) = -b * (1 + b)⁻¹ := by
      push_cast; field_simp; ring
    rw [this, norm_mul, norm_neg, norm_inv, h1b, inv_one, mul_one]
    exact hb1
  -- step 0
  have d0 : browkin2Digit 0 b⁻¹ = 1 / p := by
    rw [browkin2Digit, if_pos (by decide), s_alpha hp2 hb hb1]
  have c1 : bcf2CQ b⁻¹ 1 = b⁻¹ := by
    rw [bcf2CQ, bcf2CQ, d0, hpinv, hsub]
  -- step 1
  have t1 : browkinT b⁻¹ = 1 / p :=
    browkinT_eq (inv_p_mem_K hp2) (by rw [alpha_sub hb]; exact hb1.le)
  have d1 : browkin2Digit 1 b⁻¹ = 1 / p - 1 := by
    have hpos : (0 : ℚ) < 1 / p := by have := three_le hp2; positivity
    rw [browkin2Digit, if_neg (by decide), t1, if_neg (by rw [hpinv, hsub]; exact hb1.ne),
      sign_pos hpos]
    simp
  have c2 : bcf2CQ b⁻¹ 2 = (1 + b)⁻¹ := by
    rw [bcf2CQ, c1, d1]
    congr 1
    push_cast
    linear_combination hsub
  -- step 2
  have d2 : browkin2Digit 2 (1 + b)⁻¹ = 1 := by
    rw [browkin2Digit, if_pos (by decide)]
    exact_mod_cast browkinS_eq (pm_one_mem_J hp2 1 (Or.inl rfl)) hw
  have c3 : bcf2CQ b⁻¹ 3 = -b⁻¹ - 1 := by
    rw [bcf2CQ, c2, d2]
    push_cast
    apply inv_eq_of_mul_eq_one_right
    field_simp
    ring
  -- step 3
  have hx3 : -b⁻¹ - 1 - (((-1 / p : ℚ)) : ℚ_[p]) = -(1 + b) := by
    push_cast; linear_combination -hsub
  have t3 : browkinT (-b⁻¹ - 1) = -1 / p :=
    browkinT_eq (neg_inv_p_mem_K hp2) (by rw [hx3, norm_neg, h1b])
  have d3 : browkin2Digit 3 (-b⁻¹ - 1) = -1 / p := by
    rw [browkin2Digit, if_neg (by decide), t3, if_pos (by rw [hx3, norm_neg, h1b])]
  have c4 : bcf2CQ b⁻¹ 4 = -(1 + b)⁻¹ := by
    rw [bcf2CQ, c3, d3, hx3, inv_neg]
  -- step 4
  have d4 : browkin2Digit 4 (-(1 + b)⁻¹) = -1 := by
    rw [browkin2Digit, if_pos (by decide)]
    have h : ‖-(1 + b)⁻¹ - ((-1 : ℤ) : ℚ)‖ < 1 := by
      have : -(1 + b)⁻¹ - (((-1 : ℤ) : ℚ) : ℚ_[p]) = -((1 + b)⁻¹ - (((1 : ℤ) : ℚ) : ℚ_[p])) := by
        push_cast; ring
      rw [this, norm_neg]; exact hw
    exact_mod_cast browkinS_eq (pm_one_mem_J hp2 (-1) (Or.inr rfl)) h
  have c5 : bcf2CQ b⁻¹ 5 = b⁻¹ + 1 := by
    rw [bcf2CQ, c4, d4]
    push_cast
    apply inv_eq_of_mul_eq_one_right
    field_simp
    ring
  -- step 5
  have hx5 : b⁻¹ + 1 - (((1 / p : ℚ)) : ℚ_[p]) = 1 + b := by
    rw [hpinv]; linear_combination hsub
  have t5 : browkinT (b⁻¹ + 1) = 1 / p :=
    browkinT_eq (inv_p_mem_K hp2) (by rw [hx5, h1b])
  have d5 : browkin2Digit 5 (b⁻¹ + 1) = 1 / p := by
    rw [browkin2Digit, if_neg (by decide), t5, if_pos (by rw [hx5, h1b])]
  have c6 : bcf2CQ b⁻¹ 6 = (1 + b)⁻¹ := by
    rw [bcf2CQ, c5, d5, hx5]
  refine ⟨c1, c2, c3, c4, c5, c6, d0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bcf2PQ, c1, d1]
  · rw [bcf2PQ, c2, d2]
  · rw [bcf2PQ, c3, d3]
  · rw [bcf2PQ, c4, d4]
  · rw [bcf2PQ, c5, d5]

/-- Browkin II: the complete quotients are periodic with period 4 from index 2. -/
lemma bcf2CQ_periodic (n : ℕ) (hn : 2 ≤ n) : bcf2CQ b⁻¹ (n + 4) = bcf2CQ b⁻¹ n := by
  induction n, hn using Nat.le_induction with
  | base =>
    obtain ⟨-, c2, -, -, -, c6, -⟩ := bcf2_first_steps hp2 hb hb1
    rw [c6, c2]
  | succ n _ ih =>
    have e1 : bcf2CQ b⁻¹ (n + 1 + 4) =
        (bcf2CQ b⁻¹ (n + 4) - (browkin2Digit (n + 4) (bcf2CQ b⁻¹ (n + 4)) : ℚ_[p]))⁻¹ := rfl
    have e2 : bcf2CQ b⁻¹ (n + 1) =
        (bcf2CQ b⁻¹ n - (browkin2Digit n (bcf2CQ b⁻¹ n) : ℚ_[p]))⁻¹ := rfl
    rw [e1, e2, ih, browkin2Digit_add_four]

lemma bcf2PQ_periodic (n : ℕ) (hn : 2 ≤ n) : bcf2PQ b⁻¹ (n + 4) = bcf2PQ b⁻¹ n := by
  rw [bcf2PQ, bcf2PQ, bcf2CQ_periodic hp2 hb hb1 n hn, browkin2Digit_add_four]

lemma bcf2CQ_ne_zero (n : ℕ) : bcf2CQ b⁻¹ n ≠ 0 := by
  have hb0 := b_ne_zero hb
  have h1b := one_add_b hb1
  have hbm1 : b⁻¹ + 1 ≠ 0 := by
    intro h
    have : b = -1 := by rw [← inv_inj, inv_neg, inv_one]; linear_combination h
    rw [this, norm_neg, norm_one] at hb1
    exact lt_irrefl _ hb1
  have h1b0 : 1 + b ≠ 0 := by intro h; rw [h, norm_zero] at h1b; exact zero_ne_one h1b
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := bcf2_first_steps hp2 hb hb1
  obtain ⟨m, hm, he⟩ := exists_lt_of_periodic (by norm_num) (bcf2CQ_periodic hp2 hb hb1) n
  rw [he]
  interval_cases m
  · exact inv_ne_zero hb0
  · rw [c1]; exact inv_ne_zero hb0
  · rw [c2]; exact inv_ne_zero h1b0
  · rw [c3, show -b⁻¹ - 1 = -(b⁻¹ + 1) by ring]; exact neg_ne_zero.2 hbm1
  · rw [c4]; exact neg_ne_zero.2 (inv_ne_zero h1b0)
  · rw [c5]; exact hbm1

end Example

/-- A step `α_{n+1} = (α_n - a_n)⁻¹` with `α_{n+1} ≠ 0` never divides by zero. -/
lemma sub_ne_zero_of_inv_ne_zero {x y : ℚ_[p]} (h : (x - y)⁻¹ ≠ 0) : x ≠ y := by
  rintro rfl; simp at h

/-- **Main construction.** For every odd prime `p` there is an irrational algebraic `α ∈ ℚ_[p]`
(a root of `p X² - X - p`) whose Browkin expansions (first and second algorithm) never terminate,
are eventually periodic, and have finitely many, hence `p`-adically bounded, partial quotients. -/
theorem browkin_counterexample (hp2 : p ≠ 2) :
    ∃ α : ℚ_[p], (p : ℚ_[p]) * α ^ 2 - α - p = 0 ∧ IsAlgebraic ℚ α ∧
      (∀ r : ℚ, (r : ℚ_[p]) ≠ α) ∧
      -- Browkin I
      (∀ n, bcfCQ α n ≠ (bcfPQ α n : ℚ_[p])) ∧ (∀ n, bcfCQ α n = α) ∧
      (∀ n, bcfPQ α n = 1 / p) ∧ EventuallyPeriodic (bcfPQ α) ∧
      (Set.range (bcfPQ α)).Finite ∧ PadicBounded p (bcfPQ α) ∧
      -- Browkin II
      (∀ n, bcf2CQ α n ≠ (bcf2PQ α n : ℚ_[p])) ∧
      (∀ n, 2 ≤ n → bcf2PQ α (n + 4) = bcf2PQ α n) ∧ EventuallyPeriodic (bcf2PQ α) ∧
      (Set.range (bcf2PQ α)).Finite ∧ PadicBounded p (bcf2PQ α) := by
  obtain ⟨b, hb, hb1⟩ := exists_beta (p := p)
  have hα := alpha_eq hb
  have hper1 : EventuallyPeriodic (bcfPQ b⁻¹) :=
    ⟨0, 1, one_pos, fun n _ => by rw [bcfPQ_alpha hp2 hb hb1, bcfPQ_alpha hp2 hb hb1]⟩
  have hper2 : EventuallyPeriodic (bcf2PQ b⁻¹) :=
    ⟨2, 4, by norm_num, bcf2PQ_periodic hp2 hb hb1⟩
  refine ⟨b⁻¹, hα, alpha_algebraic hα, alpha_irrational hα, fun n => ?_,
    bcfCQ_alpha hp2 hb hb1, bcfPQ_alpha hp2 hb hb1, hper1, hper1.finite_range,
    padicBounded_of_finite hper1.finite_range, fun n => ?_, bcf2PQ_periodic hp2 hb hb1, hper2,
    hper2.finite_range, padicBounded_of_finite hper2.finite_range⟩
  · apply sub_ne_zero_of_inv_ne_zero
    rw [bcfPQ, bcfCQ_alpha hp2 hb hb1, s_alpha hp2 hb hb1, alpha_sub hb]
    exact inv_ne_zero (b_ne_zero hb)
  · exact sub_ne_zero_of_inv_ne_zero (bcf2CQ_ne_zero hp2 hb hb1 (n + 1))

/-- Clause 1 of the conjecture, for Browkin's first algorithm, restricted to irrational
algebraic `α` (for rational `α` the expansion is finite). -/
def ClauseNonPeriodicI (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ α : ℚ_[p], IsAlgebraic ℚ α → (∀ r : ℚ, (r : ℚ_[p]) ≠ α) → ¬ EventuallyPeriodic (bcfPQ α)

/-- Clause 2 (partial quotients unbounded in `|·|_p`), Browkin's first algorithm. -/
def ClauseUnboundedI (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ α : ℚ_[p], IsAlgebraic ℚ α → (∀ r : ℚ, (r : ℚ_[p]) ≠ α) → ¬ PadicBounded p (bcfPQ α)

/-- Clause 1 for Browkin's second algorithm. -/
def ClauseNonPeriodicII (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ α : ℚ_[p], IsAlgebraic ℚ α → (∀ r : ℚ, (r : ℚ_[p]) ≠ α) → ¬ EventuallyPeriodic (bcf2PQ α)

/-- Clause 2 for Browkin's second algorithm. -/
def ClauseUnboundedII (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ α : ℚ_[p], IsAlgebraic ℚ α → (∀ r : ℚ, (r : ℚ_[p]) ≠ α) → ¬ PadicBounded p (bcf2PQ α)

/-- **Conjecture 00000000702 is false** for every odd prime `p`: each of the two clauses fails,
separately, for both of Browkin's algorithms. -/
theorem conjecture702_false (hp2 : p ≠ 2) :
    ¬ ClauseNonPeriodicI p ∧ ¬ ClauseUnboundedI p ∧
      ¬ ClauseNonPeriodicII p ∧ ¬ ClauseUnboundedII p := by
  obtain ⟨α, -, halg, hirr, -, -, -, h1, -, h2, -, -, h3, -, h4⟩ := browkin_counterexample hp2
  exact ⟨fun h => h α halg hirr h1, fun h => h α halg hirr h2,
    fun h => h α halg hirr h3, fun h => h α halg hirr h4⟩

end C702
