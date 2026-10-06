import Mathlib

/-!
# Conjecture 00000000165 (disproof)

Statement: for `d ∣ p - 1`, let `H` be the subgroup of `d`-th powers in `F_p^*`. Then the minimal `k`
for which the `k`-fold sumset `H + ⋯ + H` covers `F_p` is `(1 + o(1)) · log p / (log p - log d)`,
as `d → ∞` with `d < p^(1-ε)`.

We refute it. For every `ε ∈ (0,1)` and every `N` there is a prime `p` and an (even) `d ≥ N` with
`d ∣ p - 1`, `d < p^(1-ε)`, `(p-1)/d` odd and `d^d < p` (Dirichlet). Then `-1` is not a `d`-th
power, so `0 ∉ H` and `0 ∉ H + H`, hence the minimal `k` is at least `3`; a cover exists (by
Cauchy-Davenport), while `log p / (log p - log d) ∈ (1, 4/3]`.
-/

open scoped Pointwise

namespace C165

/-- The subgroup of `d`-th powers of `F_p^* = (ZMod p)ˣ`: the range of `x ↦ x ^ d`. -/
def powSubgroup (p d : ℕ) : Subgroup (ZMod p)ˣ := (powMonoidHom d).range

/-- The subgroup of `d`-th powers, viewed as a subset of `F_p = ZMod p`. -/
def H (p d : ℕ) : Set (ZMod p) := (fun u : (ZMod p)ˣ => (u : ZMod p)) '' (powSubgroup p d : Set (ZMod p)ˣ)

/-- The `k`-fold sumset of `S` is Mathlib's pointwise `k • S` (`(k+1) • S = k • S + S`);
it is exactly the set of sums `s₁ + ⋯ + s_k` with all `sᵢ ∈ S`. -/
theorem mem_kfold_sumset {p : ℕ} (S : Set (ZMod p)) (k : ℕ) (x : ZMod p) :
    x ∈ k • S ↔ ∃ f : Fin k → S, (List.ofFn fun i => (f i : ZMod p)).sum = x :=
  Set.mem_nsmul

/-- The minimal `k ≥ 1` whose `k`-fold sumset of `H` is all of `F_p` (`sInf ∅ = 0`). -/
noncomputable def coverNumber (p d : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ k • H p d = Set.univ}

/-- Variant ("at most `k` summands", i.e. zero summands allowed): sumsets of `H ∪ {0}`. -/
noncomputable def coverNumberAtMost (p d : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ k • (H p d ∪ {0}) = Set.univ}

/-- The conjectured main term `log p / (log p - log d)`. -/
noncomputable def L (p d : ℕ) : ℝ := Real.log p / (Real.log p - Real.log d)

/-- `K(p,d) = (1 + o(1)) F(p,d)` as `d → ∞` over primes `p`, `d ∣ p - 1`, `d < p^(1-ε)`,
uniformly in `p`: for every `η > 0` there is `D` with `|K/F - 1| < η` once `d ≥ D`. -/
def Asymp (ε : ℝ) (K : ℕ → ℕ → ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ D : ℕ, ∀ p d : ℕ, p.Prime → d ∣ p - 1 → D ≤ d →
    (d : ℝ) < (p : ℝ) ^ (1 - ε) → |(K p d : ℝ) / F p d - 1| < η

/-- The conjecture, literally: for every fixed `ε ∈ (0,1)`, `coverNumber = (1+o(1)) · L`. -/
def Conjecture165 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 → Asymp ε coverNumber L

theorem mem_H {p d : ℕ} {x : ZMod p} :
    x ∈ H p d ↔ ∃ u : (ZMod p)ˣ, ((u ^ d : (ZMod p)ˣ) : ZMod p) = x := by
  simp only [H, powSubgroup, Set.mem_image, SetLike.mem_coe, MonoidHom.mem_range,
    powMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩; exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩; exact ⟨_, ⟨u, rfl⟩, rfl⟩

/-! ### The family (Dirichlet) -/

theorem exists_pair (N : ℕ) : ∃ p d q : ℕ, p.Prime ∧ N ≤ d ∧ 4 ≤ d ∧ d ^ d < p ∧
    p - 1 = d * (2 * q + 1) := by
  set d := 2 * (N + 2) with hd
  have hcop : (d + 1).Coprime (2 * d) := by
    have h1 : (d + 1).Coprime 2 := by
      rw [Nat.coprime_two_right]; exact ⟨N + 2, by omega⟩
    have h2 : (d + 1).Coprime d := by simp
    exact Nat.Coprime.mul_right h1 h2
  have hu : IsUnit (((d + 1 : ℕ)) : ZMod (2 * d)) := (ZMod.isUnit_iff_coprime _ _).2 hcop
  obtain ⟨p, hpgt, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu (d ^ d)
  have hmod : p % (2 * d) = d + 1 := by
    rw [ZMod.natCast_eq_natCast_iff'] at hpmod
    rw [hpmod]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨p, d, p / (2 * d), hp, by omega, by omega, hpgt, ?_⟩
  have h := Nat.div_add_mod p (2 * d)
  rw [hmod] at h
  have : d * (2 * (p / (2 * d)) + 1) = 2 * d * (p / (2 * d)) + d := by ring
  rw [this]
  generalize 2 * d * (p / (2 * d)) = t at h ⊢
  omega

/-! ### Algebra in `F_p` -/

section Field

variable {p d q : ℕ} [hpf : Fact p.Prime]

theorem neg_one_not_pow (hp2 : 2 < p) (hq : p - 1 = d * (2 * q + 1)) (u : (ZMod p)ˣ) :
    ((u ^ d : (ZMod p)ˣ) : ZMod p) ≠ -1 := by
  intro h
  have h1 : u ^ (p - 1) = 1 := ZMod.units_pow_card_sub_one_eq_one p u
  rw [hq, pow_mul] at h1
  have h2 := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) h1
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at h2
  rw [← Units.val_pow_eq_pow_val, h, Odd.neg_one_pow ⟨q, rfl⟩] at h2
  have : Fact (2 < p) := ⟨hp2⟩
  exact ZMod.neg_one_ne_one h2

theorem zero_not_mem_H : (0 : ZMod p) ∉ H p d := by
  rw [mem_H]; rintro ⟨u, hu⟩; exact (u ^ d).ne_zero hu

theorem zero_not_mem_HH (hp2 : 2 < p) (hq : p - 1 = d * (2 * q + 1)) :
    (0 : ZMod p) ∉ H p d + H p d := by
  rintro ⟨a, ha, b, hb, hab⟩
  obtain ⟨u, rfl⟩ := mem_H.1 ha
  obtain ⟨v, rfl⟩ := mem_H.1 hb
  apply neg_one_not_pow hp2 hq (v * u⁻¹)
  have e : (v * u⁻¹) ^ d * u ^ d = v ^ d := by rw [mul_pow, inv_pow, inv_mul_cancel_right]
  have e2 := congrArg (fun w : (ZMod p)ˣ => (w : ZMod p)) e
  simp only [Units.val_mul] at e2
  have hv : ((v ^ d : (ZMod p)ˣ) : ZMod p) = -((u ^ d : (ZMod p)ˣ) : ZMod p) :=
    eq_neg_of_add_eq_zero_right hab
  rw [hv, ← neg_one_mul] at e2
  exact mul_right_cancel₀ (u ^ d).ne_zero e2

theorem neg_one_not_mem_H0 (hp2 : 2 < p) (hq : p - 1 = d * (2 * q + 1)) :
    (-1 : ZMod p) ∉ H p d ∪ {0} := by
  rintro (h | h)
  · obtain ⟨u, hu⟩ := mem_H.1 h; exact neg_one_not_pow hp2 hq u hu
  · simp at h

/-- Cauchy-Davenport: a finset of `ZMod p` with at least two elements has `p • S = univ`. -/
theorem nsmul_eq_univ (S : Finset (ZMod p)) (hS : 2 ≤ S.card) : p • S = Finset.univ := by
  have hp := hpf.out
  have key : ∀ k : ℕ, min p (k + 1) ≤ ((k + 1) • S).card := by
    intro k
    induction k with
    | zero => rw [zero_add, one_nsmul]; have := hp.two_le; omega
    | succ k ih =>
      have hne : ((k + 1) • S).Nonempty := by
        rw [← Finset.card_pos]; have := hp.two_le; omega
      have hSne : S.Nonempty := by rw [← Finset.card_pos]; omega
      have cd := ZMod.cauchy_davenport hp hne hSne
      rw [succ_nsmul]
      omega
  have h1 := key (p - 1)
  rw [Nat.sub_add_cancel hp.one_le, min_self] at h1
  apply Finset.eq_univ_of_card
  have := Finset.card_le_univ (p • S)
  rw [ZMod.card] at this ⊢
  omega

/-- The finset of `d`-th powers. -/
noncomputable def Hfin (p d : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.image fun u : (ZMod p)ˣ => ((u ^ d : (ZMod p)ˣ) : ZMod p)

theorem coe_Hfin : (Hfin p d : Set (ZMod p)) = H p d := by
  ext x; simp [Hfin, mem_H]

/-- Non-degeneracy: `1` and `2 ^ d` are distinct elements of `H`. -/
theorem one_two_pow_mem_H (hd : 1 ≤ d) (h2d : 2 ^ d < p) :
    (1 : ZMod p) ∈ H p d ∧ (2 : ZMod p) ^ d ∈ H p d ∧ (2 : ZMod p) ^ d ≠ 1 := by
  have hp2 : 2 < p := lt_of_le_of_lt (by simpa using Nat.pow_le_pow_right two_pos hd) h2d
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd two_pos this) (by omega)
  refine ⟨mem_H.2 ⟨1, by simp⟩, mem_H.2 ⟨Units.mk0 2 h20, by simp⟩, ?_⟩
  intro h
  have : ((2 ^ d : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by exact_mod_cast h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h2d, Nat.mod_eq_of_lt (by omega)] at this
  have := Nat.one_lt_two_pow (n := d) (by omega)
  omega

theorem cover_exists (hd : 1 ≤ d) (h2d : 2 ^ d < p) : p • H p d = Set.univ := by
  obtain ⟨h1, h2, hne⟩ := one_two_pow_mem_H hd h2d
  have hcard : 2 ≤ (Hfin p d).card := by
    rw [← coe_Hfin] at h1 h2
    exact Finset.one_lt_card.2 ⟨_, Finset.mem_coe.1 h2, _, Finset.mem_coe.1 h1, hne⟩
  rw [← coe_Hfin, ← Finset.coe_nsmul, nsmul_eq_univ _ hcard, Finset.coe_univ]

/-- On the family, the literal cover number is at least `3`. -/
theorem three_le_coverNumber (hd : 1 ≤ d) (h2d : 2 ^ d < p) (hq : p - 1 = d * (2 * q + 1)) :
    3 ≤ coverNumber p d := by
  have hp2 : 2 < p := lt_of_le_of_lt (by simpa using Nat.pow_le_pow_right two_pos hd) h2d
  have hne : ({k : ℕ | 1 ≤ k ∧ k • H p d = Set.univ}).Nonempty :=
    ⟨p, by have := hpf.out.one_le; omega, cover_exists hd h2d⟩
  have hmem := Nat.sInf_mem hne
  by_contra hlt
  obtain ⟨h1, hU⟩ := hmem
  rw [← coverNumber] at h1 hU
  have h0 : (0 : ZMod p) ∈ coverNumber p d • H p d := hU ▸ Set.mem_univ _
  interval_cases hk : coverNumber p d
  · rw [one_nsmul] at h0; exact zero_not_mem_H h0
  · rw [two_nsmul] at h0; exact zero_not_mem_HH hp2 hq h0

/-- On the family, the "at most `k` summands" cover number is at least `2`. -/
theorem two_le_coverNumberAtMost (hd : 1 ≤ d) (h2d : 2 ^ d < p)
    (hq : p - 1 = d * (2 * q + 1)) : 2 ≤ coverNumberAtMost p d := by
  have hp2 : 2 < p := lt_of_le_of_lt (by simpa using Nat.pow_le_pow_right two_pos hd) h2d
  have hcov : p • (H p d ∪ {0}) = Set.univ :=
    Set.eq_univ_of_univ_subset ((cover_exists hd h2d).symm.subset.trans
      (Set.nsmul_subset_nsmul_left Set.subset_union_left))
  have hne : ({k : ℕ | 1 ≤ k ∧ k • (H p d ∪ {0}) = Set.univ}).Nonempty :=
    ⟨p, by have := hpf.out.one_le; omega, hcov⟩
  obtain ⟨h1, hU⟩ := Nat.sInf_mem hne
  rw [← coverNumberAtMost] at h1 hU
  by_contra hlt
  have hk : coverNumberAtMost p d = 1 := by omega
  rw [hk, one_nsmul] at hU
  exact neg_one_not_mem_H0 hp2 hq (hU ▸ Set.mem_univ _)

end Field

/-! ### Real estimates -/

theorem L_bounds {p d : ℕ} (hd : 2 ≤ d) (h4 : d ^ 4 < p) :
    0 < Real.log p - Real.log d ∧ 1 < L p d ∧ L p d ≤ 4 / 3 := by
  have hd0 : (0 : ℝ) < d := by positivity
  have hld : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have h4' : 4 * Real.log d < Real.log p := by
    have h := Real.log_lt_log (by positivity) (show (d : ℝ) ^ 4 < p by exact_mod_cast h4)
    rw [Real.log_pow] at h; push_cast at h; exact h
  have hpos : 0 < Real.log p - Real.log d := by linarith
  refine ⟨hpos, ?_, ?_⟩
  · rw [L, one_lt_div hpos]; linarith
  · rw [L, div_le_iff₀ hpos]; linarith

theorem window {p d : ℕ} {ε : ℝ} (hε : ε < 1) (hd : 2 ≤ d) (hdε : 1 ≤ (1 - ε) * d)
    (hdd : d ^ d < p) : (d : ℝ) < (p : ℝ) ^ (1 - ε) := by
  have hd0 : (0 : ℝ) < d := by positivity
  have hp0 : (0 : ℝ) < p := by have : 0 < p := by omega
                               exact_mod_cast this
  have hld : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have h1 : (d : ℝ) * Real.log d < Real.log p := by
    rw [← Real.log_pow]
    exact Real.log_lt_log (by positivity) (by exact_mod_cast hdd)
  rw [Real.lt_rpow_iff_log_lt hd0 hp0]
  nlinarith [mul_lt_mul_of_pos_left h1 (by linarith : (0 : ℝ) < 1 - ε)]

/-! ### Main results -/

/-- The explicit non-degenerate family: for each `ε ∈ (0,1)` and `N`, an admissible pair with
`d ≥ N`, where the cover exists, the literal cover number is `≥ 3`, the at-most-`k` cover
number is `≥ 2`, `1 < L ≤ 4/3`, and `2^d ∈ H` with `2^d ≠ 1` (so `H ≠ {1}`). -/
theorem family (ε : ℝ) (_hε0 : 0 < ε) (hε1 : ε < 1) (N : ℕ) :
    ∃ p d : ℕ, p.Prime ∧ d ∣ p - 1 ∧ N ≤ d ∧ (d : ℝ) < (p : ℝ) ^ (1 - ε) ∧
      p • H p d = Set.univ ∧ 3 ≤ coverNumber p d ∧ 2 ≤ coverNumberAtMost p d ∧
      1 < L p d ∧ L p d ≤ 4 / 3 ∧ (2 : ZMod p) ^ d ∈ H p d ∧ (2 : ZMod p) ^ d ≠ 1 := by
  obtain ⟨p, d, q, hp, hNd, hd4, hdd, hq⟩ := exists_pair (max N ⌈1 / (1 - ε)⌉₊)
  have : Fact p.Prime := ⟨hp⟩
  have hd1 : 1 ≤ d := by omega
  have h2d : 2 ^ d < p := lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) d) hdd
  have h4 : d ^ 4 < p := lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hd4) hdd
  have hdε : 1 ≤ (1 - ε) * d := by
    have hc : (⌈1 / (1 - ε)⌉₊ : ℝ) ≤ d := by exact_mod_cast le_of_max_le_right hNd
    have := Nat.le_ceil (1 / (1 - ε))
    rw [div_le_iff₀ (by linarith)] at this
    nlinarith
  obtain ⟨-, hL1, hL2⟩ := L_bounds (by omega) h4
  obtain ⟨-, h2m, h2ne⟩ := one_two_pow_mem_H hd1 h2d
  exact ⟨p, d, hp, ⟨2 * q + 1, hq⟩, le_of_max_le_left hNd, window hε1 (by omega) hdε hdd,
    cover_exists hd1 h2d, three_le_coverNumber hd1 h2d hq, two_le_coverNumberAtMost hd1 h2d hq,
    hL1, hL2, h2m, h2ne⟩

theorem floor_round_L {p d : ℕ} (hL1 : 1 < L p d) (hL2 : L p d ≤ 4 / 3) :
    ⌊L p d⌋ = 1 ∧ round (L p d) = 1 := by
  rw [round_eq, Int.floor_eq_iff, Int.floor_eq_iff]; norm_num
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- For every `ε ∈ (0,1)`: the asymptotic fails for the literal cover number against `L`
(ratio `≥ 9/4`), `⌈L⌉` (ratio `≥ 3/2`), `⌊L⌋` and `round L` (ratio `≥ 3`), and for the
at-most-`k` cover number against `L` (ratio `≥ 3/2`), `⌊L⌋` and `round L` (ratio `≥ 2`). -/
theorem main (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ¬ Asymp ε coverNumber L ∧ ¬ Asymp ε coverNumber (fun p d => (⌈L p d⌉ : ℝ)) ∧
      ¬ Asymp ε coverNumber (fun p d => (⌊L p d⌋ : ℝ)) ∧
      ¬ Asymp ε coverNumber (fun p d => (round (L p d) : ℝ)) ∧
      ¬ Asymp ε coverNumberAtMost L ∧
      ¬ Asymp ε coverNumberAtMost (fun p d => (⌊L p d⌋ : ℝ)) ∧
      ¬ Asymp ε coverNumberAtMost (fun p d => (round (L p d) : ℝ)) := by
  have key : ∀ (K : ℕ → ℕ → ℕ) (F : ℕ → ℕ → ℝ), (∀ p d : ℕ, 1 < L p d → L p d ≤ 4 / 3 →
      3 ≤ coverNumber p d → 2 ≤ coverNumberAtMost p d → 1 / 2 ≤ (K p d : ℝ) / F p d - 1) →
      ¬ Asymp ε K F := by
    intro K F hKF hA
    obtain ⟨D, hD⟩ := hA (1 / 2) (by norm_num)
    obtain ⟨p, d, hp, hdvd, hDd, hw, -, h3, h2, hL1, hL2, -⟩ := family ε hε0 hε1 D
    have := hD p d hp hdvd hDd hw
    have := hKF p d hL1 hL2 h3 h2
    rw [abs_lt] at *; linarith
  refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_⟩
  · intro p d hL1 hL2 h3 _
    have h3' : (3 : ℝ) ≤ coverNumber p d := by exact_mod_cast h3
    rw [le_sub_iff_add_le, le_div_iff₀ (by linarith)]; nlinarith
  · intro p d hL1 hL2 h3 _
    have hc : ⌈L p d⌉ = 2 := by rw [Int.ceil_eq_iff]; norm_num; constructor <;> linarith
    have h3' : (3 : ℝ) ≤ coverNumber p d := by exact_mod_cast h3
    simp only [hc]; push_cast; linarith
  · intro p d hL1 hL2 h3 _
    have h3' : (3 : ℝ) ≤ coverNumber p d := by exact_mod_cast h3
    simp only [(floor_round_L hL1 hL2).1]; push_cast; linarith
  · intro p d hL1 hL2 h3 _
    have h3' : (3 : ℝ) ≤ coverNumber p d := by exact_mod_cast h3
    simp only [(floor_round_L hL1 hL2).2]; push_cast; linarith
  · intro p d hL1 hL2 _ h2
    have h2' : (2 : ℝ) ≤ coverNumberAtMost p d := by exact_mod_cast h2
    rw [le_sub_iff_add_le, le_div_iff₀ (by linarith)]; nlinarith
  · intro p d hL1 hL2 _ h2
    have h2' : (2 : ℝ) ≤ coverNumberAtMost p d := by exact_mod_cast h2
    simp only [(floor_round_L hL1 hL2).1]; push_cast; linarith
  · intro p d hL1 hL2 _ h2
    have h2' : (2 : ℝ) ≤ coverNumberAtMost p d := by exact_mod_cast h2
    simp only [(floor_round_L hL1 hL2).2]; push_cast; linarith

/-- The conjecture is false. -/
theorem not_conjecture165 : ¬ Conjecture165 := fun h =>
  (main (1 / 2) (by norm_num) (by norm_num)).1 (h (1 / 2) (by norm_num) (by norm_num))

end C165
