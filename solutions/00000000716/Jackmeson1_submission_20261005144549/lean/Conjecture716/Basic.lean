import Mathlib

/-!
# Conjecture 00000000716: the sign in the p-adic reflection formula

Morita's `p`-adic gamma function `Γ_p : ℤ_[p] → ℤ_[p]` is the unique continuous function with
`Γ_p(n) = (-1)^n ∏_{0 < j < n, p ∤ j} j` for positive integers `n`.  We construct it (for odd
primes `p`) as a limit of these products along the approximations `PadicInt.appr`, prove that it
is continuous, interpolates the product formula and is the unique such continuous function.

The conjecture says that the sign `Γ_p(a) Γ_p(1 - a) = ±1` is an explicit function of `p mod 4`.
We refute two readings:
* (A) the product depends only on `p` (a fortiori only on `p mod 4`), not on `a`:
  for every odd prime `p`, `Γ_p(1) Γ_p(0) = -1` while `Γ_p(2) Γ_p(-1) ≡ 1 (mod p)`;
* (B) for each fixed integer `a` the sign is a function of `p mod 4`: for `a = 4`,
  the product is `≡ -1 (mod 3)` for `p = 3` and `≡ 1 (mod 7)` for `p = 7`, although `3 ≡ 7 (mod 4)`.
-/

open Finset Filter Topology

namespace C716

/-- Morita's finite product `(-1)^n ∏_{0 ≤ j < n, p ∤ j} j` (the factor `j = 0` is excluded
automatically since `p ∣ 0`). -/
def mor (p n : ℕ) : ℤ := (-1) ^ n * ∏ j ∈ (range n).filter (fun j => ¬ p ∣ j), (j : ℤ)

/-- The factor `j` if `p ∤ j`, and `1` otherwise, as an element of `ZMod (p^k)`. -/
def fac (p k j : ℕ) : ZMod (p ^ k) := if ¬ p ∣ j then (j : ZMod (p ^ k)) else 1

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
lemma mor_cast (k n : ℕ) :
    ((mor p n : ℤ) : ZMod (p ^ k)) = (-1) ^ n * ∏ j ∈ range n, fac p k j := by
  simp only [mor, fac, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_prod,
    prod_filter]
  congr 1; refine prod_congr rfl fun j _ => ?_; split_ifs <;> simp

/-- In `ZMod (p^k)` with `p` odd, the only square roots of `1` are `±1`. -/
lemma sq_eq_one_zmod (hp2 : p ≠ 2) (k : ℕ) (x : ZMod (p ^ k)) (hx : x * x = 1) :
    x = 1 ∨ x = -1 := by
  obtain ⟨y, rfl⟩ : ∃ y : ℤ, (y : ZMod (p ^ k)) = x := ⟨x.cast, ZMod.intCast_zmod_cast x⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hd : ((p ^ k : ℕ) : ℤ) ∣ (y - 1) * (y + 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; linear_combination hx
  push_cast at hd
  by_cases h1 : (p : ℤ) ∣ y - 1
  · have h2 : ¬ (p : ℤ) ∣ y + 1 := by
      intro h2
      have : (p : ℤ) ∣ 2 := by
        have := dvd_sub h2 h1; ring_nf at this; exact this
      have := Int.le_of_dvd (by norm_num) this
      have h3 := hp.out.two_le
      have : (p : ℤ) ∣ 2 := ‹_›
      have h4 : p ∣ 2 := by exact_mod_cast this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h4)
    have hc : IsCoprime ((p : ℤ) ^ k) (y + 1) :=
      ((hpZ.irreducible.coprime_iff_not_dvd).2 h2).pow_left
    have := hc.dvd_of_dvd_mul_right hd
    left
    have : ((y - 1 : ℤ) : ZMod (p ^ k)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact this
    push_cast at this; linear_combination this
  · have hc : IsCoprime ((p : ℤ) ^ k) (y - 1) :=
      ((hpZ.irreducible.coprime_iff_not_dvd).2 h1).pow_left
    have := hc.dvd_of_dvd_mul_left hd
    right
    have : ((y + 1 : ℤ) : ZMod (p ^ k)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact this
    push_cast at this; linear_combination this

/-- Generalized Wilson theorem for odd prime powers: the product of all units is `-1`. -/
lemma prod_units_eq_neg_one (hp2 : p ≠ 2) (k : ℕ) :
    ∏ u : (ZMod (p ^ k))ˣ, u = -1 := by
  classical
  have : (∏ x ∈ (univ : Finset (ZMod (p ^ k))ˣ).erase (-1), x) = 1 := by
    refine prod_involution (fun x _ => x⁻¹) (by simp) (fun a ha hne heq => ?_)
      (fun a ha => by simp [@inv_eq_iff_eq_inv _ _ a] at ha ⊢; exact ha) (by simp)
    have h1 : a * a = 1 := by
      have := mul_inv_cancel a; rw [heq] at this; exact this
    have h2 : (a : ZMod (p ^ k)) * a = 1 := by rw [← Units.val_mul, h1, Units.val_one]
    rcases sq_eq_one_zmod hp2 k _ h2 with h | h
    · exact hne (Units.ext h)
    · exact (mem_erase.1 ha).1 (Units.ext (by simpa using h))
  rw [← insert_erase (mem_univ (-1 : (ZMod (p ^ k))ˣ)), prod_insert (notMem_erase _ _), this,
    mul_one]

lemma not_dvd_iff_coprime {k j : ℕ} (hk : 1 ≤ k) : ¬ p ∣ j ↔ Nat.Coprime j (p ^ k) := by
  rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]

/-- The product of the factors over one full period `0 ≤ j < p^k` is `-1`. -/
lemma prod_range_fac (hp2 : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) :
    ∏ j ∈ range (p ^ k), fac p k j = -1 := by
  classical
  have hpos : 0 < p ^ k := pow_pos hp.out.pos k
  have : NeZero (p ^ k) := ⟨hpos.ne'⟩
  simp only [fac]
  rw [← prod_filter]
  have key : ∏ j ∈ (range (p ^ k)).filter (fun j => ¬ p ∣ j), (j : ZMod (p ^ k)) =
      ∏ u : (ZMod (p ^ k))ˣ, (u : ZMod (p ^ k)) := by
    refine prod_bij' (fun j hj => ZMod.unitOfCoprime j ((not_dvd_iff_coprime hk).1
        (mem_filter.1 hj).2)) (fun u _ => (u : ZMod (p ^ k)).val) (by simp) ?_ ?_ ?_ ?_
    · intro u _
      simp only [mem_filter, mem_range]
      exact ⟨ZMod.val_lt _, (not_dvd_iff_coprime hk).2 (ZMod.val_coe_unit_coprime u)⟩
    · intro j hj
      simp only [ZMod.coe_unitOfCoprime]
      exact ZMod.val_cast_of_lt (mem_range.1 (mem_filter.1 hj).1)
    · intro u _
      ext; simp [ZMod.coe_unitOfCoprime]
    · intro j hj; simp [ZMod.coe_unitOfCoprime]
  rw [key, ← Units.coe_prod, prod_units_eq_neg_one hp2 k, Units.val_neg, Units.val_one]

omit hp in
lemma fac_add_period {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : fac p k (n + p ^ k) = fac p k n := by
  have h1 : (p ∣ n + p ^ k ↔ p ∣ n) := (Nat.dvd_add_left (dvd_pow_self p (by omega))).trans Iff.rfl
  simp only [fac, h1, Nat.cast_add, Nat.cast_pow]
  rw [show ((p : ZMod (p ^ k)) ^ k) = ((p ^ k : ℕ) : ZMod (p ^ k)) by push_cast; rfl,
    ZMod.natCast_self, add_zero]

lemma isUnit_fac {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : IsUnit (fac p k n) := by
  by_cases h : p ∣ n
  · simp [fac, h]
  · simp only [fac, h, not_false_eq_true, if_true]
    exact (ZMod.isUnit_iff_coprime n (p ^ k)).2 ((not_dvd_iff_coprime hk).1 h)

/-- Generalized Wilson theorem over any window of length `p^k`. -/
lemma prod_Ico_fac (hp2 : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ∏ j ∈ Ico n (n + p ^ k), fac p k j = -1 := by
  induction n with
  | zero => rw [zero_add, ← range_eq_Ico]; exact prod_range_fac hp2 hk
  | succ n ih =>
    have e1 := prod_Ico_succ_top (show n ≤ n + p ^ k by omega) (fac p k)
    have e2 := prod_eq_prod_Ico_succ_bot (show n < n + p ^ k + 1 by omega) (fac p k)
    rw [e1, fac_add_period hk, ih] at e2
    rw [show n + 1 + p ^ k = n + p ^ k + 1 by omega]
    have hu := isUnit_fac (p := p) hk n
    apply hu.mul_left_cancel
    rw [← e2, mul_comm]

lemma mor_add_period (hp2 : p ≠ 2) (k n : ℕ) :
    ((mor p (n + p ^ k) : ℤ) : ZMod (p ^ k)) = mor p n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  rw [mor_cast, mor_cast, ← prod_range_mul_prod_Ico _ (show n ≤ n + p ^ k by omega),
    prod_Ico_fac hp2 hk, pow_add]
  have hodd : Odd (p ^ k) := (hp.out.odd_of_ne_two hp2).pow
  rw [hodd.neg_one_pow]; ring

/-- Morita's congruence: `n ≡ m (mod p^k)` implies `mor p n ≡ mor p m (mod p^k)`. -/
lemma mor_congr (hp2 : p ≠ 2) (k : ℕ) {n m : ℕ} (h : (n : ZMod (p ^ k)) = m) :
    ((mor p n : ℤ) : ZMod (p ^ k)) = mor p m := by
  wlog hnm : n ≤ m generalizing n m
  · exact (this h.symm (by omega)).symm
  have hd : p ^ k ∣ m - n := (Nat.modEq_iff_dvd' hnm).1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h)
  obtain ⟨t, ht⟩ := hd
  have hm : m = n + p ^ k * t := by omega
  subst hm
  clear h hnm ht
  induction t with
  | zero => simp
  | succ t ih => rw [mul_add, mul_one, ← add_assoc, mor_add_period hp2, ih]

omit hp in
lemma mor_succ (k n : ℕ) :
    ((mor p (n + 1) : ℤ) : ZMod (p ^ k)) = (mor p n : ZMod (p ^ k)) * (-1) * fac p k n := by
  rw [mor_cast, mor_cast, prod_range_succ, pow_succ]; ring

/-! ### Construction of Morita's `Γ_p` -/

/-- The `k`-th approximant `mor p (appr x k)` of `Γ_p(x)`, where `appr x k < p^k` is the
natural number with `x ≡ appr x k (mod p^k)`. -/
noncomputable def approx (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) (k : ℕ) : ℤ_[p] :=
  ((mor p (x.appr k) : ℤ) : ℤ_[p])

lemma norm_sub_le_iff {x y : ℤ_[p]} {k : ℕ} :
    ‖x - y‖ ≤ (p : ℝ) ^ (-(k : ℤ)) ↔ PadicInt.toZModPow k x = PadicInt.toZModPow k y := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    sub_eq_zero]

lemma approx_congr (hp2 : p ≠ 2) (x : ℤ_[p]) {k m : ℕ} (hkm : k ≤ m) :
    PadicInt.toZModPow k (approx p x m) = PadicInt.toZModPow k (approx p x k) := by
  simp only [approx, map_intCast]
  refine mor_congr hp2 k ?_
  have h := (Nat.modEq_iff_dvd' (x.appr_mono hkm)).2 (x.dvd_appr_sub_appr k m hkm)
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).2 h).symm

lemma cauchySeq_approx (hp2 : p ≠ 2) (x : ℤ_[p]) : CauchySeq (approx p x) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  refine cauchySeq_of_le_geometric (1 / (p : ℝ)) 1 ((div_lt_one (by linarith)).2 hp1)
    (fun m => ?_)
  rw [dist_eq_norm, one_mul, one_div, inv_pow, ← zpow_natCast, ← zpow_neg]
  exact norm_sub_le_iff.2 (approx_congr hp2 x (Nat.le_succ m)).symm

/-- Morita's `p`-adic gamma function, defined as `lim_k mor p (appr x k)`. -/
noncomputable def gammaP (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) : ℤ_[p] :=
  limUnder atTop (approx p x)

lemma toZModPow_gammaP (hp2 : p ≠ 2) (x : ℤ_[p]) (k : ℕ) :
    PadicInt.toZModPow k (gammaP p x) = ((mor p (x.appr k) : ℤ) : ZMod (p ^ k)) := by
  have hT : Tendsto (approx p x) atTop (𝓝 (gammaP p x)) := (cauchySeq_approx hp2 x).tendsto_limUnder
  have hle : ‖gammaP p x - approx p x k‖ ≤ (p : ℝ) ^ (-(k : ℤ)) :=
    le_of_tendsto (hT.sub_const _).norm
      (eventually_atTop.2 ⟨k, fun m hm => norm_sub_le_iff.2 (approx_congr hp2 x hm)⟩)
  rw [norm_sub_le_iff.1 hle, approx, map_intCast]

/-- If `x ≡ n (mod p^k)` then `Γ_p(x) ≡ mor p n (mod p^k)`. -/
lemma toZModPow_gammaP_of (hp2 : p ≠ 2) {x : ℤ_[p]} {k n : ℕ}
    (h : PadicInt.toZModPow k x = (n : ZMod (p ^ k))) :
    PadicInt.toZModPow k (gammaP p x) = ((mor p n : ℤ) : ZMod (p ^ k)) := by
  rw [toZModPow_gammaP hp2]; exact mor_congr hp2 k h

/-- `Γ_p` interpolates Morita's product: `Γ_p(n) = (-1)^n ∏_{0<j<n, p∤j} j` for all `n : ℕ`. -/
theorem gammaP_natCast (hp2 : p ≠ 2) (n : ℕ) : gammaP p n = ((mor p n : ℤ) : ℤ_[p]) := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [toZModPow_gammaP_of hp2 (n := n) (map_natCast _ _), map_intCast]

/-- `Γ_p` is continuous. -/
theorem continuous_gammaP (hp2 : p ≠ 2) : Continuous (gammaP p) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨(p : ℝ) ^ (-(k : ℤ)), zpow_pos (by exact_mod_cast hp.out.pos) _, fun a ha => ?_⟩
  rw [dist_eq_norm] at ha ⊢
  have h1 : PadicInt.toZModPow k a = ((b.appr k : ℕ) : ZMod (p ^ k)) :=
    (norm_sub_le_iff.1 ha.le).trans rfl
  have : PadicInt.toZModPow k (gammaP p a) = PadicInt.toZModPow k (gammaP p b) := by
    rw [toZModPow_gammaP_of hp2 h1, toZModPow_gammaP hp2]
  exact (norm_sub_le_iff.2 this).trans_lt hk

/-- Uniqueness: any continuous `G : ℤ_[p] → ℤ_[p]` with `G n = (-1)^n ∏_{0<j<n, p∤j} j` for all
positive integers `n` equals `gammaP p`. So `gammaP p` is Morita's `p`-adic gamma function. -/
theorem gammaP_unique (hp2 : p ≠ 2) (G : ℤ_[p] → ℤ_[p]) (hG : Continuous G)
    (hval : ∀ n : ℕ, 0 < n → G n = ((mor p n : ℤ) : ℤ_[p])) : G = gammaP p := by
  have hd : DenseRange ((fun z : ℤ_[p] => z + 1) ∘ (Nat.cast : ℕ → ℤ_[p])) :=
    (Function.Surjective.denseRange fun y => ⟨y - 1, by ring⟩).comp PadicInt.denseRange_natCast
      (continuous_add_const 1)
  refine hG.ext_on hd (continuous_gammaP hp2) ?_
  rintro _ ⟨n, rfl⟩
  have := hval (n + 1) (by omega)
  have h2 := gammaP_natCast hp2 (p := p) (n + 1)
  push_cast at this h2
  simp only [Function.comp_apply]
  rw [this, h2]

/-! ### Values used in the refutation -/

theorem gammaP_zero (hp2 : p ≠ 2) : gammaP p 0 = 1 := by
  simpa [mor] using gammaP_natCast hp2 (p := p) 0

theorem gammaP_one (hp2 : p ≠ 2) : gammaP p 1 = -1 := by
  have := gammaP_natCast hp2 (p := p) 1
  simpa [mor, Finset.range_one, Finset.filter_singleton] using this

theorem gammaP_two (hp2 : p ≠ 2) : gammaP p 2 = 1 := by
  have := gammaP_natCast hp2 (p := p) 2
  have h1 : ¬ p ∣ 1 := hp.out.not_dvd_one
  have hs : (range 2).filter (fun x => ¬ p ∣ x) = {1} := by
    ext x
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨h, h'⟩
      interval_cases x
      · simp at h'
      · rfl
    · rintro rfl; exact ⟨by norm_num, h1⟩
  simpa [mor, hs] using this

/-! ### Reading (A): the sign is not a function of `p` (let alone of `p mod 4`) -/

/-- For every odd prime `p`: `Γ_p(1) Γ_p(1-1) = -1` but `Γ_p(2) Γ_p(1-2) ≡ 1 (mod p)`. -/
theorem reflection_products (hp2 : p ≠ 2) :
    gammaP p 1 * gammaP p (1 - 1) = -1 ∧
      PadicInt.toZModPow 1 (gammaP p 2 * gammaP p (1 - 2)) = 1 := by
  refine ⟨by rw [sub_self, gammaP_one hp2, gammaP_zero hp2]; ring, ?_⟩
  have hpz : (p : ZMod (p ^ 1)) = 0 := by
    rw [show (p : ZMod (p ^ 1)) = ((p ^ 1 : ℕ) : ZMod (p ^ 1)) by rw [pow_one],
      ZMod.natCast_self]
  have hp1 := hp.out.one_le
  have hcast : ((p - 1 : ℕ) : ZMod (p ^ 1)) = -1 := by rw [Nat.cast_sub hp1, hpz]; simp
  have hx : PadicInt.toZModPow 1 (1 - 2 : ℤ_[p]) = ((p - 1 : ℕ) : ZMod (p ^ 1)) := by
    rw [hcast, map_sub, map_one, map_ofNat]; ring
  have hnd : ¬ p ∣ p - 1 := fun h => by
    have := Nat.le_of_dvd (by have := hp.out.two_le; omega) h; omega
  have hfac : fac p 1 (p - 1) = -1 := by simp only [fac, hnd, not_false_eq_true, if_true, hcast]
  have hmor : ((mor p (p - 1) : ℤ) : ZMod (p ^ 1)) = 1 := by
    have e1 : ((mor p p : ℤ) : ZMod (p ^ 1)) = mor p 0 := by
      convert mor_add_period hp2 1 0 using 3; simp
    have e2 := mor_succ (p := p) 1 (p - 1)
    rw [Nat.sub_add_cancel hp1, hfac] at e2
    have e0 : ((mor p 0 : ℤ) : ZMod (p ^ 1)) = 1 := by simp [mor]
    rw [e1, e0] at e2
    linear_combination -e2
  rw [map_mul, gammaP_two hp2, map_one, one_mul, toZModPow_gammaP_of hp2 hx, hmor]

/-- For every odd prime `p`, `a ↦ Γ_p(a) Γ_p(1-a)` is not constant on `ℤ_[p]`. -/
theorem reflection_product_not_constant (hp2 : p ≠ 2) :
    ¬ ∃ c : ℤ_[p], ∀ a : ℤ_[p], gammaP p a * gammaP p (1 - a) = c := by
  rintro ⟨c, hc⟩
  obtain ⟨h1, h2⟩ := reflection_products hp2
  rw [hc 2, ← hc 1, h1, map_neg, map_one] at h2
  have : Fact (2 < p ^ 1) := ⟨by rw [pow_one]; exact lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)⟩
  exact ZMod.neg_one_ne_one h2

/-- **Main theorem, reading (A).** There is no function `f` of `p mod 4` such that
`Γ_p(a) Γ_p(1-a) = f(p mod 4)` for every odd prime `p` and every `a ∈ ℤ_[p]`. -/
theorem not_function_of_p_mod_four :
    ¬ ∃ f : ZMod 4 → ℤ, ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∀ a : ℤ_[p], gammaP p a * gammaP p (1 - a) = ((f (p : ZMod 4) : ℤ) : ℤ_[p]) := by
  rintro ⟨f, hf⟩
  exact reflection_product_not_constant (p := 3) (by norm_num) ⟨_, hf 3 (by norm_num)⟩

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ### Reading (B): for the fixed integer `a = 4` the sign is not a function of `p mod 4` -/

/-- `Γ_3(4) Γ_3(1-4) ≡ -1 (mod 3)` and `Γ_7(4) Γ_7(1-4) ≡ 1 (mod 7)`. -/
theorem reflection_four :
    PadicInt.toZModPow 1 (gammaP 3 4 * gammaP 3 (1 - 4)) = -1 ∧
      PadicInt.toZModPow 1 (gammaP 7 4 * gammaP 7 (1 - 4)) = 1 := by
  constructor
  · have hx : PadicInt.toZModPow 1 (1 - 4 : ℤ_[3]) = ((0 : ℕ) : ZMod (3 ^ 1)) := by
      rw [map_sub, map_one, map_ofNat]; decide
    have h4 := gammaP_natCast (p := 3) (by norm_num) 4
    push_cast at h4
    rw [map_mul, h4, map_intCast, toZModPow_gammaP_of (by norm_num) hx]
    decide
  · have hx : PadicInt.toZModPow 1 (1 - 4 : ℤ_[7]) = ((4 : ℕ) : ZMod (7 ^ 1)) := by
      rw [map_sub, map_one, map_ofNat]; decide
    have h4 := gammaP_natCast (p := 7) (by norm_num) 4
    push_cast at h4
    rw [map_mul, h4, map_intCast, toZModPow_gammaP_of (by norm_num) hx]
    decide

/-- **Main theorem, reading (B).** There is no sign function `s` of `p mod 4` with
`Γ_p(4) Γ_p(1-4) = s(p mod 4)` for every odd prime `p`. -/
theorem not_function_of_p_mod_four_at_four :
    ¬ ∃ s : ZMod 4 → ℤˣ, ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      gammaP p 4 * gammaP p (1 - 4) = (((s (p : ZMod 4) : ℤˣ) : ℤ) : ℤ_[p]) := by
  rintro ⟨s, hs⟩
  obtain ⟨h3, h7⟩ := reflection_four
  rw [hs 3 (by norm_num), map_intCast] at h3
  rw [hs 7 (by norm_num), map_intCast, show ((7 : ℕ) : ZMod 4) = ((3 : ℕ) : ZMod 4) by decide]
    at h7
  rcases Int.units_eq_one_or (s ((3 : ℕ) : ZMod 4)) with h | h <;> rw [h] at h3 h7
  · revert h3; decide
  · revert h7; decide

end C716
