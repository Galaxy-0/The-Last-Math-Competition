import Mathlib

/-!
# Conjecture 00000000125 is false

**Conjecture (as stated).** The number of elements of `SL₂(F_p)` whose trace has absolute value a
prime is asymptotic to `c · p² / log p`, with `c` explicit from a Sato–Tate type density for the
trace distribution.

The trace of `A ∈ SL₂(F_p)` lies in `F_p = ZMod p`; to speak of its absolute value being prime we
lift it to `ℤ`.  We treat an arbitrary lift `L : ZMod p → ℤ` and specialise to the two standard
lifts: the centered representative `ZMod.valMinAbs` (in `(-p/2, p/2]`) and the representative
`ZMod.val` in `[0, p)`.

**Disproof.** For `p ≥ 5` both lifts send the trace value `2` to the prime `2`.  The matrices
`[[a, b], [-(a-1)² b⁻¹, 2 - a]]` with `a ∈ F_p`, `b ∈ F_p^×` have determinant one and trace `2`, and
they are pairwise distinct, so `N(p) ≥ p (p - 1)`.  Hence `N(p) / (p² / log p) ≥ log p / 2 → ∞`
along the primes: `N(p)` is not `O(p² / log p)`, so `N(p) ~ c p² / log p` fails for every real `c`.
-/

open Filter Topology Asymptotics

namespace C125

/-- The primes, as the subtype `{p : ℕ // p.Prime}` with the order induced from `ℕ`; its filter
`atTop` is "`p → ∞` through the primes". -/
abbrev PrimeNat := {p : ℕ // p.Prime}

instance : Nonempty PrimeNat := ⟨⟨2, Nat.prime_two⟩⟩

/-- The group `SL₂(F_p)`, as Mathlib's special linear group over `ZMod p`. -/
abbrev SL2 (p : ℕ) := Matrix.SpecialLinearGroup (Fin 2) (ZMod p)

/-- The trace of an element of `SL₂(ZMod p)` (Mathlib's `Matrix.trace`). -/
def tr {p : ℕ} (A : SL2 p) : ZMod p := Matrix.trace (A : Matrix (Fin 2) (Fin 2) (ZMod p))

/-- Centered lift `ZMod n → ℤ`: the representative in `(-n/2, n/2]` (`ZMod.valMinAbs`). -/
def centeredLift (n : ℕ) (x : ZMod n) : ℤ := x.valMinAbs

/-- Standard lift `ZMod n → ℤ`: the representative in `[0, n)` (`ZMod.val`). -/
def standardLift (n : ℕ) (x : ZMod n) : ℤ := (x.val : ℤ)

/-- `N L p` is the number of `A ∈ SL₂(ZMod p)` such that the absolute value of the integer lift
`L p (tr A)` of the trace is a prime number. -/
noncomputable def N (L : ∀ n : ℕ, ZMod n → ℤ) (p : ℕ) : ℕ :=
  Nat.card {A : SL2 p // (L p (tr A)).natAbs.Prime}

/-- The conjecture for a given lift `L`: there is `c > 0` with `N(p) / (c p² / log p) → 1` as
`p → ∞` through the primes. -/
def Conjecture125 (L : ∀ n : ℕ, ZMod n → ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto (fun p : PrimeNat =>
    (N L p : ℝ) / (c * ((p : ℕ) : ℝ) ^ 2 / Real.log ((p : ℕ) : ℝ))) atTop (𝓝 1)

/-! ### A family of trace-`2` elements -/

/-- The matrix `[[a, b], [-(a-1)² b⁻¹, 2 - a]]`, an element of `SL₂(ZMod p)` of trace `2`. -/
def traceTwo {p : ℕ} (a : ZMod p) (b : (ZMod p)ˣ) : SL2 p :=
  ⟨!![a, (b : ZMod p); -(a - 1) ^ 2 * ((b⁻¹ : (ZMod p)ˣ) : ZMod p), 2 - a], by
    rw [Matrix.det_fin_two_of]
    have hb : (b : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := Units.mul_inv b
    linear_combination (a - 1) ^ 2 * hb⟩

theorem tr_traceTwo {p : ℕ} (a : ZMod p) (b : (ZMod p)ˣ) : tr (traceTwo a b) = 2 := by
  simp [tr, traceTwo, Matrix.trace_fin_two_of]

theorem traceTwo_injective {p : ℕ} :
    Function.Injective (fun x : ZMod p × (ZMod p)ˣ => traceTwo x.1 x.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h' := congrArg (fun A : SL2 p => (A : Matrix (Fin 2) (Fin 2) (ZMod p))) h
  have h00 := congrFun (congrFun h' 0) 0
  have h01 := congrFun (congrFun h' 0) 1
  simp only [traceTwo, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01
  exact Prod.ext h00 (Units.ext h01)

/-- **Lower bound.** If the lift of the trace value `2` has prime absolute value, then
`N L p ≥ p (p - 1)`. -/
theorem lower_bound (L : ∀ n : ℕ, ZMod n → ℤ) {p : ℕ} (hp : p.Prime)
    (hL : (L p 2).natAbs.Prime) : p * (p - 1) ≤ N L p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let f : ZMod p × (ZMod p)ˣ → {A : SL2 p // (L p (tr A)).natAbs.Prime} :=
    fun x => ⟨traceTwo x.1 x.2, by rw [tr_traceTwo]; exact hL⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact traceTwo_injective (congrArg Subtype.val hxy)
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card (α := (ZMod p)ˣ),
    ZMod.card_units p] at h
  exact h

/-! ### The two standard lifts send `2` to `2` for `p ≥ 5` -/

theorem centeredLift_two {p : ℕ} (hp : 4 ≤ p) : (centeredLift p 2).natAbs = 2 := by
  have h : ((2 : ℕ) : ZMod p).valMinAbs = 2 := ZMod.valMinAbs_natCast_of_le_half (by omega)
  simp only [Nat.cast_ofNat] at h
  simp [centeredLift, h]

theorem standardLift_two {p : ℕ} (hp : 3 ≤ p) : (standardLift p 2).natAbs = 2 := by
  have h : (2 : ZMod p).val = 2 := ZMod.val_ofNat_of_lt (show 2 < p by omega)
  simp [standardLift, h]

/-! ### Asymptotics along the primes -/

theorem tendsto_primes_atTop : Tendsto (fun p : PrimeNat => (p : ℕ)) atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone (f := fun p : PrimeNat => (p : ℕ)) (fun _ _ h => h)
  intro b
  obtain ⟨p, hbp, hp⟩ := Nat.exists_infinite_primes b
  exact ⟨⟨p, hp⟩, hbp⟩

/-- **`N(p)` is not `O(p² / log p)`** along the primes, for every lift `L` that sends `2` to a
prime (in absolute value) for all large primes `p`. -/
theorem not_isBigO (L : ∀ n : ℕ, ZMod n → ℤ)
    (hL : ∃ p₀ : ℕ, ∀ p : ℕ, p₀ ≤ p → p.Prime → (L p 2).natAbs.Prime) :
    ¬ (fun p : PrimeNat => (N L p : ℝ)) =O[atTop]
      (fun p : PrimeNat => ((p : ℕ) : ℝ) ^ 2 / Real.log ((p : ℕ) : ℝ)) := by
  intro h
  obtain ⟨p₀, hp₀⟩ := hL
  obtain ⟨C, hC⟩ := h.bound
  have hlog : Tendsto (fun p : PrimeNat => Real.log ((p : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_primes_atTop)
  have h1 : ∀ᶠ p : PrimeNat in atTop, 2 * C < Real.log ((p : ℕ) : ℝ) :=
    hlog.eventually_gt_atTop _
  have h2 : ∀ᶠ p : PrimeNat in atTop, max p₀ 3 ≤ (p : ℕ) :=
    tendsto_primes_atTop.eventually (eventually_ge_atTop _)
  obtain ⟨⟨p, hp⟩, hCp, h1p, h2p⟩ := (hC.and (h1.and h2)).exists
  simp only at hCp h1p h2p
  have hp3 : 3 ≤ p := le_of_max_le_right h2p
  have hlb := lower_bound L hp (hp₀ p (le_of_max_le_left h2p) hp)
  set x : ℝ := (p : ℝ) with hx
  have hx3 : (3 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hp3
  have hlb' : x * (x - 1) ≤ (N L p : ℝ) := by
    have : ((p * (p - 1) : ℕ) : ℝ) ≤ (N L p : ℝ) := by exact_mod_cast hlb
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one] at this
    exact this
  have hℓ : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hℓ.le)] at hCp
  have hmain : Real.log x * (x * (x - 1)) ≤ C * x ^ 2 := by
    have := mul_le_mul_of_nonneg_left (hlb'.trans hCp) hℓ.le
    calc Real.log x * (x * (x - 1)) ≤ Real.log x * (C * (x ^ 2 / Real.log x)) := this
      _ = C * x ^ 2 := by field_simp
  nlinarith [mul_pos (sub_pos.2 h1p) (by positivity : (0 : ℝ) < x ^ 2),
    mul_nonneg (mul_nonneg hℓ.le (by linarith : (0 : ℝ) ≤ x)) (by linarith : (0 : ℝ) ≤ x - 2)]

/-- **No asymptotic equivalence `N(p) ~ c p² / log p`** along the primes, for any real `c`. -/
theorem not_isEquivalent (L : ∀ n : ℕ, ZMod n → ℤ)
    (hL : ∃ p₀ : ℕ, ∀ p : ℕ, p₀ ≤ p → p.Prime → (L p 2).natAbs.Prime) (c : ℝ) :
    ¬ (fun p : PrimeNat => (N L p : ℝ)) ~[atTop]
      (fun p : PrimeNat => c * ((p : ℕ) : ℝ) ^ 2 / Real.log ((p : ℕ) : ℝ)) := by
  intro h
  apply not_isBigO L hL
  refine h.isBigO.trans ?_
  have e : (fun p : PrimeNat => c * ((p : ℕ) : ℝ) ^ 2 / Real.log ((p : ℕ) : ℝ)) =
      fun p : PrimeNat => c * (((p : ℕ) : ℝ) ^ 2 / Real.log ((p : ℕ) : ℝ)) := by
    funext p; ring
  rw [e]
  exact (isBigO_refl _ _).const_mul_left c

/-- **No real `c` (positive or not) makes `N(p) / (c p² / log p) → 1`** along the primes. -/
theorem not_tendsto_ratio (L : ∀ n : ℕ, ZMod n → ℤ)
    (hL : ∃ p₀ : ℕ, ∀ p : ℕ, p₀ ≤ p → p.Prime → (L p 2).natAbs.Prime) :
    ¬ ∃ c : ℝ, Tendsto (fun p : PrimeNat =>
      (N L p : ℝ) / (c * ((p : ℕ) : ℝ) ^ 2 / Real.log ((p : ℕ) : ℝ))) atTop (𝓝 1) := by
  rintro ⟨c, hc⟩
  exact not_isEquivalent L hL c (isEquivalent_of_tendsto_one hc)

theorem centeredLift_hyp :
    ∃ p₀ : ℕ, ∀ p : ℕ, p₀ ≤ p → p.Prime → (centeredLift p 2).natAbs.Prime :=
  ⟨4, fun p hp _ => by rw [centeredLift_two hp]; exact Nat.prime_two⟩

theorem standardLift_hyp :
    ∃ p₀ : ℕ, ∀ p : ℕ, p₀ ≤ p → p.Prime → (standardLift p 2).natAbs.Prime :=
  ⟨3, fun p hp _ => by rw [standardLift_two hp]; exact Nat.prime_two⟩

/-- **Main theorem.** The conjecture fails for both standard integer lifts of the trace
(centered `valMinAbs` and `[0, p)` representative `val`); moreover, for both lifts the count is
not even `O(p² / log p)` along the primes. -/
theorem conjecture125_false :
    ¬ Conjecture125 centeredLift ∧ ¬ Conjecture125 standardLift ∧
    ¬ (fun p : PrimeNat => (N centeredLift p : ℝ)) =O[atTop]
      (fun p : PrimeNat => ((p : ℕ) : ℝ) ^ 2 / Real.log ((p : ℕ) : ℝ)) ∧
    ¬ (fun p : PrimeNat => (N standardLift p : ℝ)) =O[atTop]
      (fun p : PrimeNat => ((p : ℕ) : ℝ) ^ 2 / Real.log ((p : ℕ) : ℝ)) :=
  ⟨fun ⟨c, _, hc⟩ => not_tendsto_ratio centeredLift centeredLift_hyp ⟨c, hc⟩,
   fun ⟨c, _, hc⟩ => not_tendsto_ratio standardLift standardLift_hyp ⟨c, hc⟩,
   not_isBigO centeredLift centeredLift_hyp,
   not_isBigO standardLift standardLift_hyp⟩

end C125
