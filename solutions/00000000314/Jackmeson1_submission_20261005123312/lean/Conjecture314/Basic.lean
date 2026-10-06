import Mathlib

/-!
# Conjecture 00000000314 is false

Conjecture (verbatim): "Definition: The Markov constant M(α) = limsup 1/‖qα‖ measures the quality of
worst approximation. Conjecture: The set {M(√p) : p prime} is dense in the half-open interval from √5
to 3; and the density follows from the transition statistics of the continued-fraction partial
quotients of square roots of primes."

Here `‖x‖` is the distance from `x` to the nearest integer and the `limsup` is over positive
integers `q → ∞`. We formalize two readings of `M`:

* `markovConst α = limsup_{q → ∞} 1 / (q ‖qα‖)` (the standard Lagrange/Markov value), and
* `markovConstLiteral α = limsup_{q → ∞} 1 / ‖qα‖` (the text's formula as written).

Both take values in `[0, ∞]` (`ℝ≥0∞`, with `1/0 = ∞`).

Pell's equation `x² - p y² = 1` has solutions with `y` arbitrarily large (Mathlib's
`Pell.IsFundamental`). For such a solution, `0 < x - y√p = 1/(x + y√p) < 1/(2y√p)`, so
`‖y√p‖ < 1/(2y√p)` and `1/(y‖y√p‖) > 2√p`. Hence `markovConst √p ≥ 2√p ≥ 2√2` and
`markovConstLiteral √p = ∞` for every prime `p`. Since `√5 < 2√2 < 3`, no value lies in the
nonempty open subinterval `(√5, 2√2)` of `[√5, 3)`, so neither set is dense there.
-/

open Filter Real
open scoped ENNReal

namespace C314

/-- Distance from `x` to the nearest integer: `‖x‖ = inf_{n ∈ ℤ} |x - n|`. -/
noncomputable def distNearestInt (x : ℝ) : ℝ := ⨅ n : ℤ, |x - n|

lemma distNearestInt_nonneg (x : ℝ) : 0 ≤ distNearestInt x :=
  le_ciInf fun _ => abs_nonneg _

lemma distNearestInt_le (x : ℝ) (n : ℤ) : distNearestInt x ≤ |x - n| :=
  ciInf_le ⟨0, by rintro _ ⟨m, rfl⟩; exact abs_nonneg _⟩ n

/-- Standard reading: `M(α) = limsup_{q → ∞} 1 / (q ‖qα‖)` over positive integers `q`,
valued in `[0, ∞]`. -/
noncomputable def markovConst (α : ℝ) : ℝ≥0∞ :=
  limsup (fun q : ℕ => (ENNReal.ofReal ((q : ℝ) * distNearestInt ((q : ℝ) * α)))⁻¹) atTop

/-- Literal reading of the text: `M(α) = limsup_{q → ∞} 1 / ‖qα‖`, valued in `[0, ∞]`. -/
noncomputable def markovConstLiteral (α : ℝ) : ℝ≥0∞ :=
  limsup (fun q : ℕ => (ENNReal.ofReal (distNearestInt ((q : ℝ) * α)))⁻¹) atTop

/-- The set `{F(√p) : p prime}` for a given reading `F` of the Markov constant. -/
def valueSet (F : ℝ → ℝ≥0∞) : Set ℝ≥0∞ := {m | ∃ p : ℕ, p.Prime ∧ m = F (√(p : ℝ))}

/-- The half-open interval `[√5, 3)`. -/
noncomputable def targetInterval : Set ℝ≥0∞ := Set.Ico (ENNReal.ofReal √5) 3

/-- Density of `S` in `I`, topological form: `I ⊆ closure S`. -/
def DenseInTop (S I : Set ℝ≥0∞) : Prop := I ⊆ closure S

/-- Density of `S` in `I`, interval form: between any two points `a < b` of `I` there is a
point of `S`. -/
def DenseInIntervals (S I : Set ℝ≥0∞) : Prop :=
  ∀ a ∈ I, ∀ b ∈ I, a < b → ∃ s ∈ S, a < s ∧ s < b

/-! ### Pell solutions with large `y` -/

/-- For a positive non-square `d`, Pell's equation `x² - d y² = 1` has solutions with `x > 0`
and `y` larger than any given bound. -/
lemma pell_large (d : ℤ) (h₀ : 0 < d) (hd : ¬IsSquare d) (N : ℕ) :
    ∃ x y : ℤ, 0 < x ∧ (N : ℤ) < y ∧ x ^ 2 - d * y ^ 2 = 1 := by
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare h₀ hd
  have key : ∀ n : ℕ, (n : ℤ) ≤ (a ^ (n : ℤ)).y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := ha.y_strictMono (show (n : ℤ) < (n : ℤ) + 1 by omega)
      simp only at this
      push_cast
      omega
  refine ⟨(a ^ ((N + 1 : ℕ) : ℤ)).x, (a ^ ((N + 1 : ℕ) : ℤ)).y,
    Pell.Solution₁.x_zpow_pos ha.x_pos _, ?_, (a ^ ((N + 1 : ℕ) : ℤ)).prop⟩
  have := key (N + 1)
  push_cast at this ⊢
  omega

/-- The Pell estimate: if `x² - d y² = 1` with `x, y > 0`, then
`‖y√d‖ ≤ x - y√d = 1/(x + y√d)` and `y (x - y√d) ≤ 1/(2√d)`. -/
lemma pell_bound (d : ℕ) (hd : 0 < d) (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 2 - (d : ℤ) * y ^ 2 = 1) :
    distNearestInt ((y : ℝ) * √(d : ℝ)) * (2 * (y : ℝ) * √(d : ℝ)) ≤ 1 := by
  set s := √(d : ℝ) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hss : s * s = (d : ℝ) := Real.mul_self_sqrt (by positivity)
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hR : (x : ℝ) ^ 2 - (d : ℝ) * (y : ℝ) ^ 2 = 1 := by exact_mod_cast h
  -- `(x - y s)(x + y s) = 1`
  have hprod : ((x : ℝ) - y * s) * ((x : ℝ) + y * s) = 1 := by
    have : ((x : ℝ) - y * s) * ((x : ℝ) + y * s) = (x : ℝ) ^ 2 - (s * s) * (y : ℝ) ^ 2 := by ring
    rw [this, hss, hR]
  have hpos : 0 < (x : ℝ) + y * s := by positivity
  have hdiff : 0 < (x : ℝ) - y * s := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  have hxys : y * s < (x : ℝ) := by linarith
  have hdist : distNearestInt ((y : ℝ) * s) ≤ (x : ℝ) - y * s := by
    have := distNearestInt_le ((y : ℝ) * s) x
    rwa [abs_sub_comm, abs_of_pos hdiff] at this
  calc distNearestInt ((y : ℝ) * s) * (2 * (y : ℝ) * s)
      ≤ ((x : ℝ) - y * s) * (2 * (y : ℝ) * s) :=
        mul_le_mul_of_nonneg_right hdist (by positivity)
    _ ≤ ((x : ℝ) - y * s) * ((x : ℝ) + y * s) :=
        mul_le_mul_of_nonneg_left (by linarith) hdiff.le
    _ = 1 := hprod

/-- From `t * c ≤ 1` with `t, c ≥ 0`, get `ofReal c ≤ (ofReal t)⁻¹`. -/
lemma ofReal_le_inv_of_mul_le_one {t c : ℝ} (hc : 0 ≤ c) (h : t * c ≤ 1) :
    ENNReal.ofReal c ≤ (ENNReal.ofReal t)⁻¹ := by
  rw [ENNReal.le_inv_iff_mul_le, ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

lemma prime_not_isSquare {p : ℕ} (hp : p.Prime) : ¬IsSquare (p : ℤ) :=
  (Nat.prime_iff_prime_int.mp hp).not_isSquare

/-- For a prime `p` and any `N`, there is `q ≥ N` with
`q ‖q√p‖ · 2√p ≤ 1` and `‖q√p‖ · 2q√p ≤ 1`, `q ≥ 1`. -/
lemma exists_good_q {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∃ q : ℕ, N ≤ q ∧ 1 ≤ q ∧
      distNearestInt ((q : ℝ) * √(p : ℝ)) * (2 * (q : ℝ) * √(p : ℝ)) ≤ 1 := by
  have hp0 : 0 < p := hp.pos
  obtain ⟨x, y, hx, hy, h⟩ := pell_large (p : ℤ) (by exact_mod_cast hp0) (prime_not_isSquare hp) N
  have hy0 : 0 < y := lt_of_le_of_lt (Int.natCast_nonneg N) hy
  refine ⟨y.toNat, by omega, by omega, ?_⟩
  have hcast : ((y.toNat : ℕ) : ℝ) = (y : ℝ) := by
    have : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy0.le
    exact_mod_cast this
  rw [hcast]
  exact pell_bound p hp0 x y hx hy0 h

/-! ### The two readings of `M(√p)` -/

/-- Standard reading: `M(√p) ≥ 2√p` for every prime `p`. -/
theorem markovConst_sqrt_prime_ge {p : ℕ} (hp : p.Prime) :
    ENNReal.ofReal (2 * √(p : ℝ)) ≤ markovConst √(p : ℝ) := by
  apply le_limsup_of_frequently_le'
  rw [frequently_atTop]
  intro N
  obtain ⟨q, hqN, -, hq⟩ := exists_good_q hp N
  refine ⟨q, hqN, ofReal_le_inv_of_mul_le_one (by positivity) ?_⟩
  calc (q : ℝ) * distNearestInt ((q : ℝ) * √(p : ℝ)) * (2 * √(p : ℝ))
      = distNearestInt ((q : ℝ) * √(p : ℝ)) * (2 * (q : ℝ) * √(p : ℝ)) := by ring
    _ ≤ 1 := hq

/-- Literal reading: `limsup 1/‖q√p‖ = ∞` for every prime `p`. -/
theorem markovConstLiteral_sqrt_prime {p : ℕ} (hp : p.Prime) :
    markovConstLiteral √(p : ℝ) = ⊤ := by
  have hs1 : (1 : ℝ) ≤ √(p : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast hp.one_lt.le
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  apply le_limsup_of_frequently_le'
  rw [frequently_atTop]
  intro N
  obtain ⟨q, hqN, -, hq⟩ := exists_good_q hp (N + ⌈(r : ℝ)⌉₊)
  refine ⟨q, by omega, ?_⟩
  have hrq : (r : ℝ) ≤ q := by
    have h1 := Nat.le_ceil (r : ℝ)
    have h2 : ((N + ⌈(r : ℝ)⌉₊ : ℕ) : ℝ) ≤ q := by exact_mod_cast hqN
    push_cast at h2
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal (2 * (q : ℝ) * √(p : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
        nlinarith
    _ ≤ (ENNReal.ofReal (distNearestInt ((q : ℝ) * √(p : ℝ))))⁻¹ :=
        ofReal_le_inv_of_mul_le_one (by positivity) hq

/-! ### Non-density -/

lemma sqrt5_lt_two_sqrt2 : √5 < 2 * √2 := by
  have h : 2 * √2 = √8 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma two_sqrt2_lt_three : 2 * √2 < 3 := by
  have h : 2 * √2 = √8 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h, show (3 : ℝ) = √9 by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- If every value `F(√p)` is at least `2√2`, then `{F(√p)}` misses the open subinterval
`(√5, 2√2)` of `[√5, 3)`, so it is dense there in neither sense. -/
theorem not_dense_of_ge {F : ℝ → ℝ≥0∞} (hF : ∀ p : ℕ, p.Prime → ENNReal.ofReal (2 * √2) ≤ F √(p : ℝ)) :
    ¬ DenseInTop (valueSet F) targetInterval ∧ ¬ DenseInIntervals (valueSet F) targetInterval := by
  set a := ENNReal.ofReal √5
  set b := ENNReal.ofReal (2 * √2)
  have hab : a < b := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr sqrt5_lt_two_sqrt2
  have hb3 : b < 3 := by
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr two_sqrt2_lt_three
  have ha : a ∈ targetInterval := ⟨le_rfl, hab.trans hb3⟩
  have hbI : b ∈ targetInterval := ⟨hab.le, hb3⟩
  have hsub : valueSet F ⊆ Set.Ici b := by
    rintro _ ⟨p, hp, rfl⟩; exact hF p hp
  refine ⟨fun hD => ?_, fun hD => ?_⟩
  · have : a ∈ Set.Ici b := closure_minimal hsub isClosed_Ici (hD ha)
    exact absurd this (not_le.mpr hab)
  · obtain ⟨s, hs, -, hsb⟩ := hD a ha b hbI hab
    exact absurd (hsub hs) (not_le.mpr hsb)

/-- **Main theorem.** Under both the standard reading `M(α) = limsup 1/(q‖qα‖)` and the literal
reading `M(α) = limsup 1/‖qα‖`, the set `{M(√p) : p prime}` is not dense in `[√5, 3)`, neither in
the sense `[√5, 3) ⊆ closure {M(√p)}` nor in the sense that every pair `a < b` in `[√5, 3)`
has a value strictly between them. Concretely, no value lies in `(√5, 2√2)`. -/
theorem conjecture314_false :
    (¬ DenseInTop (valueSet markovConst) targetInterval ∧
      ¬ DenseInIntervals (valueSet markovConst) targetInterval) ∧
    (¬ DenseInTop (valueSet markovConstLiteral) targetInterval ∧
      ¬ DenseInIntervals (valueSet markovConstLiteral) targetInterval) := by
  refine ⟨not_dense_of_ge fun p hp => ?_, not_dense_of_ge fun p hp => ?_⟩
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (markovConst_sqrt_prime_ge hp)
    have : √2 ≤ √(p : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hp.two_le)
    linarith
  · rw [markovConstLiteral_sqrt_prime hp]; exact le_top

end C314
