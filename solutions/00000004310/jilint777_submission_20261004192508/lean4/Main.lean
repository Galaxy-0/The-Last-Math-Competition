/-!
# Conjecture 00000004310 is false: equal discriminants force isomorphic unit groups

The conjecture: *there exist two imaginary quadratic fields of the same discriminant whose
3-parts of the class groups are isomorphic while their unit groups are not; the smallest such
discriminant has seven digits.*

Every imaginary quadratic field is `ℚ(√m)` for a unique squarefree integer `m < 0` (Marcus,
*Number Fields*, Ch. 2), its ring of integers is `O_m = ℤ[√m]` (`m ≢ 1 mod 4`) or
`ℤ[(1+√m)/2]` (`m ≡ 1 mod 4`), and its discriminant is `disc m = m` or `4m`.  Everything below is
built from scratch in core Lean 4 (no Mathlib):

* `Squarefree`, `IsImagQuadParam m` (`m < 0` squarefree), `disc m`.
* `disc_injective`: `disc m₁ = disc m₂ → m₁ = m₂` (so two imaginary quadratic fields with the same
  discriminant are the same field); `disc_fundamental`, `mOfDisc_disc` (explicit inverse).
* `QR` with `mul t n`: the quadratic ring `ℤ[ω]`, `ω² = tω − n`, as pairs `(a, b) ↦ a + bω`;
  proven commutative, associative, unital, distributive; `norm`, `conj`, `trace`, `discBasis`.
* `fT m`, `fN m`: the parameters of `O_m`; `sqrtM_sq` (`√m ∈ O_m`), `field_discBasis`
  (`disc(1, ω) = disc m`), `halfCoords_mul` (the pair model multiplies like `ℚ(√m)`),
  `integral_iff` (`(x + y√m)/2` has integral norm iff it lies in `O_m`).
* `tD D`, `nD D`: the quadratic order of any discriminant `D ≡ 0, 1 mod 4`; `fT_eq`, `fN_eq`:
  `O_m` is the order of discriminant `disc m`.
* `IsUnitQ`, `UnitGrp`: the unit group (elements with an inverse), `isUnit_iff_norm`.
* `units_classification`: units of the order of discriminant `D < 0` are listed by
  `unitList D`, which has `w D` elements (`4` for `D = −4`, `6` for `D = −3`, `2` otherwise) and
  consists of the powers of one generator (`unitList_eq_pows`): the unit group is cyclic of order
  `w D`, a function of `D` alone.
* `MulIso`: isomorphisms of multiplicative structures.  `orderUnits_iso_of_w_eq`: unit groups of
  orders whose discriminants have the same `w` are isomorphic.
* `conjecture_00000004310_false`: `¬ Claim C3` for every predicate `C3` standing for the
  class-group condition; `no_witness_discriminant`, `smallest_seven_digit_false`;
  `order_claim_false` (the reading with orders of the same discriminant).
* Non-vacuity: `param_neg1`, `param_neg3`, `param_neg2`, … and `fieldUnits_not_iso`
  (`O_{-1}^× ≇ O_{-2}^×`, so "not isomorphic" is not an empty condition).
-/

namespace Conj4310

/-- Polynomial identities over `ℤ`: distribute, sort monomials (AC), re-associate to the left so
that numerals become coefficients, then `omega` (monomials are atoms). -/
macro "poly_omega" : tactic => `(tactic| (
  (try simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc, Int.mul_comm,
    Int.mul_left_comm, Int.neg_mul, Int.mul_neg, Int.mul_one, Int.one_mul, Int.mul_zero,
    Int.zero_mul]) <;>
  (try simp only [← Int.mul_assoc]) <;>
  omega))

/-! ## 1. Squarefree integers and the discriminant -/

/-- `m` is squarefree: the only integers whose square divides `m` are `±1`. -/
def Squarefree (m : Int) : Prop := ∀ d : Int, d * d ∣ m → d = 1 ∨ d = -1

/-- `m` parametrises an imaginary quadratic field `ℚ(√m)`. -/
def IsImagQuadParam (m : Int) : Prop := m < 0 ∧ Squarefree m

/-- The discriminant of `ℚ(√m)`, `m` squarefree. -/
def disc (m : Int) : Int := if m % 4 = 1 then m else 4 * m

theorem Squarefree.emod_four_ne_zero {m : Int} (h : Squarefree m) : m % 4 ≠ 0 := by
  intro h0
  have h4 : (2 : Int) * 2 ∣ m := Int.dvd_of_emod_eq_zero h0
  rcases h 2 h4 with h' | h' <;> omega

/-- A decidable test: no `k² ∣ n` for `2 ≤ k ≤ n`. -/
def SqfCheck (n : Nat) : Prop := ∀ k, k < n + 1 → 2 ≤ k → n % (k * k) ≠ 0

instance (n : Nat) : Decidable (SqfCheck n) := by unfold SqfCheck; infer_instance

theorem squarefree_of_check {m : Int} (hm : m ≠ 0) (h : SqfCheck m.natAbs) : Squarefree m := by
  intro d hd
  have hd' : d.natAbs * d.natAbs ∣ m.natAbs := by
    rw [← Int.natAbs_mul]; exact Int.natAbs_dvd_natAbs.mpr hd
  have hpos : 0 < m.natAbs := Int.natAbs_pos.mpr hm
  have hle : d.natAbs * d.natAbs ≤ m.natAbs := Nat.le_of_dvd hpos hd'
  have hk : d.natAbs ≤ 1 := by
    apply Nat.not_lt.mp; intro h2
    have hsq : d.natAbs ≤ d.natAbs * d.natAbs := Nat.le_mul_of_pos_right _ (by omega)
    exact h d.natAbs (by omega) (by omega) (Nat.mod_eq_zero_of_dvd hd')
  rcases Nat.lt_or_ge d.natAbs 1 with h0 | h1
  · have hd0 : d = 0 := by omega
    subst hd0
    have : m = 0 := Int.zero_dvd.mp (by simpa using hd)
    exact absurd this hm
  · omega

theorem param_of_check {m : Int} (hm : m < 0) (h : SqfCheck m.natAbs) : IsImagQuadParam m :=
  ⟨hm, squarefree_of_check (by omega) h⟩

theorem param_neg1 : IsImagQuadParam (-1) := param_of_check (by decide) (by decide)
theorem param_neg2 : IsImagQuadParam (-2) := param_of_check (by decide) (by decide)
theorem param_neg3 : IsImagQuadParam (-3) := param_of_check (by decide) (by decide)
theorem param_neg5 : IsImagQuadParam (-5) := param_of_check (by decide) (by decide)
theorem param_neg23 : IsImagQuadParam (-23) := param_of_check (by decide) (by decide)
theorem not_param_neg4 : ¬ IsImagQuadParam (-4) := fun h =>
  h.2.emod_four_ne_zero (by decide)

/-- **Injectivity of the discriminant** (on all integers, a fortiori on squarefree ones). -/
theorem disc_injective {m₁ m₂ : Int} (h : disc m₁ = disc m₂) : m₁ = m₂ := by
  unfold disc at h; split at h <;> split at h <;> omega

theorem disc_neg {m : Int} (h : m < 0) : disc m < 0 := by
  unfold disc; split <;> omega

theorem disc_mod_four (m : Int) : disc m % 4 = 0 ∨ disc m % 4 = 1 := by
  unfold disc; split <;> omega

/-- Values of `disc` on squarefree `m` are fundamental discriminants. -/
theorem disc_fundamental {m : Int} (h : Squarefree m) :
    disc m % 4 = 1 ∨ disc m % 16 = 8 ∨ disc m % 16 = 12 := by
  have := h.emod_four_ne_zero
  unfold disc; split <;> omega

/-- Recover `m` from the discriminant. -/
def mOfDisc (D : Int) : Int := if D % 4 = 1 then D else D / 4

theorem mOfDisc_disc (m : Int) : mOfDisc (disc m) = m := by
  unfold mOfDisc disc; split <;> (try split) <;> omega

/-! ## 2. Quadratic rings `ℤ[ω]`, `ω² = tω − n` -/

/-- `⟨a, b⟩` stands for `a + bω`. -/
structure QR where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace QR

theorem ext' {x y : QR} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; simp_all

def one : QR := ⟨1, 0⟩
def zero : QR := ⟨0, 0⟩
def omega : QR := ⟨0, 1⟩
def add (x y : QR) : QR := ⟨x.a + y.a, x.b + y.b⟩
def neg (x : QR) : QR := ⟨-x.a, -x.b⟩
/-- `(a + bω)(c + dω) = (ac − n bd) + (ad + bc + t bd) ω`. -/
def mul (t n : Int) (x y : QR) : QR :=
  ⟨x.a * y.a - n * (x.b * y.b), x.a * y.b + x.b * y.a + t * (x.b * y.b)⟩
/-- `N(a + bω) = a² + t ab + n b²`. -/
def norm (t n : Int) (x : QR) : Int := x.a * x.a + t * (x.a * x.b) + n * (x.b * x.b)
/-- `Tr(a + bω) = 2a + tb`. -/
def trace (t : Int) (x : QR) : Int := 2 * x.a + t * x.b
/-- The conjugate `a + bω̄ = (a + tb) − bω`. -/
def conj (t : Int) (x : QR) : QR := ⟨x.a + t * x.b, -x.b⟩
/-- Powers. -/
def pow (t n : Int) (g : QR) : Nat → QR
  | 0 => one
  | k + 1 => mul t n (pow t n g k) g

theorem omega_sq (t n : Int) : mul t n omega omega = ⟨-n, t⟩ := by
  apply ext' <;> simp [mul, omega]

theorem mul_comm (t n : Int) (x y : QR) : mul t n x y = mul t n y x := by
  apply ext' <;> simp only [mul] <;>
    poly_omega

theorem mul_assoc (t n : Int) (x y z : QR) :
    mul t n (mul t n x y) z = mul t n x (mul t n y z) := by
  apply ext' <;> simp only [mul] <;>
    poly_omega

theorem one_mul (t n : Int) (x : QR) : mul t n one x = x := by
  apply ext' <;> simp [mul, one]

theorem mul_one (t n : Int) (x : QR) : mul t n x one = x := by
  rw [mul_comm, one_mul]

theorem mul_add (t n : Int) (x y z : QR) : mul t n x (add y z) = add (mul t n x y) (mul t n x z) := by
  apply ext' <;> simp only [mul, add] <;>
    poly_omega

theorem mul_left_comm (t n : Int) (x y z : QR) :
    mul t n x (mul t n y z) = mul t n y (mul t n x z) := by
  rw [← mul_assoc, mul_comm t n x y, mul_assoc]

theorem norm_mul (t n : Int) (x y : QR) :
    norm t n (mul t n x y) = norm t n x * norm t n y := by
  simp only [norm, mul]
  poly_omega

theorem mul_conj (t n : Int) (x : QR) : mul t n x (conj t x) = ⟨norm t n x, 0⟩ := by
  apply ext' <;> simp only [mul, conj, norm] <;>
    poly_omega

/-- `4 N(x) = Tr(x)² + (4n − t²) b²`: the norm form is positive definite when `t² < 4n`. -/
theorem four_norm (t n : Int) (x : QR) :
    4 * norm t n x = trace t x * trace t x + (4 * n - t * t) * (x.b * x.b) := by
  simp only [norm, trace]
  poly_omega

/-- The discriminant `det (Tr(eᵢ eⱼ))` of the basis `e₁ = 1`, `e₂ = ω`. -/
def discBasis (t n : Int) : Int :=
  trace t (mul t n one one) * trace t (mul t n omega omega)
    - trace t (mul t n one omega) * trace t (mul t n omega one)

theorem discBasis_eq (t n : Int) : discBasis t n = t * t - 4 * n := by
  simp only [discBasis, trace, mul, one, omega]
  poly_omega

end QR

open QR

theorem mul_self_nonneg' (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · rw [← Int.neg_mul_neg]; exact Int.mul_nonneg (by omega) (by omega)

/-- If `T² < (k+1)²` with `k ≥ 0` then `|T| ≤ k`. -/
theorem abs_le_of_sq_lt (k T : Int) (hk : 0 ≤ k) (h : T * T < (k + 1) * (k + 1)) :
    -k ≤ T ∧ T ≤ k := by
  constructor
  · apply Int.not_lt.mp; intro hT
    have : (k + 1) * (k + 1) ≤ (-T) * (-T) :=
      Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
    rw [Int.neg_mul_neg] at this; omega
  · apply Int.not_lt.mp; intro hT
    have : (k + 1) * (k + 1) ≤ T * T :=
      Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
    omega

/-! ## 3. Rings of integers of imaginary quadratic fields and quadratic orders -/

/-- `O_m = ℤ[ω]` with `ω = (1+√m)/2` (`t = 1`) if `m ≡ 1 mod 4`, else `ω = √m` (`t = 0`). -/
def fT (m : Int) : Int := if m % 4 = 1 then 1 else 0
/-- `n = N(ω)`: `(1 − m)/4` or `−m`. -/
def fN (m : Int) : Int := if m % 4 = 1 then (1 - m) / 4 else -m
/-- `√m ∈ O_m`: `2ω − 1` or `ω`. -/
def sqrtM (m : Int) : QR := if m % 4 = 1 then ⟨-1, 2⟩ else ⟨0, 1⟩

theorem sqrtM_sq (m : Int) : mul (fT m) (fN m) (sqrtM m) (sqrtM m) = ⟨m, 0⟩ := by
  unfold fT fN sqrtM
  split
  · apply ext' <;> simp [mul] <;> omega
  · apply ext' <;> simp [mul]

theorem field_discBasis (m : Int) : discBasis (fT m) (fN m) = disc m := by
  rw [discBasis_eq]; unfold fT fN disc; split <;> simp <;> omega

/-- Coordinates of `a + bω ∈ O_m` written as `(x + y√m)/2`. -/
def halfCoords (m : Int) (q : QR) : Int × Int :=
  if m % 4 = 1 then (2 * q.a + q.b, q.b) else (2 * q.a, 2 * q.b)

/-- The pair model multiplies like `ℚ(√m)`:
`((x₁ + y₁√m)/2)((x₂ + y₂√m)/2) = ((x₁x₂ + m y₁y₂) + (x₁y₂ + x₂y₁)√m)/4`. -/
theorem halfCoords_mul (m : Int) (q r : QR) :
    2 * (halfCoords m (mul (fT m) (fN m) q r)).1
        = (halfCoords m q).1 * (halfCoords m r).1 + m * ((halfCoords m q).2 * (halfCoords m r).2) ∧
    2 * (halfCoords m (mul (fT m) (fN m) q r)).2
        = (halfCoords m q).1 * (halfCoords m r).2 + (halfCoords m q).2 * (halfCoords m r).1 := by
  unfold halfCoords fT fN
  split
  · rename_i h
    obtain ⟨k, hk⟩ : ∃ k, m = 1 - 4 * k := ⟨(1 - m) / 4, by omega⟩
    have hn : (1 - m) / 4 = k := by omega
    rw [hn]; subst hk
    simp only [mul]
    constructor <;>
    poly_omega
  · simp only [mul]
    constructor <;>
    poly_omega

theorem sq_form (y : Int) : ∃ c, y * y = 4 * c + y % 2 := by
  rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with h | h
  · obtain ⟨p, hp⟩ : ∃ p, y = 2 * p := ⟨y / 2, by omega⟩
    subst hp
    refine ⟨p * p, ?_⟩
    poly_omega
  · obtain ⟨p, hp⟩ : ∃ p, y = 2 * p + 1 := ⟨y / 2, by omega⟩
    subst hp
    refine ⟨p * p + p, ?_⟩
    poly_omega

/-- **Ring of integers.**  For `m ≢ 0 mod 4` (true for squarefree `m`), an element
`(x + y√m)/2` (`x, y ∈ ℤ`; its trace `x` is an integer) has integral norm `(x² − my²)/4`
iff it lies in `O_m`. -/
theorem integral_iff {m : Int} (hm : m % 4 ≠ 0) (x y : Int) :
    (∃ q, halfCoords m q = (x, y)) ↔ (4 : Int) ∣ x * x - m * (y * y) := by
  constructor
  · rintro ⟨⟨a, b⟩, hq⟩
    unfold halfCoords at hq
    split at hq
    · simp only [Prod.mk.injEq] at hq
      obtain ⟨hx, hy⟩ := hq
      subst hx hy
      obtain ⟨k, hk⟩ : ∃ k, m = 1 - 4 * k := ⟨(1 - m) / 4, by omega⟩
      subst hk
      refine ⟨a * a + a * b + k * (b * b), ?_⟩
      poly_omega
    · simp only [Prod.mk.injEq] at hq
      obtain ⟨hx, hy⟩ := hq
      subst hx hy
      refine ⟨a * a - m * (b * b), ?_⟩
      poly_omega
  · intro hdvd
    obtain ⟨c, hc⟩ := sq_form x
    obtain ⟨e, he⟩ := sq_form y
    rw [hc, he, Int.mul_add] at hdvd
    have h4 : (4 : Int) ∣ 4 * c + x % 2 - (m * (4 * e) + m * (y % 2)) := hdvd
    have hme : m * (4 * e) = 4 * (m * e) := by poly_omega
    rw [hme] at h4
    generalize m * e = M at h4
    rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy | hy <;> rw [hy] at h4 <;>
      simp only [Int.mul_zero, Int.mul_one, Int.add_zero] at h4
    · -- `y` even: then `x` even
      have hx : x % 2 = 0 := by omega
      unfold halfCoords
      split
      · exact ⟨⟨(x - y) / 2, y⟩, Prod.ext (by dsimp only <;> omega) (by dsimp only <;> omega)⟩
      · exact ⟨⟨x / 2, y / 2⟩, Prod.ext (by dsimp only <;> omega) (by dsimp only <;> omega)⟩
    · -- `y` odd: forces `m ≡ 1 mod 4` and `x` odd
      have hm1 : m % 4 = 1 := by omega
      have hx : x % 2 = 1 := by omega
      unfold halfCoords
      simp only [if_pos hm1]
      exact ⟨⟨(x - y) / 2, y⟩, Prod.ext (by dsimp only <;> omega) (by dsimp only <;> omega)⟩

/-- The order of discriminant `D ≡ 0, 1 mod 4`: `ℤ[ω]`, `ω = (t + √D)/2`, `t = D mod 2`,
`n = (t − D)/4` (so `ω² = tω − n`). -/
def tD (D : Int) : Int := D % 2
def nD (D : Int) : Int := (D % 2 - D) / 4

/-- A negative discriminant of a quadratic order. -/
def ValidDisc (D : Int) : Prop := D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1)

theorem discBasis_tD {D : Int} (h : D % 4 = 0 ∨ D % 4 = 1) : discBasis (tD D) (nD D) = D := by
  rw [discBasis_eq]; unfold tD nD
  rcases (by omega : D % 2 = 0 ∨ D % 2 = 1) with h2 | h2 <;> rw [h2] <;> simp <;> omega

/-- `O_m` *is* the order of discriminant `disc m`. -/
theorem fT_eq (m : Int) : fT m = tD (disc m) := by
  unfold fT tD disc; split <;> omega

theorem fN_eq (m : Int) : fN m = nD (disc m) := by
  unfold fN nD disc; split <;> omega

theorem validDisc_disc {m : Int} (h : m < 0) : ValidDisc (disc m) :=
  ⟨disc_neg h, disc_mod_four m⟩

/-! ## 4. Units -/

/-- `x` is a unit of `ℤ[ω]`. -/
def IsUnitQ (t n : Int) (x : QR) : Prop := ∃ y, mul t n x y = one

theorem isUnit_mul {t n : Int} {x y : QR} (hx : IsUnitQ t n x) (hy : IsUnitQ t n y) :
    IsUnitQ t n (mul t n x y) := by
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  refine ⟨mul t n x' y', ?_⟩
  rw [mul_assoc, mul_left_comm t n y x' y', hy', mul_one, hx']

theorem isUnit_one (t n : Int) : IsUnitQ t n one := ⟨one, one_mul t n one⟩

/-- In a positive definite quadratic ring, units are exactly the elements of norm `1`. -/
theorem isUnit_iff_norm {t n : Int} (hdef : t * t < 4 * n) (x : QR) :
    IsUnitQ t n x ↔ norm t n x = 1 := by
  have hnn : ∀ z : QR, 0 ≤ norm t n z := by
    intro z
    have h4 := four_norm t n z
    have h1 := mul_self_nonneg' (trace t z)
    have h2 : 0 ≤ (4 * n - t * t) * (z.b * z.b) :=
      Int.mul_nonneg (by omega) (mul_self_nonneg' z.b)
    omega
  constructor
  · rintro ⟨y, hy⟩
    have := norm_mul t n x y
    rw [hy] at this
    exact Int.eq_one_of_mul_eq_one_right (hnn x) (by simpa [norm, one] using this.symm)
  · intro h
    exact ⟨conj t x, by rw [mul_conj, h]; rfl⟩

theorem tD_cases (D : Int) : tD D = 0 ∨ tD D = 1 := by unfold tD; omega

theorem tD_def {D : Int} (h : ValidDisc D) : tD D * tD D < 4 * nD D := by
  have := discBasis_tD h.2
  rw [discBasis_eq] at this
  have := h.1
  omega

/-- Units of an imaginary quadratic order have coordinates in `{−1, 0, 1}`. -/
theorem unit_bounds {D : Int} (hD : ValidDisc D) {x : QR} (hx : norm (tD D) (nD D) x = 1) :
    (-1 ≤ x.a ∧ x.a ≤ 1) ∧ (-1 ≤ x.b ∧ x.b ≤ 1) := by
  have hdisc := discBasis_tD hD.2
  have hD1 := hD.1
  have hD2 := hD.2
  rw [discBasis_eq] at hdisc
  have h4 := four_norm (tD D) (nD D) x
  rw [hx] at h4
  have hK : 4 * nD D - tD D * tD D = -D := by omega
  rw [hK] at h4
  have hT := mul_self_nonneg' (trace (tD D) x)
  have hB := mul_self_nonneg' x.b
  have hb : x.b * x.b < (1 + 1) * (1 + 1) := by
    apply Int.not_le.mp; intro hge
    have : 3 * 4 ≤ (-D) * (x.b * x.b) := Int.mul_le_mul (by omega) hge (by omega) (by omega)
    omega
  have hb' : x.b * x.b < 2 := by
    apply Int.not_le.mp; intro hge
    have : 3 * 2 ≤ (-D) * (x.b * x.b) := Int.mul_le_mul (by omega) hge (by omega) (by omega)
    omega
  have hb1 := abs_le_of_sq_lt 1 x.b (by omega) (by omega)
  have hT2 := abs_le_of_sq_lt 2 (trace (tD D) x) (by omega) (by
    have : 0 ≤ (-D) * (x.b * x.b) := Int.mul_nonneg (by omega) hB
    omega)
  refine ⟨?_, hb1⟩
  unfold trace at hT2
  rcases tD_cases D with ht | ht <;> rw [ht] at hT2 <;> simp at hT2 <;> omega

/-- The number of units `w(D)`. -/
def w (D : Int) : Nat := if D = -4 then 4 else if D = -3 then 6 else 2

/-- The units, listed as successive powers of a generator. -/
def unitList (D : Int) : List QR :=
  if D = -4 then [⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]
  else if D = -3 then [⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨1, -1⟩]
  else [⟨1, 0⟩, ⟨-1, 0⟩]

/-- The generator: `i`, `ζ₆ = (1+√−3)/2`, or `−1`. -/
def gen (D : Int) : QR := if D = -4 then ⟨0, 1⟩ else if D = -3 then ⟨0, 1⟩ else ⟨-1, 0⟩

theorem unitList_length (D : Int) : (unitList D).length = w D := by
  unfold unitList w; split <;> (try split) <;> rfl

theorem unitList_nodup (D : Int) : (unitList D).Nodup := by
  unfold unitList; split <;> (try split) <;> decide

theorem valid_cases {D : Int} (hD : ValidDisc D) : D = -4 ∨ D = -3 ∨ D < -4 := by
  obtain ⟨h1, h2⟩ := hD; omega

/-- **Units of an imaginary quadratic order of discriminant `D`.** -/
theorem units_classification {D : Int} (hD : ValidDisc D) (x : QR) :
    IsUnitQ (tD D) (nD D) x ↔ x ∈ unitList D := by
  rw [isUnit_iff_norm (tD_def hD)]
  constructor
  · intro hx
    obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩ := unit_bounds hD hx
    have hdisc := discBasis_tD hD.2
    rw [discBasis_eq] at hdisc
    have hc := valid_cases hD
    obtain ⟨a, b⟩ := x
    simp only at ha1 ha2 hb1 hb2
    unfold norm at hx; simp only at hx
    have ht := tD_cases D
    generalize tD D = t at hx hdisc ht
    generalize nD D = n at hx hdisc
    rcases ht with rfl | rfl <;>
    rcases (by omega : a = -1 ∨ a = 0 ∨ a = 1) with rfl | rfl | rfl <;>
    rcases (by omega : b = -1 ∨ b = 0 ∨ b = 1) with rfl | rfl | rfl <;>
    (try simp at hx hdisc) <;> unfold unitList <;> split <;> (try split) <;> (try simp) <;> omega
  · intro hx
    unfold unitList at hx
    split at hx
    · subst_vars; simp at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide
    · split at hx
      · subst_vars; simp at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · simp at hx
        rcases hx with rfl | rfl <;> simp [norm]

/-- The unit group is cyclic of order `w D`: the list of units is `1, g, g², …, g^(w−1)`
(pairwise distinct by `unitList_nodup`) and `g^(w D) = 1`. -/
theorem unitList_eq_pows {D : Int} (hD : ValidDisc D) :
    (List.range (w D)).map (pow (tD D) (nD D) (gen D)) = unitList D ∧
      pow (tD D) (nD D) (gen D) (w D) = one := by
  rcases valid_cases hD with rfl | rfl | h
  · decide
  · decide
  · have h4 : D ≠ -4 := by omega
    have h3 : D ≠ -3 := by omega
    simp only [w, unitList, gen, if_neg h4, if_neg h3]
    constructor
    · simp [List.range, List.range.loop, pow, mul, one]
    · apply ext' <;> simp [pow, mul, one]

/-- The unit group `O^×` of `ℤ[ω]`. -/
def UnitGrp (t n : Int) : Type := {x : QR // IsUnitQ t n x}

instance (t n : Int) : Mul (UnitGrp t n) :=
  ⟨fun x y => ⟨mul t n x.1 y.1, isUnit_mul x.2 y.2⟩⟩

/-- Isomorphisms of multiplicative structures (group isomorphisms for groups). -/
structure MulIso (G H : Type) [Mul G] [Mul H] where
  toFun : G → H
  invFun : H → G
  left_inv : ∀ g, invFun (toFun g) = g
  right_inv : ∀ h, toFun (invFun h) = h
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b

def MulIso.refl (G : Type) [Mul G] : MulIso G G :=
  ⟨id, id, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

/-- The unit group of the ring of integers of `ℚ(√m)`. -/
abbrev FieldUnits (m : Int) : Type := UnitGrp (fT m) (fN m)

/-- The unit group of the imaginary quadratic order of discriminant `D`. -/
abbrev OrderUnits (D : Int) : Type := UnitGrp (tD D) (nD D)

/-- For `D < −4` the units are exactly `±1`. -/
theorem units_pm_one {D : Int} (hD : ValidDisc D) (h : D < -4) (x : QR) :
    IsUnitQ (tD D) (nD D) x ↔ x = ⟨1, 0⟩ ∨ x = ⟨-1, 0⟩ := by
  rw [units_classification hD]
  have h4 : D ≠ -4 := by omega
  have h3 : D ≠ -3 := by omega
  simp [unitList, if_neg h4, if_neg h3]

theorem mul_pm_one {t₁ n₁ t₂ n₂ : Int} {x y : QR} (hx : x = ⟨1, 0⟩ ∨ x = ⟨-1, 0⟩)
    (hy : y = ⟨1, 0⟩ ∨ y = ⟨-1, 0⟩) : mul t₁ n₁ x y = mul t₂ n₂ x y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> apply ext' <;> simp [mul]

/-- Two unit groups that are both `{±1}` are isomorphic (the identity on `±1`). -/
def pmIso {t₁ n₁ t₂ n₂ : Int}
    (h₁ : ∀ x, IsUnitQ t₁ n₁ x ↔ x = ⟨1, 0⟩ ∨ x = ⟨-1, 0⟩)
    (h₂ : ∀ x, IsUnitQ t₂ n₂ x ↔ x = ⟨1, 0⟩ ∨ x = ⟨-1, 0⟩) :
    MulIso (UnitGrp t₁ n₁) (UnitGrp t₂ n₂) where
  toFun x := ⟨x.1, (h₂ x.1).2 ((h₁ x.1).1 x.2)⟩
  invFun y := ⟨y.1, (h₁ y.1).2 ((h₂ y.1).1 y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul a b := Subtype.ext (mul_pm_one ((h₁ a.1).1 a.2) ((h₁ b.1).1 b.2))

/-- **The unit group of an imaginary quadratic order depends only on `w(D)`**, a function of
the discriminant (this does not use injectivity of `disc`). -/
theorem orderUnits_iso_of_w_eq {D₁ D₂ : Int} (h₁ : ValidDisc D₁) (h₂ : ValidDisc D₂)
    (hw : w D₁ = w D₂) : Nonempty (MulIso (OrderUnits D₁) (OrderUnits D₂)) := by
  rcases valid_cases h₁ with rfl | rfl | h₁' <;> rcases valid_cases h₂ with rfl | rfl | h₂'
  · exact ⟨MulIso.refl _⟩
  · exact absurd hw (by decide)
  · have : D₂ ≠ -4 := by omega
    have : D₂ ≠ -3 := by omega
    simp [w, *] at hw
  · exact absurd hw (by decide)
  · exact ⟨MulIso.refl _⟩
  · have : D₂ ≠ -4 := by omega
    have : D₂ ≠ -3 := by omega
    simp [w, *] at hw
  · have : D₁ ≠ -4 := by omega
    have : D₁ ≠ -3 := by omega
    simp [w, *] at hw
  · have : D₁ ≠ -4 := by omega
    have : D₁ ≠ -3 := by omega
    simp [w, *] at hw
  · exact ⟨pmIso (units_pm_one h₁ h₁') (units_pm_one h₂ h₂')⟩

/-- Units of `O_m`, for every imaginary quadratic field: they are listed by `unitList (disc m)`. -/
theorem field_units_classification {m : Int} (hm : IsImagQuadParam m) (x : QR) :
    IsUnitQ (fT m) (fN m) x ↔ x ∈ unitList (disc m) := by
  rw [fT_eq, fN_eq]; exact units_classification (validDisc_disc hm.1) x

/-- `O_m^× = {±1}` unless `m = −1` or `m = −3`. -/
theorem field_units_pm_one {m : Int} (hm : IsImagQuadParam m) (h1 : m ≠ -1) (h3 : m ≠ -3)
    (x : QR) : IsUnitQ (fT m) (fN m) x ↔ x = ⟨1, 0⟩ ∨ x = ⟨-1, 0⟩ := by
  have h0 := hm.2.emod_four_ne_zero
  have hneg := hm.1
  rw [fT_eq, fN_eq]
  exact units_pm_one (validDisc_disc hm.1) (by unfold disc; split <;> omega) x

/-- `O_{-1}^× = {±1, ±i}` (`μ₄`). -/
theorem field_units_neg1 (x : QR) :
    IsUnitQ (fT (-1)) (fN (-1)) x ↔ x ∈ [⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩] :=
  field_units_classification param_neg1 x

/-- `O_{-3}^× = μ₆`, with `ω = (1+√−3)/2`. -/
theorem field_units_neg3 (x : QR) :
    IsUnitQ (fT (-3)) (fN (-3)) x ↔
      x ∈ [⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨1, -1⟩] :=
  field_units_classification param_neg3 x

/-- The number of units `w(disc m)`, a function of the discriminant. -/
theorem field_units_card {m : Int} (hm : IsImagQuadParam m) :
    (∀ x, IsUnitQ (fT m) (fN m) x ↔ x ∈ unitList (disc m)) ∧
      (unitList (disc m)).Nodup ∧ (unitList (disc m)).length = w (disc m) :=
  ⟨field_units_classification hm, unitList_nodup _, unitList_length _⟩

/-- Same discriminant ⇒ isomorphic unit groups, via `w` alone. -/
theorem fieldUnits_iso_of_disc_eq {m₁ m₂ : Int} (h₁ : IsImagQuadParam m₁)
    (h₂ : IsImagQuadParam m₂) (hd : disc m₁ = disc m₂) :
    Nonempty (MulIso (FieldUnits m₁) (FieldUnits m₂)) := by
  have := orderUnits_iso_of_w_eq (validDisc_disc h₁.1) (validDisc_disc h₂.1) (by rw [hd])
  simp only [FieldUnits, OrderUnits] at this ⊢
  rw [fT_eq, fN_eq, fT_eq m₂, fN_eq m₂]
  exact this

/-! ## 5. Non-vacuity: different discriminants can have non-isomorphic unit groups -/

def u1 : FieldUnits (-1) := ⟨⟨1, 0⟩, (field_units_neg1 _).2 (by decide)⟩
def ui : FieldUnits (-1) := ⟨⟨0, 1⟩, (field_units_neg1 _).2 (by decide)⟩
def um1 : FieldUnits (-1) := ⟨⟨-1, 0⟩, (field_units_neg1 _).2 (by decide)⟩

/-- `O_{-1}^× ≇ O_{-2}^×` (4 versus 2 elements). -/
theorem fieldUnits_not_iso : ¬ Nonempty (MulIso (FieldUnits (-1)) (FieldUnits (-2))) := by
  rintro ⟨f⟩
  have hpm : ∀ y : FieldUnits (-2), y.1 = ⟨1, 0⟩ ∨ y.1 = ⟨-1, 0⟩ := fun y =>
    (field_units_pm_one param_neg2 (by decide) (by decide) y.1).1 y.2
  have inj : ∀ a b : FieldUnits (-1), (f.toFun a).1 = (f.toFun b).1 → a.1 = b.1 := by
    intro a b h
    have := congrArg f.invFun (Subtype.ext h)
    rw [f.left_inv, f.left_inv] at this
    rw [this]
  rcases hpm (f.toFun u1) with h1 | h1 <;> rcases hpm (f.toFun ui) with h2 | h2 <;>
    rcases hpm (f.toFun um1) with h3 | h3
  all_goals first
    | exact absurd (inj u1 ui (h1.trans h2.symm)) (by decide)
    | exact absurd (inj u1 um1 (h1.trans h3.symm)) (by decide)
    | exact absurd (inj ui um1 (h2.trans h3.symm)) (by decide)

/-! ## 6. The conjecture -/

/-- The conjecture's existential clause.  `C3 m₁ m₂` stands for "the 3-parts of the class groups
of `ℚ(√m₁)` and `ℚ(√m₂)` are isomorphic" and is left completely arbitrary. -/
def Claim (C3 : Int → Int → Prop) : Prop :=
  ∃ m₁ m₂ : Int, IsImagQuadParam m₁ ∧ IsImagQuadParam m₂ ∧ disc m₁ = disc m₂ ∧ C3 m₁ m₂ ∧
    ¬ Nonempty (MulIso (FieldUnits m₁) (FieldUnits m₂))

/-- **Conjecture 00000004310 is false**, whatever the class-group condition is. -/
theorem conjecture_00000004310_false (C3 : Int → Int → Prop) : ¬ Claim C3 := by
  rintro ⟨m₁, m₂, -, -, hd, -, hn⟩
  have := disc_injective hd
  subst this
  exact hn ⟨MulIso.refl _⟩

/-- Second proof, through `w(D)` only (no injectivity of `disc`). -/
theorem conjecture_00000004310_false' (C3 : Int → Int → Prop) : ¬ Claim C3 := by
  rintro ⟨m₁, m₂, h₁, h₂, hd, -, hn⟩
  exact hn (fieldUnits_iso_of_disc_eq h₁ h₂ hd)

/-- A discriminant witnessing the claim. -/
def Witness (C3 : Int → Int → Prop) (D : Int) : Prop :=
  ∃ m₁ m₂ : Int, IsImagQuadParam m₁ ∧ IsImagQuadParam m₂ ∧ disc m₁ = D ∧ disc m₂ = D ∧
    C3 m₁ m₂ ∧ ¬ Nonempty (MulIso (FieldUnits m₁) (FieldUnits m₂))

theorem no_witness_discriminant (C3 : Int → Int → Prop) (D : Int) : ¬ Witness C3 D := by
  rintro ⟨m₁, m₂, h₁, h₂, hd₁, hd₂, hc, hn⟩
  exact conjecture_00000004310_false C3 ⟨m₁, m₂, h₁, h₂, hd₁.trans hd₂.symm, hc, hn⟩

/-- "The smallest such discriminant is a seven-digit value" is false as well. -/
theorem smallest_seven_digit_false (C3 : Int → Int → Prop) :
    ¬ ∃ D : Int, 1000000 ≤ D.natAbs ∧ D.natAbs < 10000000 ∧ Witness C3 D ∧
      ∀ D', Witness C3 D' → D.natAbs ≤ D'.natAbs := by
  rintro ⟨D, -, -, hD, -⟩
  exact no_witness_discriminant C3 D hD

/-- The reading with imaginary quadratic *orders* (or forms) of the same discriminant. -/
def OrderClaim (C3 : Int → Int → Prop) : Prop :=
  ∃ D₁ D₂ : Int, ValidDisc D₁ ∧ ValidDisc D₂ ∧ D₁ = D₂ ∧ C3 D₁ D₂ ∧
    ¬ Nonempty (MulIso (OrderUnits D₁) (OrderUnits D₂))

theorem order_claim_false (C3 : Int → Int → Prop) : ¬ OrderClaim C3 := by
  rintro ⟨D₁, D₂, h₁, h₂, hd, -, hn⟩
  exact hn (orderUnits_iso_of_w_eq h₁ h₂ (by rw [hd]))

/-- Non-vacuity of the hypotheses: equal discriminants occur (`m₁ = m₂`), and the
class-group condition holds there for any reflexive reading of "isomorphic". -/
theorem hypotheses_satisfiable :
    IsImagQuadParam (-23) ∧ disc (-23) = disc (-23) ∧ disc (-23) = -23 ∧ disc (-5) = -20 :=
  ⟨param_neg23, rfl, by decide, by decide⟩

/-- If the words "of the same discriminant" are dropped, witnesses exist, but with one-digit
discriminants (`−4` and `−8`; both class numbers are `1`, see the report), so the clause
"the smallest discriminant is a seven-digit value" still fails. -/
theorem weakened_reading_small_witness :
    IsImagQuadParam (-1) ∧ IsImagQuadParam (-2) ∧ disc (-1) = -4 ∧ disc (-2) = -8 ∧
      ¬ Nonempty (MulIso (FieldUnits (-1)) (FieldUnits (-2))) :=
  ⟨param_neg1, param_neg2, by decide, by decide, fieldUnits_not_iso⟩

end Conj4310

#print axioms Conj4310.disc_injective
#print axioms Conj4310.integral_iff
#print axioms Conj4310.halfCoords_mul
#print axioms Conj4310.units_classification
#print axioms Conj4310.unitList_eq_pows
#print axioms Conj4310.field_units_card
#print axioms Conj4310.orderUnits_iso_of_w_eq
#print axioms Conj4310.fieldUnits_not_iso
#print axioms Conj4310.conjecture_00000004310_false
#print axioms Conj4310.conjecture_00000004310_false'
#print axioms Conj4310.smallest_seven_digit_false
#print axioms Conj4310.order_claim_false
#print axioms Conj4310.weakened_reading_small_witness
