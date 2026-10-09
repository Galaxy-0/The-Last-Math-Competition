import HeightRoots
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open Polynomial
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000
namespace TLMC374

def DegreeAtMostTwo (z : ℂ) : Prop :=
  IsAlgebraic ℚ z ∧ (minpoly ℚ z).natDegree ≤ 2

/-- A signed primitive integer minimal polynomial. Its sign is immaterial for all heights below. -/
def primitiveMinpoly (z : ℂ) : ℤ[X] :=
  (IsLocalization.integerNormalization ℤ⁰ (minpoly ℚ z)).primPart

lemma primitiveMinpoly_primitive (z : ℂ) : (primitiveMinpoly z).IsPrimitive :=
  Polynomial.isPrimitive_primPart _

lemma primitiveMinpoly_ne_zero (z : ℂ) : primitiveMinpoly z ≠ 0 :=
  Polynomial.primPart_ne_zero _

lemma primitiveMinpoly_scalar {z : ℂ} (hz : IsAlgebraic ℚ z) :
    ∃ c : ℚ, c ≠ 0 ∧ (primitiveMinpoly z).map (algebraMap ℤ ℚ) =
      c • minpoly ℚ z := by
  let q := minpoly ℚ z
  let p := IsLocalization.integerNormalization ℤ⁰ q
  have hp : p ≠ 0 := by
    exact mt IsFractionRing.integerNormalization_eq_zero_iff.mp (minpoly.ne_zero hz.isIntegral)
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map ℤ⁰ q
  have hb0 : (b : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have hc0 : p.content ≠ 0 := mt Polynomial.content_eq_zero_iff.mp hp
  refine ⟨(b : ℤ) / (p.content : ℚ), div_ne_zero (by exact_mod_cast hb0)
    (by exact_mod_cast hc0), ?_⟩
  have hfactor := congrArg (Polynomial.map (algebraMap ℤ ℚ)) p.eq_C_content_mul_primPart
  change p.map (algebraMap ℤ ℚ) = (b : ℤ) • q at hb
  rw [← Int.cast_smul_eq_zsmul ℚ] at hb
  rw [Polynomial.map_mul, Polynomial.map_C] at hfactor
  ext i
  have hi := congrArg (fun f : ℚ[X] => f.coeff i) (hfactor.symm.trans hb)
  simp only [coeff_C_mul, coeff_smul, coeff_map, smul_eq_mul] at hi
  simp only [coeff_map, coeff_smul]
  change ((p.primPart.coeff i : ℤ) : ℚ) = ((b : ℤ) / (p.content : ℚ)) * q.coeff i
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (show (p.content : ℚ) ≠ 0 by exact_mod_cast hc0)).mpr
  change (p.content : ℚ) * (p.primPart.coeff i : ℚ) = (b : ℤ) * q.coeff i at hi
  nlinarith [hi]

lemma primitiveMinpoly_degree {z : ℂ} (hz : IsAlgebraic ℚ z) :
    (primitiveMinpoly z).natDegree = (minpoly ℚ z).natDegree := by
  obtain ⟨c, hc, he⟩ := primitiveMinpoly_scalar hz
  have := congrArg Polynomial.natDegree he
  rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective ℤ ℚ),
    Polynomial.natDegree_smul _ hc] at this
  exact this

lemma primitiveMinpoly_root {z : ℂ} (hz : IsAlgebraic ℚ z) :
    aeval z (primitiveMinpoly z) = 0 := by
  apply Polynomial.aeval_primPart_eq_zero
  · exact mt IsFractionRing.integerNormalization_eq_zero_iff.mp (minpoly.ne_zero hz.isIntegral)
  · exact IsLocalization.integerNormalization_aeval_eq_zero ℤ⁰ _ (minpoly.aeval ℚ z)

lemma primitiveMinpoly_constant_ne_zero {z : ℂ} (hz : IsAlgebraic ℚ z) (hz0 : z ≠ 0) :
    (primitiveMinpoly z).coeff 0 ≠ 0 := by
  obtain ⟨c, hc, he⟩ := primitiveMinpoly_scalar hz
  have hi := congrArg (fun f : ℚ[X] => f.coeff 0) he
  simp only [coeff_map, coeff_smul] at hi
  intro h
  rw [h, map_zero] at hi
  exact (mul_ne_zero hc (minpoly.coeff_zero_ne_zero hz.isIntegral hz0)) hi.symm

lemma primitiveMinpoly_irreducible {z : ℂ} (hz : IsAlgebraic ℚ z) :
    Irreducible (primitiveMinpoly z) := by
  apply (primitiveMinpoly_primitive z).irreducible_of_irreducible_map_of_injective
    (IsFractionRing.injective ℤ ℚ)
  obtain ⟨c, hc, he⟩ := primitiveMinpoly_scalar hz
  rw [he, Polynomial.smul_eq_C_mul]
  exact (irreducible_isUnit_mul (Polynomial.isUnit_C.mpr hc.isUnit)).mpr
    (minpoly.irreducible hz.isIntegral)

/-- The usual primitive integer minimal-polynomial characterization, permitting either sign. -/
def IsPrimitiveMinimalPolynomial (z : ℂ) (p : ℤ[X]) : Prop :=
  p.IsPrimitive ∧ Irreducible p ∧ aeval z p = 0

lemma primitiveMinpoly_isMinimal {z : ℂ} (hz : IsAlgebraic ℚ z) :
    IsPrimitiveMinimalPolynomial z (primitiveMinpoly z) :=
  ⟨primitiveMinpoly_primitive z, primitiveMinpoly_irreducible hz, primitiveMinpoly_root hz⟩

lemma associated_integer_polynomials_eq_or_neg {p q : ℤ[X]} (h : Associated p q) :
    q = p ∨ q = -p := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨i, hi, he⟩ := Polynomial.isUnit_iff.mp u.isUnit
  rcases Int.isUnit_iff.mp hi with hi | hi
  · left
    simpa [← he, hi] using hu.symm
  · right
    simpa [← he, hi] using hu.symm

lemma primitiveMinimalPolynomial_unique_sign {z : ℂ} (hz : IsAlgebraic ℚ z)
    {p : ℤ[X]} (hp : IsPrimitiveMinimalPolynomial z p) :
    p = primitiveMinpoly z ∨ p = -primitiveMinpoly z := by
  have hma : Associated (minpoly ℚ z) (p.map (algebraMap ℤ ℚ)) := by
    apply ((minpoly.irreducible hz.isIntegral).dvd_irreducible_iff_associated
      (hp.1.irreducible_iff_irreducible_map_fraction_map.mp hp.2.1)).mp
    apply minpoly.dvd
    simpa only [Polynomial.aeval_map_algebraMap] using hp.2.2
  have hmb : Associated (minpoly ℚ z) ((primitiveMinpoly z).map (algebraMap ℤ ℚ)) := by
    apply ((minpoly.irreducible hz.isIntegral).dvd_irreducible_iff_associated
      ((primitiveMinpoly_primitive z).irreducible_iff_irreducible_map_fraction_map.mp
        (primitiveMinpoly_irreducible hz))).mp
    apply minpoly.dvd
    simpa only [Polynomial.aeval_map_algebraMap] using primitiveMinpoly_root hz
  have hassoc := hmb.symm.trans hma
  apply associated_integer_polynomials_eq_or_neg
  apply associated_of_dvd_dvd
  · exact ((primitiveMinpoly_primitive z).dvd_iff_fraction_map_dvd_fraction_map ℚ hp.1).mpr hassoc.dvd
  · exact (hp.1.dvd_iff_fraction_map_dvd_fraction_map ℚ (primitiveMinpoly_primitive z)).mpr hassoc.dvd'

/-- Maximum absolute coefficient of the integer polynomial, with no scaling or logarithm. -/
noncomputable def naivePolynomialHeight (p : ℤ[X]) : ℕ := p.support.sup (fun i => (p.coeff i).natAbs)

def naiveHeight (z : ℂ) : ℝ := naivePolynomialHeight (primitiveMinpoly z)

lemma coeff_natAbs_le_height (p : ℤ[X]) (i : ℕ) :
    (p.coeff i).natAbs ≤ naivePolynomialHeight p := by
  by_cases hi : i ∈ p.support
  · exact Finset.le_sup (f := fun i => (p.coeff i).natAbs) hi
  · simp [Polynomial.not_mem_support_iff.mp hi]

lemma coeff_abs_le_height (p : ℤ[X]) (i : ℕ) :
    |(p.coeff i : ℝ)| ≤ (naivePolynomialHeight p : ℝ) := by
  have h := Nat.cast_le (α := ℝ).mpr (coeff_natAbs_le_height p i)
  simpa only [Int.cast_natAbs, Int.cast_abs] using h

lemma one_le_naivePolynomialHeight {p : ℤ[X]} (hp : p ≠ 0) :
    1 ≤ naivePolynomialHeight p := by
  have hn : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have h := coeff_natAbs_le_height p p.natDegree
  have hn' : 1 ≤ p.leadingCoeff.natAbs := Int.natAbs_pos.mpr hn
  exact hn'.trans h

lemma small_error_numeric {H r : ℝ} (hH : 2 ≤ H) (hr : 0 ≤ r)
    (he : r < H ^ (-(3 : ℝ))) : H * r + H * r ^ 2 < 1 := by
  have hH0 : 0 < H := by linarith
  rw [Real.rpow_neg hH0.le] at he
  rw [show H ^ (3 : ℝ) = H ^ (3 : ℕ) from Real.rpow_natCast H 3] at he
  have hm : r * H ^ 3 < 1 := (lt_div_iff₀ (pow_pos hH0 3)).mp (by simpa only [one_div] using he)
  have hH2 : 2 ≤ H ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hH2 (mul_nonneg hr hH0.le)
  have hrH : 2 * (H * r) < 1 := by nlinarith [hm, hmul]
  have hr1 : r ≤ 1 := by nlinarith
  have hsq : r ^ 2 ≤ r := by nlinarith
  have hsqH := mul_le_mul_of_nonneg_left hsq hH0.le
  linarith

lemma root_constant_bound {p : ℤ[X]} {z : ℂ} (hd : p.natDegree ≤ 2)
    (hr : aeval z p = 0) :
    |(p.coeff 0 : ℝ)| ≤ (naivePolynomialHeight p : ℝ) * ‖z‖ +
      (naivePolynomialHeight p : ℝ) * ‖z‖ ^ 2 := by
  have he : (p.coeff 0 : ℂ) + (p.coeff 1 : ℂ) * z + (p.coeff 2 : ℂ) * z ^ 2 = 0 := by
    rw [Polynomial.aeval_eq_sum_range' (show p.natDegree < 3 by omega) z] at hr
    simpa [Finset.sum_range_succ, zsmul_eq_mul] using hr
  have hc : (p.coeff 0 : ℂ) = -((p.coeff 1 : ℂ) * z + (p.coeff 2 : ℂ) * z ^ 2) := by
    linear_combination he
  calc
    |(p.coeff 0 : ℝ)| = ‖(p.coeff 0 : ℂ)‖ := by simp
    _ = ‖(p.coeff 1 : ℂ) * z + (p.coeff 2 : ℂ) * z ^ 2‖ := by rw [hc, norm_neg]
    _ ≤ ‖(p.coeff 1 : ℂ) * z‖ + ‖(p.coeff 2 : ℂ) * z ^ 2‖ := norm_add_le _ _
    _ = |(p.coeff 1 : ℝ)| * ‖z‖ + |(p.coeff 2 : ℝ)| * ‖z‖ ^ 2 := by simp
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (coeff_abs_le_height p 1) (norm_nonneg z))
      (mul_le_mul_of_nonneg_right (coeff_abs_le_height p 2) (sq_nonneg ‖z‖))

lemma naive_qualifier_height {z : ℂ} (hz : DegreeAtMostTwo z) (hz0 : z ≠ 0)
    (he : ‖z‖ < naiveHeight z ^ (-(3 : ℝ))) :
    naivePolynomialHeight (primitiveMinpoly z) ≤ 1 := by
  by_contra hh
  have hH : 2 ≤ naivePolynomialHeight (primitiveMinpoly z) := by omega
  have hn := root_constant_bound (by simpa [primitiveMinpoly_degree hz.1] using hz.2)
    (primitiveMinpoly_root hz.1)
  have hc0 := primitiveMinpoly_constant_ne_zero hz.1 hz0
  have hc : (1 : ℝ) ≤ |((primitiveMinpoly z).coeff 0 : ℝ)| := by
    have h : (1 : ℕ) ≤ ((primitiveMinpoly z).coeff 0).natAbs := Int.natAbs_pos.mpr hc0
    have hr := Nat.cast_le (α := ℝ).mpr h
    simpa only [Nat.cast_one, Int.cast_natAbs, Int.cast_abs] using hr
  have hb := small_error_numeric (H := naiveHeight z) (by unfold naiveHeight; exact_mod_cast hH) (norm_nonneg z) he
  exact (not_lt_of_ge (hc.trans hn)) hb

/-- The actual complex algebraic approximants; infinitude counts distinct numbers. -/
def approximants (H : ℂ → ℝ) (ξ τ : ℝ) : Set ℂ :=
  {z | DegreeAtMostTwo z ∧ ‖(ξ : ℂ) - z‖ < H z ^ (-τ)}

/-- Complex approximants permitted. -/
def Pcomplex (H : ℂ → ℝ) (τ : ℝ) : Set ℝ :=
  {ξ | (approximants H ξ τ).Infinite}

/-- Only real algebraic approximants permitted. -/
def Preal (H : ℂ → ℝ) (τ : ℝ) : Set ℝ :=
  {ξ | {z : ℝ | DegreeAtMostTwo (z : ℂ) ∧ |ξ - z| < H (z : ℂ) ^ (-τ)}.Infinite}

lemma naive_approximants_zero_finite : (approximants naiveHeight 0 3).Finite := by
  classical
  let U : Set ℤ := Set.Icc (-1) 1
  let B : Set ℂ := ⋃ (f : ℤ[X]) (_ : f.natDegree ≤ 2 ∧ ∀ i, f.coeff i ∈ U),
    ((f.map (algebraMap ℤ ℂ)).roots.toFinset.toSet : Set ℂ)
  have hB : B.Finite := Polynomial.bUnion_roots_finite (algebraMap ℤ ℂ) 2 (Set.finite_Icc (-1) 1)
  apply (hB.insert 0).subset
  intro z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  · apply Set.mem_insert_of_mem 0
    obtain ⟨hd, he⟩ := hz
    have he' : ‖z‖ < naiveHeight z ^ (-(3 : ℝ)) := by simpa using he
    have hheight := naive_qualifier_height hd hz0 he'
    have hpdegree : (primitiveMinpoly z).natDegree ≤ 2 := by
      simpa [primitiveMinpoly_degree hd.1] using hd.2
    have hcoeff : ∀ i, (primitiveMinpoly z).coeff i ∈ U := by
      intro i
      have h := (coeff_natAbs_le_height (primitiveMinpoly z) i).trans hheight
      change -1 ≤ (primitiveMinpoly z).coeff i ∧ (primitiveMinpoly z).coeff i ≤ 1
      omega
    refine Set.mem_iUnion.mpr ⟨primitiveMinpoly z, Set.mem_iUnion.mpr ⟨⟨hpdegree, hcoeff⟩, ?_⟩⟩
    have hpmap : (primitiveMinpoly z).map (algebraMap ℤ ℂ) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective ℤ ℂ)).mpr (primitiveMinpoly_ne_zero z)
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hpmap]
    simpa only [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] using primitiveMinpoly_root hd.1

lemma naivePolynomialHeight_neg (p : ℤ[X]) :
    naivePolynomialHeight (-p) = naivePolynomialHeight p := by
  simp [naivePolynomialHeight]

/-- The standard representative with positive leading coefficient. -/
def positivePrimitiveMinpoly (z : ℂ) : ℤ[X] :=
  if 0 < (primitiveMinpoly z).leadingCoeff then primitiveMinpoly z else -primitiveMinpoly z

lemma positivePrimitiveMinpoly_sign (z : ℂ) :
    positivePrimitiveMinpoly z = primitiveMinpoly z ∨
      positivePrimitiveMinpoly z = -primitiveMinpoly z := by
  unfold positivePrimitiveMinpoly
  split_ifs <;> simp

lemma positivePrimitiveMinpoly_leadingCoeff_pos (z : ℂ) :
    0 < (positivePrimitiveMinpoly z).leadingCoeff := by
  have hn := Polynomial.leadingCoeff_ne_zero.mpr (primitiveMinpoly_ne_zero z)
  unfold positivePrimitiveMinpoly
  split_ifs with h
  · exact h
  · rw [Polynomial.leadingCoeff_neg]
    omega

lemma positivePrimitiveMinpoly_isMinimal {z : ℂ} (hz : IsAlgebraic ℚ z) :
    IsPrimitiveMinimalPolynomial z (positivePrimitiveMinpoly z) := by
  rcases positivePrimitiveMinpoly_sign z with he | he
  · rw [he]
    exact primitiveMinpoly_isMinimal hz
  · rw [he]
    obtain ⟨hp, hi, hr⟩ := primitiveMinpoly_isMinimal hz
    have ha : Associated (primitiveMinpoly z) (-primitiveMinpoly z) := ⟨-1, by simp⟩
    exact ⟨Polynomial.isPrimitive_of_dvd hp ha.dvd', ha.irreducible_iff.mp hi, by simpa using hr⟩

lemma primitiveMinimalPolynomial_unique_positive {z : ℂ} (hz : IsAlgebraic ℚ z)
    {p : ℤ[X]} (hp : IsPrimitiveMinimalPolynomial z p) (hp0 : 0 < p.leadingCoeff) :
    p = positivePrimitiveMinpoly z := by
  rcases primitiveMinimalPolynomial_unique_sign hz hp with he | he <;>
    rcases positivePrimitiveMinpoly_sign z with hf | hf
  · exact he.trans hf.symm
  · have h := positivePrimitiveMinpoly_leadingCoeff_pos z
    rw [hf, Polynomial.leadingCoeff_neg, ← he] at h
    omega
  · have h := positivePrimitiveMinpoly_leadingCoeff_pos z
    rw [hf] at h
    rw [he, Polynomial.leadingCoeff_neg] at hp0
    omega
  · exact he.trans hf.symm

/-- Mahler measure of the primitive integer minimal polynomial. -/
def mahlerHeight (z : ℂ) : ℝ := HeightRoots.mahler (primitiveMinpoly z)

/-- Absolute multiplicative Weil height, in its primitive minimal-polynomial formula. -/
def absoluteWeilHeight (z : ℂ) : ℝ := HeightRoots.weil (primitiveMinpoly z)

lemma primitive_degree_one_or_two {z : ℂ} (hz : DegreeAtMostTwo z) :
    (primitiveMinpoly z).natDegree = 1 ∨ (primitiveMinpoly z).natDegree = 2 := by
  rw [primitiveMinpoly_degree hz.1]
  have hpos := minpoly.natDegree_pos hz.1.isIntegral
  have hd := hz.2
  omega

lemma no_strict_cube_error {H r : ℝ} (hH : 1 ≤ H) (hr : 1 ≤ r * H ^ 2) :
    ¬r < H ^ (-(3 : ℝ)) := by
  intro he
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have he2 : r < H ^ (-(2 : ℝ)) := he.trans_le
    (Real.rpow_le_rpow_of_exponent_le hH (by norm_num))
  rw [Real.rpow_neg hH0.le, Real.rpow_two] at he2
  have hm : r * H ^ 2 < 1 := (lt_div_iff₀ (sq_pos_of_pos hH0)).mp
    (by simpa only [one_div] using he2)
  exact (not_lt_of_ge hr) hm

lemma mahler_approximants_zero_finite : (approximants mahlerHeight 0 3).Finite := by
  apply (Set.finite_singleton (0 : ℂ)).subset
  intro z hz
  by_contra hz0
  have hne : z ≠ 0 := by simpa using hz0
  obtain ⟨hd, he⟩ := hz
  have hM := HeightRoots.mahler_ge_one (primitiveMinpoly_ne_zero z)
  have hroot := HeightRoots.root_mul_mahler_ge_one (primitiveMinpoly_ne_zero z)
    (primitiveMinpoly_constant_ne_zero hd.1 hne) (primitiveMinpoly_root hd.1)
  have hMM : HeightRoots.mahler (primitiveMinpoly z) ≤ HeightRoots.mahler (primitiveMinpoly z) ^ 2 := by
    nlinarith
  have hsq := hroot.trans (mul_le_mul_of_nonneg_left hMM (norm_nonneg z))
  exact no_strict_cube_error hM hsq (by simpa [mahlerHeight] using he)

lemma weil_approximants_zero_finite : (approximants absoluteWeilHeight 0 3).Finite := by
  apply (Set.finite_singleton (0 : ℂ)).subset
  intro z hz
  by_contra hz0
  have hne : z ≠ 0 := by simpa using hz0
  obtain ⟨hd, he⟩ := hz
  have hpdeg := primitive_degree_one_or_two hd
  have hW := HeightRoots.weil_ge_one (primitiveMinpoly_ne_zero z)
  have hsq := HeightRoots.root_mul_weil_sq_ge_one (primitiveMinpoly_ne_zero z)
    (primitiveMinpoly_constant_ne_zero hd.1 hne) (by omega) (by omega) (primitiveMinpoly_root hd.1)
  exact no_strict_cube_error hW hsq (by simpa [absoluteWeilHeight] using he)

lemma real_approximants_finite_of_complex {H : ℂ → ℝ} {ξ τ : ℝ}
    (h : (approximants H ξ τ).Finite) :
    {z : ℝ | DegreeAtMostTwo (z : ℂ) ∧ |ξ - z| < H (z : ℂ) ^ (-τ)}.Finite := by
  have hf := h.preimage (f := Complex.ofReal) Complex.ofReal_injective.injOn
  convert hf using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage, approximants]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma degreeAtMostTwo_real_iff (x : ℝ) :
    DegreeAtMostTwo (x : ℂ) ↔ IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ 2 := by
  have hm : minpoly ℚ (x : ℂ) = minpoly ℚ x :=
    minpoly.algebraMap_eq (A := ℚ) (B := ℝ) Complex.ofReal_injective x
  have ha : IsAlgebraic ℚ (x : ℂ) ↔ IsAlgebraic ℚ x := by
    rw [isAlgebraic_iff_isIntegral, isAlgebraic_iff_isIntegral]
    exact isIntegral_algHom_iff (IsScalarTower.toAlgHom ℚ ℝ ℂ) Complex.ofReal_injective
  simp only [DegreeAtMostTwo, hm, ha]

inductive HeightConvention where
  | naive | mahler | absoluteWeil

def standardHeight : HeightConvention → ℂ → ℝ
  | .naive => naiveHeight
  | .mahler => mahlerHeight
  | .absoluteWeil => absoluteWeilHeight

/-- The exact three polynomial-height conventions used in the statement of our disproof. -/
def polynomialHeight : HeightConvention → ℤ[X] → ℝ
  | .naive, p => naivePolynomialHeight p
  | .mahler, p => HeightRoots.mahler p
  | .absoluteWeil, p => HeightRoots.weil p

lemma polynomialHeight_neg (c : HeightConvention) (p : ℤ[X]) :
    polynomialHeight c (-p) = polynomialHeight c p := by
  cases c
  · exact congrArg (fun n : ℕ => (n : ℝ)) (naivePolynomialHeight_neg p)
  · exact HeightRoots.mahler_neg p
  · exact HeightRoots.weil_neg p

/-- Full bridge to any primitive irreducible integer defining polynomial, including the
unique conventional representative with positive leading coefficient. -/
theorem standardHeight_eq_primitivePolynomialHeight (c : HeightConvention) {z : ℂ}
    (hz : IsAlgebraic ℚ z) {p : ℤ[X]} (hp : IsPrimitiveMinimalPolynomial z p) :
    standardHeight c z = polynomialHeight c p := by
  rcases primitiveMinimalPolynomial_unique_sign hz hp with he | he
  · rw [he]
    cases c <;> rfl
  · rw [he, polynomialHeight_neg]
    cases c <;> rfl

theorem standardHeight_eq_positivePrimitivePolynomialHeight (c : HeightConvention)
    {z : ℂ} (hz : IsAlgebraic ℚ z) :
    standardHeight c z = polynomialHeight c (positivePrimitiveMinpoly z) :=
  standardHeight_eq_primitivePolynomialHeight c hz (positivePrimitiveMinpoly_isMinimal hz)

/-- The normalization exponent is the actual algebraic degree, rather than the upper bound2. -/
theorem absoluteWeilHeight_pow_degree {z : ℂ} (hz : IsAlgebraic ℚ z) :
    absoluteWeilHeight z ^ (minpoly ℚ z).natDegree = mahlerHeight z := by
  rw [← primitiveMinpoly_degree hz]
  exact HeightRoots.weil_pow_degree (primitiveMinpoly_ne_zero z)
    (by rw [primitiveMinpoly_degree hz]; exact Nat.ne_of_gt (minpoly.natDegree_pos hz.isIntegral))

lemma standard_approximants_zero_finite (c : HeightConvention) :
    (approximants (standardHeight c) 0 3).Finite := by
  cases c
  · exact naive_approximants_zero_finite
  · exact mahler_approximants_zero_finite
  · exact weil_approximants_zero_finite

/-- Both unresolved domain readings of the source. -/
inductive ApproximationDomain where
  | real | complex

def P (d : ApproximationDomain) (c : HeightConvention) (τ : ℝ) : Set ℝ :=
  match d with
  | .real => Preal (standardHeight c) τ
  | .complex => Pcomplex (standardHeight c) τ

/-- The universal real target ξ=0 fails at the included endpoint τ=3. -/
theorem zero_not_mem_P_three (d : ApproximationDomain) (c : HeightConvention) :
    (0 : ℝ) ∉ P d c 3 := by
  cases d
  · exact (real_approximants_finite_of_complex (standard_approximants_zero_finite c)).not_infinite
  · exact (standard_approximants_zero_finite c).not_infinite

/-- Direct negation of the source's entire τ≤3/full-real-line conjunct. -/
theorem source_conjunct_false (d : ApproximationDomain) (c : HeightConvention) :
    ¬(∀ τ : ℝ, τ ≤ 3 → P d c τ = Set.univ) := by
  intro h
  have hzero : (0 : ℝ) ∈ P d c 3 := by rw [h 3 le_rfl]; trivial
  exact zero_not_mem_P_three d c hzero

end TLMC374
