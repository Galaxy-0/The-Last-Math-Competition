import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Conjecture3315
noncomputable section
open MvPolynomial

abbrev Source := MvPolynomial (Fin 4) ℚ
abbrev Target := MvPolynomial (Fin 3) ℚ
abbrev Exponent := Fin 4 →₀ ℕ

/-- Homogenized lattice points: (1,1), (2,1), (1,2), (0,0). -/
def configuration : Fin 4 → Fin 3 → ℕ :=
  ![![1, 1, 1], ![1, 2, 1], ![1, 1, 2], ![1, 0, 0]]

def column (i : Fin 4) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (configuration i)

def toricMap : Source →ₐ[ℚ] Target :=
  MvPolynomial.aeval (fun i => monomial (column i) (1 : ℚ))

def toricIdeal : Ideal Source := RingHom.ker toricMap.toRingHom

def degreeOfExponent (e : Exponent) : ℕ := e 0 + e 1 + e 2 + e 3

theorem degreeOfExponent_eq_sum (e : Exponent) :
    degreeOfExponent e = e.sum (fun _ n => n) := by
  rw [Finsupp.sum_fintype]
  · simp [degreeOfExponent, Fin.sum_univ_succ, add_assoc]
  · intro i
    rfl

def imageExponent (e : Exponent) : Fin 3 →₀ ℕ :=
  e 0 • column 0 + e 1 • column 1 + e 2 • column 2 + e 3 • column 3

theorem toricMap_monomial (e : Exponent) (a : ℚ) :
    toricMap (monomial e a) = monomial (imageExponent e) a := by
  simp only [toricMap, MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_succ, monomial_pow, monomial_mul,
      C_mul_monomial, imageExponent, algebraMap_eq, add_assoc]
  · intro i
    simp

/-- Exact injectivity on all exponent vectors of total degree at most two. -/
theorem low_degree_image_injective (e f : Exponent)
    (he : degreeOfExponent e ≤ 2) (_hf : degreeOfExponent f ≤ 2)
    (h : imageExponent e = imageExponent f) : e = f := by
  have h0 := congrArg (fun v : Fin 3 →₀ ℕ => v 0) h
  have h1 := congrArg (fun v : Fin 3 →₀ ℕ => v 1) h
  have h2 := congrArg (fun v : Fin 3 →₀ ℕ => v 2) h
  simp [imageExponent, column, configuration, nsmul_eq_mul] at h0 h1 h2
  simp only [degreeOfExponent] at he
  ext i
  fin_cases i
  · change e 0 = f 0
    omega
  · change e 1 = f 1
    omega
  · change e 2 = f 2
    omega
  · change e 3 = f 3
    omega

/-- Any binomial whose two monomials have total degree at most two. -/
def LowDegreeBinomial (p : Source) : Prop :=
  ∃ (e f : Exponent) (a b : ℚ), degreeOfExponent e ≤ 2 ∧ degreeOfExponent f ≤ 2 ∧
    p = monomial e a - monomial f b

theorem low_degree_binomial_in_kernel_eq_zero (p : Source)
    (hp : LowDegreeBinomial p) (hk : p ∈ toricIdeal) : p = 0 := by
  rcases hp with ⟨e, f, a, b, he, hf, rfl⟩
  have hmap : toricMap (monomial e a - monomial f b) = 0 := hk
  rw [map_sub, toricMap_monomial, toricMap_monomial, sub_eq_zero] at hmap
  rcases (monomial_eq_monomial_iff _ _ _ _).mp hmap with ⟨hef, hab⟩ | ⟨ha, hb⟩
  · rw [low_degree_image_injective e f he hf hef, hab, sub_self]
  · simp [ha, hb]

def positiveExponent : Exponent := Finsupp.equivFunOnFinite.symm ![0, 1, 1, 1]
def negativeExponent : Exponent := Finsupp.equivFunOnFinite.symm ![3, 0, 0, 0]
def cubic : Source := monomial positiveExponent 1 - monomial negativeExponent 1

theorem cubic_as_expression : cubic = X 1 * X 2 * X 3 - (X 0 : Source) ^ 3 := by
  have hp : positiveExponent = Finsupp.single 1 1 + Finsupp.single 2 1 +
      Finsupp.single 3 1 := by
    ext i
    fin_cases i <;> norm_num [positiveExponent, Finsupp.single_apply] <;> decide
  have hn : negativeExponent = Finsupp.single 0 3 := by
    ext i
    fin_cases i <;> norm_num [negativeExponent, Finsupp.single_apply]
  simp [cubic, hp, hn, X, X_pow_eq_monomial, monomial_mul, monomial_pow]

theorem cubic_in_kernel : cubic ∈ toricIdeal := by
  change toricMap cubic = 0
  rw [cubic, map_sub, toricMap_monomial, toricMap_monomial, sub_eq_zero]
  have he : imageExponent positiveExponent = imageExponent negativeExponent := by
    ext i
    fin_cases i <;> norm_num [imageExponent, positiveExponent, negativeExponent,
      column, configuration, nsmul_eq_mul] <;> rfl
  rw [he]

theorem cubic_nonzero : cubic ≠ 0 := by
  intro h
  have hm : (monomial positiveExponent (1 : ℚ) : Source) = monomial negativeExponent 1 :=
    sub_eq_zero.mp h
  rcases (monomial_eq_monomial_iff _ _ _ _).mp hm with ⟨he, _⟩ | hz
  · have h0 := congrArg (fun e : Exponent => e 0) he
    norm_num [positiveExponent, negativeExponent] at h0
  · norm_num at hz

theorem toric_ideal_nonzero : toricIdeal ≠ ⊥ := by
  intro h
  have hc := cubic_in_kernel
  rw [h, Ideal.mem_bot] at hc
  exact cubic_nonzero hc

def lowDegreeRelations : Set Source := {p | LowDegreeBinomial p ∧ p ∈ toricIdeal}

theorem low_relation_span_is_zero : Ideal.span lowDegreeRelations = ⊥ := by
  apply Ideal.span_eq_bot.mpr
  intro p hp
  exact low_degree_binomial_in_kernel_eq_zero p hp.1 hp.2

/-- No generating set made of degree-at-most-two binomials exists. -/
theorem no_quadratic_binomial_generating_set :
    ¬ ∃ S : Set Source, (∀ p ∈ S, LowDegreeBinomial p) ∧ Ideal.span S = toricIdeal := by
  rintro ⟨S, hS, hspan⟩
  have hzero : Ideal.span S = ⊥ := by
    apply Ideal.span_eq_bot.mpr
    intro p hp
    apply low_degree_binomial_in_kernel_eq_zero p (hS p hp)
    rw [← hspan]
    exact Ideal.subset_span hp
  exact toric_ideal_nonzero (hspan.symm.trans hzero)

/-- Barycentric definition of the closed triangle with vertices (0,0),(2,1),(1,2). -/
def InTriangle (x y : ℤ) : Prop :=
  ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
    (x : ℝ) = 2 * b + c ∧ (y : ℝ) = b + 2 * c

theorem triangle_lattice_points (x y : ℤ) : InTriangle x y ↔
    (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) ∨ (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 2) := by
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, habc, hx, hy⟩
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hy0 : (0 : ℝ) ≤ y := by linarith
    have hsum : (x : ℝ) + y ≤ 3 := by linarith
    have hxy : (x : ℝ) ≤ 2 * y := by linarith
    have hyx : (y : ℝ) ≤ 2 * x := by linarith
    have hx0' : (0 : ℤ) ≤ x := by exact_mod_cast hx0
    have hy0' : (0 : ℤ) ≤ y := by exact_mod_cast hy0
    have hsum' : x + y ≤ 3 := by exact_mod_cast hsum
    have hxy' : x ≤ 2 * y := by exact_mod_cast hxy
    have hyx' : y ≤ 2 * x := by exact_mod_cast hyx
    omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨1, 0, 0, by norm_num⟩
    · exact ⟨1 / 3, 1 / 3, 1 / 3, by norm_num⟩
    · exact ⟨0, 1, 0, by norm_num⟩
    · exact ⟨0, 0, 1, by norm_num⟩

theorem configuration_is_exact_triangle (x y : ℤ) :
    InTriangle x y ↔ ∃ i : Fin 4,
      x = (configuration i 1 : ℤ) ∧ y = (configuration i 2 : ℤ) := by
  rw [triangle_lattice_points]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨3, rfl, rfl⟩
    · exact ⟨0, rfl, rfl⟩
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨2, rfl, rfl⟩
  · rintro ⟨i, rfl, rfl⟩
    fin_cases i <;> norm_num [configuration] <;> decide

#print axioms degreeOfExponent_eq_sum
#print axioms toricMap_monomial
#print axioms low_degree_image_injective
#print axioms low_degree_binomial_in_kernel_eq_zero
#print axioms cubic_as_expression
#print axioms cubic_in_kernel
#print axioms cubic_nonzero
#print axioms low_relation_span_is_zero
#print axioms no_quadratic_binomial_generating_set
#print axioms triangle_lattice_points
#print axioms configuration_is_exact_triangle

end
end Conjecture3315
