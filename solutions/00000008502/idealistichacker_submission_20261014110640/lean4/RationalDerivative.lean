import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Tactic

namespace Rational8502

noncomputable section
open Polynomial
open scoped RatFunc

variable {C : Type*} [Field C]

abbrev embed : C[X] →+* C⟮X⟯ := algebraMap C[X] C⟮X⟯

def fractionDerivative (p q : C[X]) : C⟮X⟯ :=
  (embed p.derivative * embed q - embed p * embed q.derivative) / (embed q) ^ 2

theorem fractionDerivative_zero_denominator (p : C[X]) :
    fractionDerivative p 0 = fractionDerivative 0 1 := by
  simp [fractionDerivative]

theorem fractionDerivative_scaling {p q a : C[X]} (hq : q ≠ 0) (ha : a ≠ 0) :
    fractionDerivative (a * p) (a * q) = fractionDerivative p q := by
  have ha' : embed a ≠ 0 := RatFunc.algebraMap_ne_zero ha
  have hq' : embed q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  simp only [fractionDerivative, Polynomial.derivative_mul, map_add, map_mul]
  field_simp
  ring

def derivative (x : C⟮X⟯) : C⟮X⟯ :=
  RatFunc.liftOn' x fractionDerivative (fun hq ha => fractionDerivative_scaling hq ha)

theorem derivative_fraction (p q : C[X]) :
    derivative (embed p / embed q) = fractionDerivative p q := by
  exact RatFunc.liftOn'_div p q fractionDerivative fractionDerivative_zero_denominator _

theorem derivative_polynomial (p : C[X]) : derivative (embed p) = embed p.derivative := by
  have h := derivative_fraction p 1
  simpa [fractionDerivative] using h

theorem derivative_zero : derivative (0 : C⟮X⟯) = 0 := by
  simpa using derivative_polynomial (0 : C[X])

theorem derivative_one : derivative (1 : C⟮X⟯) = 0 := by
  simpa using derivative_polynomial (1 : C[X])

theorem derivative_X : derivative (embed (X : C[X])) = 1 := by
  simpa using derivative_polynomial (X : C[X])

theorem derivative_add (x y : C⟮X⟯) : derivative (x + y) = derivative x + derivative y := by
  induction x using RatFunc.induction_on with
  | _ p q hq =>
    induction y using RatFunc.induction_on with
    | _ r s hs =>
      have hq' : embed q ≠ 0 := RatFunc.algebraMap_ne_zero hq
      have hs' : embed s ≠ 0 := RatFunc.algebraMap_ne_zero hs
      have hadd : embed p / embed q + embed r / embed s =
          embed (p * s + r * q) / embed (q * s) := by
        simp only [map_add, map_mul]
        field_simp
      rw [hadd, derivative_fraction, derivative_fraction, derivative_fraction]
      simp only [fractionDerivative, Polynomial.derivative_mul,
        map_add, map_mul]
      field_simp
      ring

theorem derivative_mul (x y : C⟮X⟯) :
    derivative (x * y) = x * derivative y + y * derivative x := by
  induction x using RatFunc.induction_on with
  | _ p q hq =>
    induction y using RatFunc.induction_on with
    | _ r s hs =>
      have hq' : embed q ≠ 0 := RatFunc.algebraMap_ne_zero hq
      have hs' : embed s ≠ 0 := RatFunc.algebraMap_ne_zero hs
      have hmul : (embed p / embed q) * (embed r / embed s) =
          embed (p * r) / embed (q * s) := by
        simp only [map_mul, div_mul_div_comm]
      rw [hmul, derivative_fraction, derivative_fraction, derivative_fraction]
      simp only [fractionDerivative, Polynomial.derivative_mul, map_add, map_mul]
      field_simp
      ring

theorem derivative_constant (c : C) : derivative (algebraMap C C⟮X⟯ c) = 0 := by
  have h := derivative_polynomial (Polynomial.C c)
  simpa [IsScalarTower.algebraMap_apply C C[X] C⟮X⟯] using h

theorem derivative_smul (c : C) (x : C⟮X⟯) : derivative (c • x) = c • derivative x := by
  rw [Algebra.smul_def, derivative_mul, derivative_constant]
  simp [Algebra.smul_def]

def derivation : Derivation C C⟮X⟯ C⟮X⟯ where
  toFun := derivative
  map_add' := derivative_add
  map_smul' := derivative_smul
  map_one_eq_zero' := derivative_one
  leibniz' x y := by simpa [smul_eq_mul] using derivative_mul x y

theorem derivative_zero_iff_constant [CharZero C] (x : C⟮X⟯) :
    derivative x = 0 ↔ exists c : C, algebraMap C C⟮X⟯ c = x := by
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0]⟩
    have hq : embed x.denom ≠ 0 := RatFunc.algebraMap_ne_zero x.denom_ne_zero
    have hquot := hx
    rw [← x.num_div_denom, derivative_fraction, fractionDerivative] at hquot
    have hz : embed x.num.derivative * embed x.denom - embed x.num * embed x.denom.derivative = 0 := by
      exact (div_eq_zero_iff.mp hquot).resolve_right (pow_ne_zero 2 hq)
    have hcross : x.num.derivative * x.denom = x.num * x.denom.derivative := by
      apply RatFunc.algebraMap_injective C
      simpa only [map_mul] using sub_eq_zero.mp hz
    have hdvd : x.num ∣ x.num.derivative * x.denom := by
      rw [hcross]
      exact dvd_mul_right _ _
    have hpzero : x.num.derivative = 0 :=
      Polynomial.dvd_derivative_iff.mp ((x.isCoprime_num_denom).dvd_of_dvd_mul_right hdvd)
    have hqzero : x.denom.derivative = 0 := by
      rw [hpzero, zero_mul] at hcross
      exact (mul_eq_zero.mp hcross.symm).resolve_left (RatFunc.num_ne_zero hx0)
    refine ⟨x.num.coeff 0 / x.denom.coeff 0, ?_⟩
    have hpC := congrArg (embed (C := C)) (Polynomial.eq_C_of_derivative_eq_zero hpzero)
    have hqC := congrArg (embed (C := C)) (Polynomial.eq_C_of_derivative_eq_zero hqzero)
    calc
      algebraMap C C⟮X⟯ (x.num.coeff 0 / x.denom.coeff 0) =
          embed (Polynomial.C (x.num.coeff 0)) / embed (Polynomial.C (x.denom.coeff 0)) := by
        simp
      _ = embed x.num / embed x.denom := congrArg₂ (fun a b : C⟮X⟯ => a / b) hpC.symm hqC.symm
      _ = x := x.num_div_denom
  · rintro ⟨c, rfl⟩
    exact derivative_constant c

def derivativeAddHom : C⟮X⟯ →+ C⟮X⟯ where
  toFun := derivative
  map_zero' := derivative_zero
  map_add' := derivative_add

@[instance_reducible]
def differentialInstance : Differential C⟮X⟯ := by
  letI : Algebra ℤ C⟮X⟯ := Ring.toIntAlgebra C⟮X⟯
  exact ⟨Derivation.mk' derivativeAddHom.toIntLinearMap
    (fun x y => by simpa [smul_eq_mul, derivativeAddHom] using derivative_mul x y)⟩

theorem concrete_D_X :
    @Differential.deriv C⟮X⟯ _ differentialInstance (embed (X : C[X])) = 1 := by
  exact derivative_X

theorem concrete_constants [CharZero C] (x : C⟮X⟯) :
    @Differential.deriv C⟮X⟯ _ differentialInstance x = 0 ↔
      exists c : C, algebraMap C C⟮X⟯ c = x := by
  exact derivative_zero_iff_constant x

end
end Rational8502
