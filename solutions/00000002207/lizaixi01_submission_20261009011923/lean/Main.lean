import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

noncomputable section

namespace TLMC2207

variable (R K : Type*) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [Finite K]

include K in
/-- Finiteness of the domain is derived from its actual fraction-field embedding. -/
theorem finite_domain_of_finite_fraction_field : Finite R :=
  Finite.of_injective (algebraMap R K) (IsFractionRing.injective R K)

include K in
/-- The derived finite domain is a field: every nonzero multiplier is surjective. -/
theorem isField_of_finite_fraction_field : IsField R where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {a} ha := by
    haveI : Finite R := finite_domain_of_finite_fraction_field R K
    exact Finite.surjective_of_injective (fun _ _ h => mul_left_cancel₀ ha h) 1

/-- Two generators may be redundant or repeated, as in the standard convention. -/
def TwoGenerated (I : Ideal R) : Prop :=
  ∃ a b : R, I = Ideal.span ({a, b} : Set R)

include K in
/-- The only actual ideals are the zero ideal and the whole ring. -/
theorem ideal_eq_bot_or_top (I : Ideal R) : I = ⊥ ∨ I = ⊤ := by
  letI : Field R := (isField_of_finite_fraction_field R K).toField
  exact Ideal.eq_bot_or_top I

include K in
/-- Explicit generator pairs work for every actual ideal, including zero. -/
theorem all_ideals_two_generated (I : Ideal R) : TwoGenerated R I := by
  rcases ideal_eq_bot_or_top R K I with h | h
  · exact ⟨0, 0, by simpa [Ideal.span_pair_zero] using h⟩
  · exact ⟨1, 0, by simpa [Ideal.span_pair_zero] using h⟩

include K in
/-- Actual ideals form a finite type, derived from the original finite-K premise. -/
theorem finite_ideals_of_finite_fraction_field : Finite (Ideal R) := by
  letI : Field R := (isField_of_finite_fraction_field R K).toField
  infer_instance

include K in
/-- The actual ideal set has exactly two elements. -/
theorem ideal_card_eq_two : Nat.card (Ideal R) = 2 := by
  letI : Field R := (isField_of_finite_fraction_field R K).toField
  exact (Nat.card_congr (Ideal.equivFinTwo R)).trans (by simp)

include K in
/-- In particular, the ideal-count denominator is strictly positive. -/
theorem ideal_card_positive : 0 < Nat.card (Ideal R) := by
  rw [ideal_card_eq_two R K]
  decide

/-- Count of actual two-generated ideals; there is no generator-pair sampling. -/
def twoGeneratedCount [Finite (Ideal R)] : ℕ := by
  classical
  letI := Fintype.ofFinite (Ideal R)
  exact (Finset.univ.filter (TwoGenerated R)).card

/-- Ordinary finite cardinal proportion, with rational-valued division. -/
def twoGeneratedProportion [Finite (Ideal R)] : ℚ :=
  (twoGeneratedCount R : ℚ) / Nat.card (Ideal R)

include K in
/-- The finite numerator equals the cardinality of the actual ideal set. -/
theorem twoGeneratedCount_eq_ideal_card :
    (letI : Finite (Ideal R) := finite_ideals_of_finite_fraction_field R K
     twoGeneratedCount R) = Nat.card (Ideal R) := by
  classical
  haveI : Finite (Ideal R) := finite_ideals_of_finite_fraction_field R K
  letI := Fintype.ofFinite (Ideal R)
  have hf : Finset.univ.filter (TwoGenerated R) = (Finset.univ : Finset (Ideal R)) :=
    Finset.filter_true_of_mem (fun I _ => all_ideals_two_generated R K I)
  change (Finset.univ.filter (TwoGenerated R)).card = Nat.card (Ideal R)
  rw [hf, Finset.card_univ, Nat.card_eq_fintype_card]

include K in
/-- In this source setting, exactly two actual ideals are two-generated. -/
theorem twoGeneratedCount_eq_two :
    (letI : Finite (Ideal R) := finite_ideals_of_finite_fraction_field R K
     twoGeneratedCount R) = 2 :=
  (twoGeneratedCount_eq_ideal_card R K).trans (ideal_card_eq_two R K)

include K in
/-- The original Bezout-domain assertion, with finiteness derived from its fraction field. -/
theorem original_proportion_one [IsBezout R] :
    (letI : Finite (Ideal R) := finite_ideals_of_finite_fraction_field R K
     twoGeneratedProportion R) = 1 := by
  haveI : Finite (Ideal R) := finite_ideals_of_finite_fraction_field R K
  change (twoGeneratedCount R : ℚ) / Nat.card (Ideal R) = 1
  rw [twoGeneratedCount_eq_ideal_card R K]
  exact div_self (Nat.cast_ne_zero.mpr (ne_of_gt (ideal_card_positive R K)))

/-- Concrete consistency witness for the finite fraction-field hypotheses. -/
theorem zmod_two_isFractionRing : IsFractionRing (ZMod 2) (ZMod 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  infer_instance

/-- A concrete inhabited model of every original hypothesis family. -/
theorem zmod_two_source_hypotheses :
    Finite (ZMod 2) ∧ IsDomain (ZMod 2) ∧ IsBezout (ZMod 2) ∧
      IsFractionRing (ZMod 2) (ZMod 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨inferInstance, inferInstance, inferInstance, zmod_two_isFractionRing⟩

#check finite_domain_of_finite_fraction_field
#check isField_of_finite_fraction_field
#check ideal_eq_bot_or_top
#check all_ideals_two_generated
#check finite_ideals_of_finite_fraction_field
#check ideal_card_eq_two
#check ideal_card_positive
#check twoGeneratedCount_eq_ideal_card
#check twoGeneratedCount_eq_two
#check original_proportion_one

#print axioms finite_domain_of_finite_fraction_field
#print axioms isField_of_finite_fraction_field
#print axioms ideal_eq_bot_or_top
#print axioms all_ideals_two_generated
#print axioms ideal_card_eq_two
#print axioms ideal_card_positive
#print axioms twoGeneratedCount_eq_ideal_card
#print axioms twoGeneratedCount_eq_two
#print axioms original_proportion_one
#print axioms zmod_two_isFractionRing
#print axioms zmod_two_source_hypotheses

end TLMC2207
