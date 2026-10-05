import Conjecture574.Matroid
import Conjecture574.Lattice

noncomputable section
open scoped BigOperators Polynomial
open Polynomial

namespace Conjecture574

/-- The complete subtype of actual flats of the eight-element parallel extension. -/
abbrev ActualFlat := ActualFlats thickened34

instance actualFlatFintype : Fintype ActualFlat :=
  Fintype.ofEquiv Flat thickenedFlatOrderIso.toEquiv

local instance actualFlatDecidableEq : DecidableEq ActualFlat := Classical.decEq _
local instance actualFlatDecidableLE : DecidableRel ((· ≤ ·) : ActualFlat → ActualFlat → Prop) :=
  Classical.decRel _

theorem actualFlat_card : Fintype.card ActualFlat = 12 := by
  rw [← Fintype.card_congr thickenedFlatOrderIso.toEquiv]
  exact flat_card

/-- Natural rank obtained from the actual matroid rank; finiteness is proved below. -/
def actualRank (F : ActualFlat) : ℕ := (thickened34.eRk F.val).toNat

theorem actualRank_eq (F : ActualFlat) :
    actualRank F = flatRank (thickenedFlatOrderIso.symm F) := by
  have h := thickenedFlatOrderIso_eRk (thickenedFlatOrderIso.symm F)
  rw [thickenedFlatOrderIso.apply_symm_apply] at h
  simp [actualRank, h]

theorem actualRank_finite (F : ActualFlat) : thickened34.eRk F.val ≠ ⊤ := by
  have h := thickenedFlatOrderIso_eRk (thickenedFlatOrderIso.symm F)
  rw [thickenedFlatOrderIso.apply_symm_apply] at h
  simp [h]

theorem actualRank_strictMono : StrictMono actualRank := by
  intro a b hab
  rw [actualRank_eq, actualRank_eq]
  exact flatRank_strictMono (thickenedFlatOrderIso.symm.strictMono hab)

def actualBottom : ActualFlat := thickenedFlatOrderIso flatBottom
def actualTop : ActualFlat := thickenedFlatOrderIso flatTop

theorem actualBottom_val : actualBottom.val = ∅ := by
  simp [actualBottom, thickenedFlatOrderIso_val, flatBottom]

theorem actualTop_val : actualTop.val = thickened34.E := by
  simp [actualTop, thickenedFlatOrderIso_val, flatTop]

theorem actualBottom_le_actualTop : actualBottom ≤ actualTop := by
  change actualBottom.val ⊆ actualTop.val
  rw [actualBottom_val]
  exact Set.empty_subset _

/-- The actual-flat Möbius function, with its full recurrence transported below. -/
def actualMobius : ActualFlat → ActualFlat → ℤ :=
  transportPair thickenedFlatOrderIso mobius

theorem actualMobius_left_recurrence (a b : ActualFlat) :
    (∑ c ∈ interval a b, actualMobius a c) = if a = b then 1 else 0 := by
  simp only [actualMobius, transportPair]
  rw [interval_sum_transport thickenedFlatOrderIso a b
    (fun c => mobius (thickenedFlatOrderIso.symm a) c), mobius_left_recurrence]
  simp

theorem actualMobius_right_recurrence (a b : ActualFlat) :
    (∑ c ∈ interval a b, actualMobius c b) = if a = b then 1 else 0 := by
  simp only [actualMobius, transportPair]
  rw [interval_sum_transport thickenedFlatOrderIso a b
    (fun c => mobius c (thickenedFlatOrderIso.symm b)), mobius_right_recurrence]
  simp

/-- Characteristic polynomial from every actual flat in the interval and actual matroid rank. -/
def actualCharacteristic (a b : ActualFlat) : ℤ[X] :=
  ∑ c ∈ interval a b, C (actualMobius a c) * X ^ (actualRank b - actualRank c)

theorem actualCharacteristic_eq (a b : ActualFlat) :
    actualCharacteristic a b =
      characteristic (thickenedFlatOrderIso.symm a) (thickenedFlatOrderIso.symm b) := by
  simp only [actualCharacteristic, actualMobius, transportPair, actualRank_eq]
  exact interval_sum_transport thickenedFlatOrderIso a b
    (fun c => C (mobius (thickenedFlatOrderIso.symm a) c) *
      X ^ (flatRank (thickenedFlatOrderIso.symm b) - flatRank c))

theorem actualCharacteristic_diagonal (a : ActualFlat) : actualCharacteristic a a = 1 := by
  rw [actualCharacteristic_eq, characteristic_diagonal]

theorem actualCharacteristic_bottom_top :
    actualCharacteristic actualBottom actualTop = X^3 - 4*X^2 + 6*X - 3 := by
  rw [actualCharacteristic_eq]
  simpa [actualBottom, actualTop] using characteristic_bottom_top

/-- A certified family on the actual matroid's complete flat lattice. -/
def actualCandidate : ActualFlat → ActualFlat → ℤ[X] :=
  transportPair thickenedFlatOrderIso candidateKL

theorem actualCandidate_isKL : IsKLFamily actualRank actualCharacteristic actualCandidate := by
  have hr : actualRank = fun a => flatRank (thickenedFlatOrderIso.symm a) :=
    funext actualRank_eq
  have hc : actualCharacteristic = transportPair thickenedFlatOrderIso characteristic := by
    funext a b
    exact actualCharacteristic_eq a b
  rw [hr, hc]
  exact candidateKL_isKL.transport thickenedFlatOrderIso

/-- A value is a KL polynomial precisely when it is the bottom/top value of a family
satisfying the standard axioms on all actual flat intervals. -/
def IsActualKLValue (p : ℤ[X]) : Prop :=
  ∃ P : ActualFlat → ActualFlat → ℤ[X],
    IsKLFamily actualRank actualCharacteristic P ∧ P actualBottom actualTop = p

theorem actualKL_existsUnique : ∃! p : ℤ[X], IsActualKLValue p :=
  klValue_existsUnique actualRank_strictMono actualCharacteristic_diagonal
    actualCandidate_isKL actualBottom actualTop actualBottom_le_actualTop

/-- The actual matroid KL polynomial, selected from the proved existence and uniqueness theorem. -/
def klPolynomial : ℤ[X] := Classical.choose actualKL_existsUnique.exists

theorem klPolynomial_spec : IsActualKLValue klPolynomial :=
  Classical.choose_spec actualKL_existsUnique.exists

theorem klPolynomial_eq : klPolynomial = 1 + 2 * X := by
  obtain ⟨P, hP, hp⟩ := klPolynomial_spec
  have h := klFamily_unique actualRank_strictMono actualCharacteristic_diagonal
    hP actualCandidate_isKL actualBottom actualTop actualBottom_le_actualTop
  rw [hp] at h
  rw [h]
  simp [actualCandidate, transportPair, actualBottom, actualTop,
    candidateKL, flatBottom, flatTop, flatRank]

theorem klPolynomial_coeff_zero : klPolynomial.coeff 0 = 1 := by
  simp [klPolynomial_eq]

theorem klPolynomial_coeff_one : klPolynomial.coeff 1 = 2 := by
  norm_num [klPolynomial_eq, coeff_one]

/-- A necessary condition for strictly alternating signs, allowing either starting sign.
It is deliberately required only where both consecutive coefficients are nonzero. -/
def AdjacentSignsAlternate (p : ℤ[X]) : Prop :=
  ∀ i : ℕ, p.coeff i ≠ 0 → p.coeff (i+1) ≠ 0 → p.coeff i * p.coeff (i+1) < 0

/-- The necessary sign-clause instance for the actual thickened U(3,4). -/
def ConjectureSignInstance : Prop := AdjacentSignsAlternate klPolynomial

theorem conjecture_false : ¬ ConjectureSignInstance := by
  intro h
  have hzero : klPolynomial.coeff 0 ≠ 0 := by rw [klPolynomial_coeff_zero]; decide
  have hone : klPolynomial.coeff 1 ≠ 0 := by rw [klPolynomial_coeff_one]; decide
  have hbad := h 0 hzero hone
  rw [klPolynomial_coeff_zero, show 0 + 1 = 1 from rfl, klPolynomial_coeff_one] at hbad
  norm_num at hbad

end Conjecture574
