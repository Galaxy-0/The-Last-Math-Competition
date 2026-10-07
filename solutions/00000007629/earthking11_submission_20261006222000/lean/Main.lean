import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

/-!
Counterexample to rotor uniqueness using the actual Mathlib Clifford algebra
and spin group.  The two scalar rotors `1` and `-1` are distinct spin-group
elements, but both induce the identity on every vector by `r * ι(v) * star r`.
-/

namespace RotorNonuniqueness

abbrev V := Fin 2 → ℝ

def standardQ : QuadraticForm ℝ V :=
  QuadraticMap.proj (R := ℝ) (n := Fin 2) 0 0 +
    QuadraticMap.proj (R := ℝ) (n := Fin 2) 1 1

def e₀ : V := Pi.single 0 1

theorem standardQ_e₀ : standardQ e₀ = 1 := by
  simp [standardQ, e₀]

theorem standardQ_neg_e₀ : standardQ (-e₀) = 1 := by
  simp [standardQ, e₀]

noncomputable section

open CliffordAlgebra

local notation "A" => CliffordAlgebra standardQ

local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

def e₀Unit : Aˣ where
  val := ι standardQ e₀
  inv := ι standardQ e₀
  val_inv := by rw [ι_sq_scalar, standardQ_e₀]; simp
  inv_val := by rw [ι_sq_scalar, standardQ_e₀]; simp

def negE₀Unit : Aˣ where
  val := ι standardQ (-e₀)
  inv := ι standardQ (-e₀)
  val_inv := by rw [ι_sq_scalar, standardQ_neg_e₀]; simp
  inv_val := by rw [ι_sq_scalar, standardQ_neg_e₀]; simp

theorem e₀Unit_mem_generators :
    e₀Unit ∈ ((↑) ⁻¹' Set.range (ι standardQ) : Set Aˣ) := by
  exact ⟨e₀, rfl⟩

theorem negE₀Unit_mem_generators :
    negE₀Unit ∈ ((↑) ⁻¹' Set.range (ι standardQ) : Set Aˣ) := by
  exact ⟨-e₀, rfl⟩

theorem e₀_negE₀Unit_eq_negOne : e₀Unit * negE₀Unit = (-1 : Aˣ) := by
  apply Units.ext
  simp [e₀Unit, negE₀Unit, ι_sq_scalar, standardQ_e₀]

theorem negOne_mem_lipschitz : (-1 : Aˣ) ∈ lipschitzGroup standardQ := by
  rw [← e₀_negE₀Unit_eq_negOne]
  apply (lipschitzGroup standardQ).mul_mem
  · exact Subgroup.subset_closure e₀Unit_mem_generators
  · exact Subgroup.subset_closure negE₀Unit_mem_generators

theorem negOne_mem_pin : (-1 : A) ∈ pinGroup standardQ := by
  rw [pinGroup.mem_iff]
  constructor
  · change ((-1 : Aˣ) : A) ∈ _
    rw [lipschitzGroup.coe_mem_iff_mem]
    simpa using negOne_mem_lipschitz
  · rw [Unitary.mem_iff]
    simp

theorem negOne_mem_even : (-1 : A) ∈ CliffordAlgebra.even standardQ := by
  have hone : (1 : A) ∈ CliffordAlgebra.even standardQ :=
    (CliffordAlgebra.even standardQ).one_mem
  have hneg := (CliffordAlgebra.even standardQ).neg_mem hone
  exact hneg

theorem negOne_mem_spin : (-1 : A) ∈ spinGroup standardQ :=
  spinGroup.mem_iff.mpr ⟨negOne_mem_pin, negOne_mem_even⟩

theorem one_mem_spin : (1 : A) ∈ spinGroup standardQ := by
  rw [spinGroup.mem_iff]
  constructor
  · rw [pinGroup.mem_iff]
    constructor
    · change ((1 : Aˣ) : A) ∈ _
      rw [lipschitzGroup.coe_mem_iff_mem]
      exact (lipschitzGroup standardQ).one_mem
    · rw [Unitary.mem_iff]
      simp
  · exact (CliffordAlgebra.even standardQ).one_mem

def rotorPlus : spinGroup standardQ := ⟨1, one_mem_spin⟩
def rotorMinus : spinGroup standardQ := ⟨-1, negOne_mem_spin⟩

theorem rotorPlus_ne_rotorMinus : rotorPlus ≠ rotorMinus := by
  intro h
  have hv := congrArg (fun r : spinGroup standardQ => (r : A)) h
  change (1 : A) = -1 at hv
  have htwo_ne : (2 : A) ≠ 0 := by
    intro hz
    have hreal : (2 : ℝ) = 0 := by
      apply (FaithfulSMul.algebraMap_injective ℝ A)
      simpa only [map_ofNat, map_zero] using hz
    norm_num at hreal
  have htwo_zero : (2 : A) = 0 := by
    have hsum := congrArg (fun x : A => x + 1) hv
    norm_num at hsum ⊢
    exact hsum
  exact htwo_ne htwo_zero

def realizes (r : spinGroup standardQ) (T : V →ₗ[ℝ] V) : Prop :=
  ∀ v, (r : A) * ι standardQ v * star (r : A) = ι standardQ (T v)

def identityChange : V →ₗ[ℝ] V := LinearMap.id

def standardBasis : Module.Basis (Fin 2) ℝ V := Pi.basisFun ℝ (Fin 2)

theorem standardQ_apply (v : V) :
    standardQ v = v 0 * v 0 + v 1 * v 1 := by
  simp [standardQ, QuadraticMap.proj_apply]

theorem standardQ_eq_sum_squares (v : V) :
    standardQ v = v 0 ^ 2 + v 1 ^ 2 := by
  rw [standardQ_apply]
  simp [pow_two]

theorem standardBasis_unit (i : Fin 2) : standardQ (standardBasis i) = 1 := by
  fin_cases i <;> simp [standardBasis, standardQ_apply]

theorem standardBasis_orthogonal {i j : Fin 2} (hij : i ≠ j) :
    QuadraticMap.polar standardQ (standardBasis i) (standardBasis j) = 0 := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · norm_num [standardBasis, standardQ_apply, QuadraticMap.polar]
  · norm_num [standardBasis, standardQ_apply, QuadraticMap.polar]
  · exact (hij rfl).elim

theorem identityChange_fixes_basis (i : Fin 2) :
    identityChange (standardBasis i) = standardBasis i := rfl

def PreservesQuadraticForm (T : V →ₗ[ℝ] V) : Prop :=
  ∀ v, standardQ (T v) = standardQ v

theorem identityChange_preservesQuadraticForm :
    PreservesQuadraticForm identityChange := by
  intro v
  rfl

theorem rotorPlus_realizes_identity : realizes rotorPlus identityChange := by
  intro v
  simp [rotorPlus, identityChange]

theorem rotorMinus_realizes_identity : realizes rotorMinus identityChange := by
  intro v
  simp [rotorMinus, identityChange]

theorem identityChange_has_det_one : LinearMap.det identityChange = 1 := by
  simp [identityChange]

theorem no_unique_rotor_for_identity :
    ¬ ∃! r : spinGroup standardQ, realizes r identityChange := by
  rintro ⟨r, hr, huniq⟩
  have hp : rotorPlus = r := huniq rotorPlus rotorPlus_realizes_identity
  have hm : rotorMinus = r := huniq rotorMinus rotorMinus_realizes_identity
  exact rotorPlus_ne_rotorMinus (hp.trans hm.symm)

theorem actual_rotor_counterexample :
    rotorPlus ≠ rotorMinus ∧
      realizes rotorPlus identityChange ∧
      realizes rotorMinus identityChange ∧
      PreservesQuadraticForm identityChange ∧
      (∀ v, standardQ v = v 0 ^ 2 + v 1 ^ 2) ∧
      (∀ i, standardQ (standardBasis i) = 1) ∧
      (∀ i j, i ≠ j →
        QuadraticMap.polar standardQ (standardBasis i) (standardBasis j) = 0) ∧
      (∀ i, identityChange (standardBasis i) = standardBasis i) ∧
      LinearMap.det identityChange = 1 ∧
      ¬ ∃! r : spinGroup standardQ, realizes r identityChange := by
  exact ⟨rotorPlus_ne_rotorMinus, rotorPlus_realizes_identity,
    rotorMinus_realizes_identity, identityChange_preservesQuadraticForm,
    standardQ_eq_sum_squares, standardBasis_unit,
    (fun i j hij => standardBasis_orthogonal hij),
    identityChange_fixes_basis, identityChange_has_det_one,
    no_unique_rotor_for_identity⟩

#print axioms negOne_mem_spin
#print axioms rotorPlus_ne_rotorMinus
#print axioms rotorPlus_realizes_identity
#print axioms rotorMinus_realizes_identity
#print axioms actual_rotor_counterexample

end
end RotorNonuniqueness
