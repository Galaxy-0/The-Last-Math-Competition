import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Counterexample to the literal raw-scalar reading of conjecture 00000002844.

We formalize a symmetric order-three tensor on a one-dimensional complexified
Euclidean space, its full contraction, the bilinear unit condition, and the
set of scalar E-eigenvalues.  The tensor has its only coefficient equal to 1.
-/
namespace Conjecture2844

abbrev Vec := Fin 1 → ℂ
abbrev Tensor3 := Fin 1 → Fin 1 → Fin 1 → ℂ

def unitTensor : Tensor3 := fun _ _ _ => 1

def IsSymmetric (T : Tensor3) : Prop :=
  ∀ i j k, T i j k = T j i k ∧ T i j k = T i k j

theorem unitTensor_symmetric : IsSymmetric unitTensor := by
  intro i j k
  constructor <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

/-- The tensor contraction `Tᵢⱼₖ xⱼ xₖ` (both repeated indices summed). -/
def contract (T : Tensor3) (x : Vec) (i : Fin 1) : ℂ :=
  ∑ j : Fin 1, ∑ k : Fin 1, T i j k * x j * x k

/-- The complex-bilinear extension of the Euclidean quadratic form. -/
def quadraticNorm (x : Vec) : ℂ := ∑ i : Fin 1, x i * x i

/-- A normalized E-eigenpair, with the scalar eigenvalue retained. -/
def IsEEigenpair (T : Tensor3) (eigenvalue : ℂ) (x : Vec) : Prop :=
  quadraticNorm x = 1 ∧ x ≠ 0 ∧ ∀ i, contract T x i = eigenvalue * x i

/-- The actual set of scalar E-eigenvalues, not sign-pairs or certificates. -/
def EValues (T : Tensor3) : Set ℂ := {eigenvalue | ∃ x, IsEEigenpair T eigenvalue x}

theorem quadraticNorm_eq_coordinate (x : Vec) :
    quadraticNorm x = x 0 * x 0 := by
  simp [quadraticNorm]

theorem contract_unitTensor_eq_square (x : Vec) (i : Fin 1) :
    contract unitTensor x i = x 0 * x 0 := by
  fin_cases i
  simp [contract, unitTensor]

theorem evalue_iff (eigenvalue : ℂ) :
    eigenvalue ∈ EValues unitTensor ↔ eigenvalue = 1 ∨ eigenvalue = -1 := by
  constructor
  · rintro ⟨x, hnorm, hnonzero, heigen⟩
    have hx2 : x 0 * x 0 = 1 := by
      rw [← quadraticNorm_eq_coordinate]
      exact hnorm
    have hcontract : x 0 * x 0 = eigenvalue * x 0 := by
      simpa only [contract_unitTensor_eq_square] using heigen 0
    have hfactor : (x 0 - 1) * (x 0 + 1) = 0 := by
      calc
        (x 0 - 1) * (x 0 + 1) = x 0 * x 0 - 1 := by ring
        _ = 0 := by rw [hx2]; ring
    rcases mul_eq_zero.mp hfactor with hpos | hneg
    · have hx : x 0 = 1 := sub_eq_zero.mp hpos
      rw [hx] at hcontract
      norm_num at hcontract
      exact Or.inl hcontract.symm
    · have hx : x 0 = -1 := by simpa [eq_neg_iff_add_eq_zero] using hneg
      rw [hx] at hcontract
      norm_num at hcontract
      exact Or.inr (neg_eq_iff_eq_neg.mp hcontract.symm)
  · rintro (hplus | hminus)
    · refine ⟨fun _ => 1, ?_, ?_, ?_⟩
      · simp [quadraticNorm]
      · intro h
        have h0 := congrFun h 0
        norm_num at h0
      · intro i
        fin_cases i
        simp [contract, unitTensor, hplus]
    · refine ⟨fun _ => -1, ?_, ?_, ?_⟩
      · simp [quadraticNorm]
      · intro h
        have h0 := congrFun h 0
        norm_num at h0
      · intro i
        fin_cases i
        simp [contract, unitTensor, hminus]

theorem evalues_eq_pair : EValues unitTensor = ({(1 : ℂ), -1} : Set ℂ) := by
  ext eigenvalue
  rw [evalue_iff]
  simp

theorem evalues_card : (EValues unitTensor).ncard = 2 := by
  rw [evalues_eq_pair]
  apply Set.ncard_pair
  norm_num

theorem formula_at_order3_dimension1 :
    ((3 - 1 : ℕ) ^ 1 - 1) / (3 - 2) = 1 := by
  norm_num

/-- The literal number of distinct scalar E-eigenvalues disagrees with N. -/
theorem raw_evalue_count_disagrees_with_formula :
    (EValues unitTensor).ncard ≠ ((3 - 1 : ℕ) ^ 1 - 1) / (3 - 2) := by
  rw [evalues_card, formula_at_order3_dimension1]
  decide

#print axioms evalues_card
#print axioms raw_evalue_count_disagrees_with_formula

end Conjecture2844
