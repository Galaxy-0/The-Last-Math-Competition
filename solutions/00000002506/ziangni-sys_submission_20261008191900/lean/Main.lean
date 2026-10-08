import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

open scoped BigOperators
namespace TuckerClosure
variable {d : Type*} [Fintype d] [DecidableEq d] {K : Type*} [CommSemiring K]
variable {I J L : d → Type*} [∀ i, Fintype (I i)] [∀ i, Fintype (J i)] [∀ i, Fintype (L i)]
variable [∀ i, DecidableEq (I i)] [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (L i)]

-- Actual coordinate arrays and rectangular factor matrices, with arbitrary arity.
abbrev Tensor (I : d → Type*) := (∀ i, I i) → K
abbrev Factors (I J : d → Type*) := ∀ i, Matrix (I i) (J i) K
noncomputable def contract (U : Factors (K:=K) I J) (C : Tensor (K:=K) J) : Tensor (K:=K) I :=
  fun x => ∑ y : ∀ i, J i, C y * ∏ i, U i (x i) (y i)
noncomputable def compose (V : Factors (K:=K) L I) (U : Factors (K:=K) I J) : Factors (K:=K) L J :=
  fun i => V i * U i

-- Every subsequent collection of actual mode contractions updates the factors.
theorem contractions_compose (V : Factors (K:=K) L I) (U : Factors (K:=K) I J)
    (C : Tensor (K:=K) J) : contract V (contract U C) = contract (compose V U) C := by
  classical
  funext z
  unfold contract compose
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  simp_rw [Matrix.mul_apply]
  rw [Fintype.prod_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.prod_mul_distrib]
  ring

noncomputable def identities : Factors (K:=K) I I := fun _ => 1

theorem identity_kernel (x y : ∀ i, I i) :
    (∏ i, identities (K:=K) (I:=I) i (x i) (y i)) = if y=x then 1 else 0 := by
  classical
  by_cases h : y=x
  · subst y; simp [identities]
  · rw [if_neg h]
    have he : ∃ i, x i ≠ y i := by
      by_contra he
      push_neg at he
      exact h (funext fun i => (he i).symm)
    obtain ⟨i, hi⟩ := he
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [identities, Matrix.one_apply, hi]

theorem identity_factorization (C : Tensor (K:=K) I) : contract identities C = C := by
  classical
  funext x
  simp [contract, identity_kernel]

-- Tucker representations consist of an actual core and one factor per mode.
def HasTuckerRepresentation (T : Tensor (K:=K) I) (C : Tensor (K:=K) J)
    (U : Factors (K:=K) I J) : Prop := T = contract U C

theorem every_tensor_has_tucker (T : Tensor (K:=K) I) :
    HasTuckerRepresentation T T identities := (identity_factorization T).symm

theorem tucker_closed (T : Tensor (K:=K) I) (C : Tensor (K:=K) J)
    (U : Factors (K:=K) I J) (V : Factors (K:=K) L I)
    (h : HasTuckerRepresentation T C U) :
    HasTuckerRepresentation (contract V T) C (compose V U) := by
  unfold HasTuckerRepresentation at *
  rw [h, contractions_compose]

-- A single mode product is the collection with identities in all other modes.
noncomputable def modeFactors [DecidableEq d] (k : d) (A : Matrix (I k) (I k) K) :
    Factors (K:=K) I I := fun i => if h : i=k then h.symm ▸ A else 1
noncomputable def modeProduct [DecidableEq d] (k : d) (A : Matrix (I k) (I k) K)
    (T : Tensor (K:=K) I) : Tensor (K:=K) I := contract (modeFactors k A) T

@[simp] theorem mode_at [DecidableEq d] (k : d) (A : Matrix (I k) (I k) K) : modeFactors k A k = A := by
  simp [modeFactors]
@[simp] theorem mode_other [DecidableEq d] (k i : d) (h : i ≠ k) (A : Matrix (I k) (I k) K) :
    modeFactors k A i = 1 := by simp [modeFactors, h]

theorem same_mode_compose [DecidableEq d] (k : d) (A B : Matrix (I k) (I k) K)
    (T : Tensor (K:=K) I) : modeProduct k B (modeProduct k A T) = modeProduct k (B*A) T := by
  unfold modeProduct
  rw [contractions_compose]
  apply congrArg (fun U : Factors (K:=K) I I => contract U T)
  funext i
  by_cases h : i=k
  · subst i; simp [compose]
  · simp [compose, mode_other, h]

theorem distinct_modes_commute [DecidableEq d] (k l : d) (hkl : k ≠ l)
    (A : Matrix (I k) (I k) K) (B : Matrix (I l) (I l) K)
    (T : Tensor (K:=K) I) : modeProduct l B (modeProduct k A T) = modeProduct k A (modeProduct l B T) := by
  unfold modeProduct
  rw [contractions_compose, contractions_compose]
  apply congrArg (fun U : Factors (K:=K) I I => contract U T)
  funext i
  by_cases hk : i=k
  · subst i; simp [compose, mode_other, hkl]
  · by_cases hl : i=l
    · subst i; simp [compose, mode_other, Ne.symm hkl]
    · simp [compose, mode_other, hk, hl]

#print axioms contractions_compose
#print axioms identity_kernel
#print axioms identity_factorization
#print axioms every_tensor_has_tucker
#print axioms tucker_closed
#print axioms same_mode_compose
#print axioms distinct_modes_commute
end TuckerClosure
